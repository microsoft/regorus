use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use regorus::Engine;
use std::collections::HashMap;
use std::hint::black_box;
use std::sync::{Arc, Barrier, Mutex};
use std::thread;
use std::time::Duration;

fn multi_threaded_eval(
    num_threads: usize,
    evals_per_thread: usize,
    use_cloned_engines: bool,
    use_cloned_inputs: bool,
) -> (std::time::Duration, HashMap<String, usize>) {
    // Complex policies with multiple valid inputs for each
    let policies_with_inputs = vec![
        (
            r#"
            package bench
            
            default allow := false
            
            allow if {
                input.user.role == "admin"
                input.action in ["read", "write", "delete"]
                input.resource.classification in ["public", "internal"]
                count(input.user.permissions) > 0
            }
            "#,
            vec![
                r#"{
                    "user": {"role": "admin", "permissions": ["all"]},
                    "action": "read",
                    "resource": {"classification": "public", "id": "doc1"}
                }"#,
                r#"{
                    "user": {"role": "admin", "permissions": ["read", "write"]},
                    "action": "write",
                    "resource": {"classification": "internal", "owner": "alice"}
                }"#,
                r#"{
                    "user": {"role": "admin", "permissions": ["delete", "admin"]},
                    "action": "delete",
                    "resource": {"classification": "public", "type": "document"}
                }"#,
            ],
        ),
        (
            r#"
            package bench
            
            default allow := false
            
            valid_api_paths := ["/api/v1/", "/api/v2/", "/api/v3/"]
            
            allow if {
                input.request.method == "GET"
                some path in valid_api_paths
                startswith(input.request.path, path)
                input.user.authenticated == true
                time.now_ns() - input.user.login_time < 86400000000000  # 24 hours in nanoseconds
            }
            "#,
            vec![
                r#"{
                    "request": {"method": "GET", "path": "/api/v1/users"},
                    "user": {"authenticated": true, "login_time": 1640995200000000000}
                }"#,
                r#"{
                    "request": {"method": "GET", "path": "/api/v2/documents/123"},
                    "user": {"authenticated": true, "login_time": 1640995300000000000}
                }"#,
                r#"{
                    "request": {"method": "GET", "path": "/api/v3/reports"},
                    "user": {"authenticated": true, "login_time": 1640995250000000000}
                }"#,
            ],
        ),
        (
            r#"
            package bench
            
            default allow := false
            
            rbac_roles := {
                "admin": ["read", "write", "delete", "admin"],
                "manager": ["read", "write"],
                "user": ["read"]
            }
            
            user_permissions contains perm if {
                some role in input.user.roles
                perm := rbac_roles[role][_]
            }
            
            allow if {
                input.action in user_permissions
                input.resource.owner == input.user.id
            }
            
            allow if {
                input.action in user_permissions
                input.resource.public == true
                input.action == "read"
            }
            "#,
            vec![
                r#"{
                    "user": {"id": "alice", "roles": ["admin"]},
                    "action": "write",
                    "resource": {"owner": "alice", "id": "doc1"}
                }"#,
                r#"{
                    "user": {"id": "bob", "roles": ["manager"]},
                    "action": "read",
                    "resource": {"public": true, "type": "article"}
                }"#,
                r#"{
                    "user": {"id": "charlie", "roles": ["user"]},
                    "action": "read",
                    "resource": {"public": true, "classification": "open"}
                }"#,
            ],
        ),
        (
            r#"
            package bench
            
            default allow := false
            
            # Time-based access control with complex conditions
            business_hours if {
                hour := time.clock([time.now_ns(), "America/New_York"])[0]
                hour >= 9
                hour < 17
            }
            
            allow if {
                input.user.department in ["engineering", "product"]
                input.action == "deploy"
                business_hours
                count([x | x := input.approvals[_]; x.status == "approved"]) >= 2
            }
            
            allow if {
                input.user.emergency_access == true
                input.action in ["read", "diagnose"]
                input.justification != ""
            }
            "#,
            vec![
                r#"{
                    "user": {"department": "engineering", "emergency_access": false},
                    "action": "deploy",
                    "approvals": [
                        {"status": "approved", "by": "alice"},
                        {"status": "approved", "by": "bob"}
                    ]
                }"#,
                r#"{
                    "user": {"department": "product", "emergency_access": false},
                    "action": "deploy",
                    "approvals": [
                        {"status": "approved", "by": "charlie"},
                        {"status": "approved", "by": "diana"},
                        {"status": "pending", "by": "eve"}
                    ]
                }"#,
                r#"{
                    "user": {"department": "ops", "emergency_access": true},
                    "action": "diagnose",
                    "justification": "Production incident response"
                }"#,
            ],
        ),
        (
            r#"
            package bench
            
            default allow := false
            
            # Complex data filtering and aggregation
            sensitive_fields := ["ssn", "credit_card", "password"]
            
            contains_sensitive_data if {
                some field in sensitive_fields
                object.get(input.data, field, null) != null
            }
            
            user_clearance_level := object.get(input.user.attributes, "clearance", 0)

            required_clearance := 3 if contains_sensitive_data else := 1

            allow if {
                user_clearance_level >= required_clearance
                input.operation in ["read", "export"]
                count(input.data) > 0
                count(input.data) <= 1000  # Limit data size
            }
            
            allow if {
                input.user.role == "data_processor"
                input.operation == "transform"
                not contains_sensitive_data
            }
            "#,
            vec![
                r#"{
                    "user": {"attributes": {"clearance": 3}, "role": "analyst"},
                    "operation": "read",
                    "data": {"name": "John", "ssn": "123-45-6789"}
                }"#,
                r#"{
                    "user": {"attributes": {"clearance": 2}, "role": "viewer"},
                    "operation": "export",
                    "data": {"name": "Jane", "age": 30, "department": "engineering"}
                }"#,
                r#"{
                    "user": {"role": "data_processor"},
                    "operation": "transform",
                    "data": {"name": "Bob", "age": 25, "city": "Seattle"}
                }"#,
            ],
        ),
        (
            r#"
            package bench
            
            default allow := false
            
            # Azure VM deployment policy
            allowed_vm_sizes := [
                "Standard_B1s", "Standard_B2s", "Standard_B4ms",
                "Standard_D2s_v3", "Standard_D4s_v3", "Standard_F2s_v2"
            ]
            
            allowed_regions := ["eastus", "westus2", "northeurope", "southeastasia"]
            
            allow if {
                input.operation == "Microsoft.Compute/virtualMachines/write"
                input.resource.properties.hardwareProfile.vmSize in allowed_vm_sizes
                input.resource.location in allowed_regions
                input.resource.properties.osProfile.adminPassword == null  # Require SSH keys
                count(input.resource.tags) > 0  # Must have tags
                input.resource.tags.environment in ["dev", "test", "prod"]
            }
            "#,
            vec![
                r#"{
                    "operation": "Microsoft.Compute/virtualMachines/write",
                    "resource": {
                        "location": "eastus",
                        "properties": {
                            "hardwareProfile": {"vmSize": "Standard_B2s"},
                            "osProfile": {"adminUsername": "azureuser", "adminPassword": null}
                        },
                        "tags": {"environment": "dev", "project": "webapp"}
                    }
                }"#,
                r#"{
                    "operation": "Microsoft.Compute/virtualMachines/write",
                    "resource": {
                        "location": "westus2",
                        "properties": {
                            "hardwareProfile": {"vmSize": "Standard_D2s_v3"},
                            "osProfile": {"adminUsername": "admin", "adminPassword": null}
                        },
                        "tags": {"environment": "prod", "costCenter": "engineering"}
                    }
                }"#,
                r#"{
                    "operation": "Microsoft.Compute/virtualMachines/write",
                    "resource": {
                        "location": "northeurope",
                        "properties": {
                            "hardwareProfile": {"vmSize": "Standard_F2s_v2"},
                            "osProfile": {"adminUsername": "sysadmin", "adminPassword": null}
                        },
                        "tags": {"environment": "test", "team": "devops"}
                    }
                }"#,
            ],
        ),
        (
            r#"
            package bench
            
            default allow := false
            
            # Azure Storage Account security policy
            required_encryption_algorithms := ["AES256", "RSA-OAEP"]
            
            allow if {
                input.operation == "Microsoft.Storage/storageAccounts/write"
                input.resource.properties.supportsHttpsTrafficOnly == true
                input.resource.properties.minimumTlsVersion == "TLS1_2"
                input.resource.properties.encryption.services.blob.enabled == true
                input.resource.properties.encryption.keySource == "Microsoft.Storage"
                input.resource.properties.allowBlobPublicAccess == false
                input.resource.properties.networkAcls.defaultAction == "Deny"
                count(input.resource.properties.networkAcls.ipRules) > 0
            }
            "#,
            vec![
                r#"{
                    "operation": "Microsoft.Storage/storageAccounts/write",
                    "resource": {
                        "properties": {
                            "supportsHttpsTrafficOnly": true,
                            "minimumTlsVersion": "TLS1_2",
                            "encryption": {
                                "services": {"blob": {"enabled": true}},
                                "keySource": "Microsoft.Storage"
                            },
                            "allowBlobPublicAccess": false,
                            "networkAcls": {
                                "defaultAction": "Deny",
                                "ipRules": [{"value": "203.0.113.0/24", "action": "Allow"}]
                            }
                        }
                    }
                }"#,
                r#"{
                    "operation": "Microsoft.Storage/storageAccounts/write",
                    "resource": {
                        "properties": {
                            "supportsHttpsTrafficOnly": true,
                            "minimumTlsVersion": "TLS1_2",
                            "encryption": {
                                "services": {"blob": {"enabled": true}, "file": {"enabled": true}},
                                "keySource": "Microsoft.Storage"
                            },
                            "allowBlobPublicAccess": false,
                            "networkAcls": {
                                "defaultAction": "Deny",
                                "ipRules": [
                                    {"value": "192.168.1.0/24", "action": "Allow"},
                                    {"value": "10.0.0.0/16", "action": "Allow"}
                                ]
                            }
                        }
                    }
                }"#,
                r#"{
                    "operation": "Microsoft.Storage/storageAccounts/write",
                    "resource": {
                        "properties": {
                            "supportsHttpsTrafficOnly": true,
                            "minimumTlsVersion": "TLS1_2",
                            "encryption": {
                                "services": {"blob": {"enabled": true}},
                                "keySource": "Microsoft.Storage"
                            },
                            "allowBlobPublicAccess": false,
                            "networkAcls": {
                                "defaultAction": "Deny",
                                "ipRules": [{"value": "172.16.0.0/12", "action": "Allow"}]
                            }
                        }
                    }
                }"#,
            ],
        ),
        (
            r#"
            package bench
            
            default allow := false
            
            # Azure Key Vault access policy
            valid_operations := [
                "Microsoft.KeyVault/vaults/keys/read",
                "Microsoft.KeyVault/vaults/secrets/read",
                "Microsoft.KeyVault/vaults/certificates/read"
            ]
            
            vault_admins := ["admin@company.com", "security@company.com"]
            
            allow if {
                input.operation in valid_operations
                input.principal.type == "ServicePrincipal"
                input.principal.appId != ""
                input.resource.properties.enableSoftDelete == true
                input.resource.properties.enablePurgeProtection == true
                time.now_ns() - input.principal.createdTime < 31536000000000000  # Less than 1 year old
            }
            
            allow if {
                input.operation in valid_operations
                input.principal.type == "User"
                input.principal.userPrincipalName in vault_admins
                input.context.conditionalAccess.compliant == true
            }
            "#,
            vec![
                r#"{
                    "operation": "Microsoft.KeyVault/vaults/secrets/read",
                    "principal": {
                        "type": "ServicePrincipal",
                        "appId": "12345678-1234-1234-1234-123456789012",
                        "createdTime": 1640995200000000000
                    },
                    "resource": {
                        "properties": {
                            "enableSoftDelete": true,
                            "enablePurgeProtection": true
                        }
                    }
                }"#,
                r#"{
                    "operation": "Microsoft.KeyVault/vaults/keys/read",
                    "principal": {
                        "type": "User",
                        "userPrincipalName": "admin@company.com"
                    },
                    "resource": {
                        "properties": {
                            "enableSoftDelete": true,
                            "enablePurgeProtection": true
                        }
                    },
                    "context": {
                        "conditionalAccess": {"compliant": true}
                    }
                }"#,
                r#"{
                    "operation": "Microsoft.KeyVault/vaults/certificates/read",
                    "principal": {
                        "type": "ServicePrincipal",
                        "appId": "87654321-4321-4321-4321-210987654321",
                        "createdTime": 1672531200000000000
                    },
                    "resource": {
                        "properties": {
                            "enableSoftDelete": true,
                            "enablePurgeProtection": true
                        }
                    }
                }"#,
            ],
        ),
        (
            r#"
            package bench
            
            default allow := false
            
            # Azure Network Security Group rules policy
            dangerous_ports := [22, 3389, 1433, 3306, 5432, 6379, 27017]
            internal_networks := ["10.0.0.0/8", "172.16.0.0/12", "192.168.0.0/16"]
            
            is_internal_source if {
                some network in internal_networks
                net.cidr_contains(network, input.rule.sourceAddressPrefix)
            }
            
            allow if {
                input.operation == "Microsoft.Network/networkSecurityGroups/securityRules/write"
                input.rule.direction == "Inbound"
                input.rule.access == "Allow"
                input.rule.destinationPortRange != "*"
                not input.rule.destinationPortRange in dangerous_ports
                input.rule.sourceAddressPrefix != "*"
                input.rule.sourceAddressPrefix != "Internet"
            }
            
            allow if {
                input.operation == "Microsoft.Network/networkSecurityGroups/securityRules/write"
                input.rule.direction == "Inbound"
                input.rule.access == "Allow"
                input.rule.destinationPortRange in dangerous_ports
                is_internal_source
                input.rule.priority >= 1000
            }
            "#,
            vec![
                r#"{
                    "operation": "Microsoft.Network/networkSecurityGroups/securityRules/write",
                    "rule": {
                        "direction": "Inbound",
                        "access": "Allow",
                        "destinationPortRange": "80",
                        "sourceAddressPrefix": "203.0.113.0/24",
                        "priority": 100
                    }
                }"#,
                r#"{
                    "operation": "Microsoft.Network/networkSecurityGroups/securityRules/write",
                    "rule": {
                        "direction": "Inbound",
                        "access": "Allow",
                        "destinationPortRange": "22",
                        "sourceAddressPrefix": "10.0.1.0/24",
                        "priority": 1100
                    }
                }"#,
                r#"{
                    "operation": "Microsoft.Network/networkSecurityGroups/securityRules/write",
                    "rule": {
                        "direction": "Inbound",
                        "access": "Allow",
                        "destinationPortRange": "443",
                        "sourceAddressPrefix": "198.51.100.0/24",
                        "priority": 200
                    }
                }"#,
            ],
        ),
    ];

    // Policy names for tracking
    let policy_names = vec![
        "rbac_policy",
        "data_sensitivity_policy",
        "time_based_policy",
        "azure_vm_policy",
        "azure_storage_policy",
        "azure_keyvault_policy",
        "azure_nsg_policy",
        "network_security_policy",
        "compliance_policy",
    ];

    // Initialize policy evaluation counters
    let policy_counters = Arc::new(Mutex::new(HashMap::new()));
    for policy_name in &policy_names {
        policy_counters
            .lock()
            .unwrap()
            .insert(policy_name.to_string(), 0);
    }

    let barrier = Arc::new(Barrier::new(num_threads));
    let mut handles = Vec::with_capacity(num_threads);

    for thread_id in 0..num_threads {
        let barrier = barrier.clone();
        let policies_with_inputs = policies_with_inputs.clone();
        let policy_names = policy_names.clone();
        let policy_counters = policy_counters.clone();

        handles.push(thread::spawn(move || {
            let mut elapsed = std::time::Duration::ZERO;

            // Pre-create engines if using cloned engines
            let engines = if use_cloned_engines {
                Some(
                    policies_with_inputs
                        .iter()
                        .map(|(policy, _)| {
                            let mut engine = Engine::new();
                            engine
                                .add_policy("policy.rego".to_string(), policy.to_string())
                                .unwrap();
                            engine
                        })
                        .collect::<Vec<_>>(),
                )
            } else {
                None
            };

            // Pre-parse inputs if using cloned inputs
            let parsed_inputs = if use_cloned_inputs {
                Some(
                    policies_with_inputs
                        .iter()
                        .map(|(_, inputs)| {
                            inputs
                                .iter()
                                .map(|input_str| regorus::Value::from_json_str(input_str).unwrap())
                                .collect::<Vec<_>>()
                        })
                        .collect::<Vec<_>>(),
                )
            } else {
                None
            };

            barrier.wait();
            for i in 0..evals_per_thread {
                // Use different policy for each iteration
                let policy_idx = (thread_id + i) % policies_with_inputs.len();
                let (policy, inputs) = &policies_with_inputs[policy_idx];

                // Use different input for the same policy based on iteration
                let input_idx = i % inputs.len();
                let input = &inputs[input_idx];

                let start = std::time::Instant::now();

                let mut engine = if use_cloned_engines {
                    engines.as_ref().unwrap()[policy_idx].clone()
                } else {
                    let mut engine = Engine::new();
                    engine
                        .add_policy("policy.rego".to_string(), policy.to_string())
                        .unwrap();
                    engine
                };

                let input_value = if use_cloned_inputs {
                    parsed_inputs.as_ref().unwrap()[policy_idx][input_idx].clone()
                } else {
                    regorus::Value::from_json_str(input).unwrap()
                };

                engine.set_input(input_value);

                let result = engine.eval_rule("data.bench.allow".to_string());
                elapsed += start.elapsed();

                // Track successful evaluations
                if result.is_ok() {
                    if let Some(policy_name) = policy_names.get(policy_idx) {
                        let mut counters = policy_counters.lock().unwrap();
                        *counters.entry(policy_name.to_string()).or_insert(0) += 1;
                    }
                }
            }
            elapsed
        }));
    }

    let mut total = std::time::Duration::ZERO;
    for handle in handles {
        total += handle.join().unwrap();
    }

    let final_counters = policy_counters.lock().unwrap().clone();
    (total, final_counters)
}

fn criterion_benchmark(c: &mut Criterion) {
    let max_threads = num_cpus::get() * 2;
    println!("Running benchmark with max_threads: {}", max_threads);

    let evals_per_thread = 1000;

    // Benchmark all combinations of cloned engines and inputs
    for use_cloned_engines in [true, false] {
        for use_cloned_inputs in [true, false] {
            let group_name = match (use_cloned_engines, use_cloned_inputs) {
                (true, true) => "cloned_engines , cloned_inputs ",
                (true, false) => "cloned_engines , fresh_inputs  ",
                (false, true) => "fresh_engines  , cloned_inputs ",
                (false, false) => "fresh_engines  , fresh_inputs  ",
            };

            let mut group = c.benchmark_group(group_name);
            group.measurement_time(Duration::from_secs(5));

            // Test specific thread counts: powers of 2 + some intermediate values
            let thread_counts: Vec<usize> = (1..=max_threads)
                .filter(|&n| {
                    n == 1 || // Always test single-threaded
                    n % 2 == 0 || // Always test even threads
                    n == max_threads // Maximum threads
                })
                .collect();

            for threads in thread_counts {
                let total_evals = threads * evals_per_thread;
                group.throughput(Throughput::Elements(total_evals as u64));
                group.bench_with_input(
                    BenchmarkId::new("eval", format!(" {threads} threads")),
                    &threads,
                    |b, &threads| {
                        b.iter_custom(|iters| {
                            let evals_per_thread = evals_per_thread * (iters as usize);
                            let (duration, policy_counters) = multi_threaded_eval(
                                black_box(threads),
                                black_box(evals_per_thread),
                                black_box(use_cloned_engines),
                                black_box(use_cloned_inputs),
                            );

                            // On one iteration, print policy evaluation statistics
                            if iters == 1 {
                                // println!("\nPolicy Evaluation Statistics:");
                                for (policy_name, count) in &policy_counters {
                                    // println!("  {}: {} evaluations", policy_name, count);
                                    if *count == 0 {
                                        println!("\x1b[31mERROR: Policy '{}' was never evaluated successfully!\x1b[0m", policy_name);
                                    }
                                }
                            }

                            duration
                        });
                    },
                );
            }
            group.finish();
        }
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
