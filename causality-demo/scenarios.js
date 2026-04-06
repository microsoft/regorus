export const scenarios = [
  {
    id: "k8s-admission",
    navTitle: "K8s Admission",
    navSubtitle: "Why was my pod rejected?",
    title: "Kubernetes admission control with stacked violations",
    summary: "A Gatekeeper-style policy checks container images, privilege escalation, and resource limits across every container. Two of three containers pass cleanly — the explanation traces the two violations to the one problematic container.",
    focus: "Comprehension witnesses + regex",
    features: ["set comprehension","regex.match","nested iteration","stacked violations","container tracing"],
    engine: "rvm",
    query: "data.k8s.deny",
    whyBindings: true,
    whyFullValues: true,
    whyAllConditions: true,
    assumeUnknownInput: false,
    detail: "standard",
    policy: `package k8s
import rego.v1

deny contains msg if {
    container := input.request.object.spec.containers[_]
    not regex.match("^[a-z0-9]+[.]azurecr[.]io/", container.image)
    msg := sprintf("container '%v' uses untrusted registry: %v", [container.name, container.image])
}

deny contains msg if {
    container := input.request.object.spec.containers[_]
    container.securityContext.privileged
    msg := sprintf("container '%v' must not run privileged", [container.name])
}

deny contains msg if {
    container := input.request.object.spec.containers[_]
    not container.resources.limits
    msg := sprintf("container '%v' is missing resource limits", [container.name])
}

deny contains msg if {
    container := input.request.object.spec.containers[_]
    container.securityContext.runAsUser == 0
    msg := sprintf("container '%v' must not run as root (uid 0)", [container.name])
}`,
    data: "{}",
    input: `{
  "request": {
    "kind": {
      "kind": "Pod"
    },
    "object": {
      "metadata": {
        "name": "web-app",
        "namespace": "production"
      },
      "spec": {
        "containers": [
          {
            "name": "frontend",
            "image": "mycompany.azurecr.io/frontend:v2.1",
            "resources": {
              "limits": {
                "cpu": "500m",
                "memory": "256Mi"
              }
            },
            "securityContext": {
              "privileged": false,
              "runAsUser": 1000
            }
          },
          {
            "name": "sidecar-debug",
            "image": "ghcr.io/debug-tools:latest",
            "resources": {
              "limits": {
                "cpu": "200m",
                "memory": "128Mi"
              }
            },
            "securityContext": {
              "privileged": true,
              "runAsUser": 1000
            }
          },
          {
            "name": "log-agent",
            "image": "mycompany.azurecr.io/log-agent:v1.0",
            "resources": {
              "limits": {
                "cpu": "100m",
                "memory": "64Mi"
              }
            },
            "securityContext": {
              "privileged": false,
              "runAsUser": 1000
            }
          }
        ]
      }
    }
  }
}`
  },
  {
    id: "rbac-resolution",
    navTitle: "RBAC Resolution",
    navSubtitle: "Why was this user denied?",
    title: "Role-based access with iteration witnesses",
    summary: "Eve requests write access to /reports/quarterly-summary but holds only a read grant on /public/*. The explanation walks both allow rules, showing that the action mismatch on her sole grant blocks evaluation before the scope glob is ever reached.",
    focus: "Grant iteration witnesses",
    features: ["some x in","glob.match","iteration witnesses","action mismatch","scope short-circuit"],
    engine: "rvm",
    query: "data.rbac.allow",
    whyBindings: true,
    whyFullValues: true,
    whyAllConditions: true,
    assumeUnknownInput: false,
    detail: "standard",
    policy: `package rbac
import rego.v1

default allow := false

allow if {
    some grant in data.role_grants[input.user]
    grant.action == input.action
    glob.match(grant.scope, ["/"], input.resource)
}

allow if {
    some grant in data.role_grants[input.user]
    grant.action == "*"
    glob.match(grant.scope, ["/"], input.resource)
}`,
    data: `{
  "role_grants": {
    "alice": [
      {"role": "viewer", "action": "read", "scope": "/reports/*"},
      {"role": "editor", "action": "write", "scope": "/reports/drafts/*"},
      {"role": "viewer", "action": "read", "scope": "/dashboards/*"}
    ],
    "bob": [
      {"role": "admin", "action": "*", "scope": "/admin/*"},
      {"role": "viewer", "action": "read", "scope": "/reports/*"}
    ],
    "eve": [
      {"role": "viewer", "action": "read", "scope": "/public/*"}
    ]
  }
}`,
    input: `{
  "user": "eve",
  "action": "write",
  "resource": "/reports/quarterly-summary"
}`
  },
  {
    id: "terraform-compliance",
    navTitle: "Cloud Compliance",
    navSubtitle: "Which resources are non-compliant?",
    title: "Terraform resource compliance audit",
    summary: "Infrastructure-as-code policies check encryption, tagging, public exposure, and backup requirements across four resources. Two pass cleanly while the explanation pinpoints the three failing checks — missing encryption and missing backups — on the other two.",
    focus: "Glob matching + infra policies",
    features: ["glob.match","nested checks","infra compliance","encryption audit","backup enforcement"],
    engine: "rvm",
    query: "data.terraform.violations",
    whyBindings: true,
    whyFullValues: true,
    whyAllConditions: true,
    assumeUnknownInput: false,
    detail: "standard",
    policy: `package terraform
import rego.v1

violations contains msg if {
    resource := input.resources[_]
    not resource.tags.environment
    msg := sprintf("%v (%v): missing required 'environment' tag", [resource.name, resource.type])
}

violations contains msg if {
    resource := input.resources[_]
    not resource.tags.owner
    msg := sprintf("%v (%v): missing required 'owner' tag", [resource.name, resource.type])
}

violations contains msg if {
    resource := input.resources[_]
    resource.type == "storage_account"
    not resource.properties.encryption.enabled
    msg := sprintf("%v: storage account must have encryption enabled", [resource.name])
}

violations contains msg if {
    resource := input.resources[_]
    resource.properties.public_access
    not resource.properties.encryption.enabled
    msg := sprintf("%v: public resource without encryption", [resource.name])
}

violations contains msg if {
    resource := input.resources[_]
    glob.match("*-prod-*", ["-"], resource.name)
    not resource.properties.backup_enabled
    msg := sprintf("%v: production resource must have backups enabled", [resource.name])
}`,
    data: "{}",
    input: `{
  "resources": [
    {
      "name": "api-prod-westus",
      "type": "app_service",
      "tags": {
        "environment": "production",
        "owner": "platform-team"
      },
      "properties": {
        "public_access": true,
        "encryption": {
          "enabled": true
        },
        "backup_enabled": true
      }
    },
    {
      "name": "data-prod-eastus",
      "type": "storage_account",
      "tags": {
        "environment": "production",
        "owner": "data-team"
      },
      "properties": {
        "public_access": false,
        "encryption": {
          "enabled": false
        },
        "backup_enabled": false
      }
    },
    {
      "name": "cache-staging-westus",
      "type": "redis_cache",
      "tags": {
        "environment": "staging",
        "owner": "platform-team"
      },
      "properties": {
        "public_access": false,
        "encryption": {
          "enabled": true
        },
        "backup_enabled": false
      }
    },
    {
      "name": "logs-prod-centralus",
      "type": "storage_account",
      "tags": {
        "environment": "production",
        "owner": "sre-team"
      },
      "properties": {
        "public_access": false,
        "encryption": {
          "enabled": true
        },
        "backup_enabled": false
      }
    }
  ]
}`
  },
  {
    id: "supply-chain",
    navTitle: "Supply Chain",
    navSubtitle: "Trace license violations through deps",
    title: "SBOM supply chain license audit",
    summary: "Four dependencies are audited — two are fully clean. The explanation traces one direct license violation and one transitive GPL dependency pulled in through an otherwise-approved package.",
    focus: "Deep nested dependency tracing",
    features: ["transitive deps","nested iteration","license audit","SBOM","supply chain"],
    engine: "rvm",
    query: "data.sbom.issues",
    whyBindings: true,
    whyFullValues: true,
    whyAllConditions: true,
    assumeUnknownInput: false,
    detail: "standard",
    policy: `package sbom
import rego.v1

approved_licenses := {"MIT", "Apache-2.0", "BSD-2-Clause", "BSD-3-Clause", "ISC"}

issues contains msg if {
    dep := input.dependencies[_]
    not dep.license in approved_licenses
    msg := sprintf("direct dependency '%v' uses unapproved license: %v", [dep.name, dep.license])
}

issues contains msg if {
    dep := input.dependencies[_]
    transitive := dep.requires[_]
    pkg := data.package_registry[transitive]
    not pkg.license in approved_licenses
    msg := sprintf("transitive dependency '%v' (via '%v') uses unapproved license: %v", [transitive, dep.name, pkg.license])
}

issues contains msg if {
    dep := input.dependencies[_]
    transitive := dep.requires[_]
    not data.package_registry[transitive]
    msg := sprintf("transitive dependency '%v' (via '%v') is not in the package registry", [transitive, dep.name])
}

issues contains msg if {
    dep := input.dependencies[_]
    dep.deprecated
    msg := sprintf("dependency '%v' is deprecated", [dep.name])
}`,
    data: `{
  "package_registry": {
    "zlib": {
      "version": "1.3.1",
      "license": "MIT"
    },
    "openssl": {
      "version": "3.2.0",
      "license": "Apache-2.0"
    },
    "libgmp": {
      "version": "6.3.0",
      "license": "GPL-3.0"
    },
    "sqlite": {
      "version": "3.45.0",
      "license": "BSD-2-Clause"
    },
    "curl": {
      "version": "8.6.0",
      "license": "MIT"
    },
    "libyaml": {
      "version": "0.2.5",
      "license": "MIT"
    }
  }
}`,
    input: `{
  "dependencies": [
    {
      "name": "web-framework",
      "version": "4.2.0",
      "license": "MIT",
      "deprecated": false,
      "requires": [
        "openssl",
        "zlib",
        "libyaml"
      ]
    },
    {
      "name": "crypto-utils",
      "version": "2.1.0",
      "license": "Apache-2.0",
      "deprecated": false,
      "requires": [
        "openssl",
        "libgmp"
      ]
    },
    {
      "name": "data-layer",
      "version": "3.0.0",
      "license": "BSD-3-Clause",
      "deprecated": false,
      "requires": [
        "sqlite",
        "curl"
      ]
    },
    {
      "name": "legacy-xml-parser",
      "version": "0.9.3",
      "license": "LGPL-2.1",
      "deprecated": false,
      "requires": [
        "zlib"
      ]
    }
  ]
}`
  },
  {
    id: "release-gate",
    navTitle: "Release Gate",
    navSubtitle: "Decision rule plus every witness",
    title: "Release decisions with causal witnesses",
    summary: "The ship decision evaluates to false despite the branch check and all three required CI checks passing — two critical findings block it: a GPL-3.0 runtime dependency and an unauthenticated public service. The explanation shows both the passing helpers and the blocking findings.",
    focus: "Decision + helper + every",
    features: ["every","complete decision","supporting findings","all contributing"],
    engine: "rvm",
    query: "data.demo.ship",
    whyBindings: false,
    whyFullValues: false,
    whyAllConditions: true,
    assumeUnknownInput: false,
    detail: "standard",
    policy: `package demo
import rego.v1

default ship := false

ship if {
    release_branch
    all_required_checks_pass
    count(critical_findings) == 0
}

release_branch if {
    startswith(input.build.branch, "release/")
}

all_required_checks_pass if {
    every check in input.build.required_checks {
        check.passed
    }
}

critical_findings contains msg if {
    dep := input.build.dependencies[_]
    dep.runtime
    dep.license == "GPL-3.0"
    msg := sprintf("runtime dependency %v uses GPL-3.0", [dep.name])
}

critical_findings contains msg if {
    svc := input.services[_]
    svc.public
    svc.auth == "none"
    msg := sprintf("public service %v has no auth", [svc.name])
}`,
    data: "{}",
    input: `{
  "build": {
    "branch": "release/2026.03",
    "required_checks": [
      {"name": "unit", "passed": true},
      {"name": "integration", "passed": true},
      {"name": "sbom", "passed": true}
    ],
    "dependencies": [
      {"name": "openssl", "runtime": true, "license": "Apache-2.0"},
      {"name": "legacy-crypto", "runtime": true, "license": "GPL-3.0"}
    ]
  },
  "services": [
    {"name": "public-api", "public": true, "auth": "oauth2"},
    {"name": "debug-ui", "public": true, "auth": "none"}
  ]
}`
  },
  {
    id: "fraud-signals",
    navTitle: "Fraud Signals",
    navSubtitle: "Many contributing conditions in one alert",
    title: "Stacked evidence for suspicious activity",
    summary: "All-contributing mode surfaces every condition behind two fraud alerts — string builtins, amount thresholds, country mismatch, and a negated card-present check — showing how each signal contributed to the flagged transactions.",
    focus: "All-contributing evidence",
    features: ["multiple findings","builtins","comparisons","negation"],
    engine: "rvm",
    query: "data.demo.alerts",
    whyBindings: false,
    whyFullValues: false,
    whyAllConditions: true,
    assumeUnknownInput: false,
    detail: "standard",
    policy: `package demo
import rego.v1

alerts contains msg if {
    txn := input.transactions[_]
    startswith(lower(txn.merchant), "gift")
    txn.amount >= 500
    txn.country != input.account.home_country
    not txn.card_present
    msg := sprintf("transaction %v looks like gift-card laundering", [txn.id])
}

alerts contains msg if {
    txn := input.transactions[_]
    endswith(lower(txn.merchant), ".ru")
    txn.amount > 100
    msg := sprintf("transaction %v targets suspicious merchant domain", [txn.id])
}`,
    data: "{}",
    input: `{
  "account": {
    "home_country": "US"
  },
  "transactions": [
    {
      "id": "tx-100",
      "merchant": "gift galaxy",
      "amount": 1200,
      "country": "MT",
      "card_present": false
    },
    {
      "id": "tx-101",
      "merchant": "compute-hub.ru",
      "amount": 240,
      "country": "US",
      "card_present": true
    },
    {
      "id": "tx-102",
      "merchant": "coffee-stop",
      "amount": 8,
      "country": "US",
      "card_present": true
    }
  ]
}`
  },
  {
    id: "feature-flags",
    navTitle: "Feature Flags",
    navSubtitle: "Why did this user get this variant?",
    title: "Feature flag targeting with segment rules",
    summary: "A targeting engine decides which feature variant a user sees based on allowlists, attribute rules, and percentage rollouts. The explanation pinpoints the exact rule that matched.",
    focus: "Multiple rule heads + targeting",
    features: ["multiple rules","contains","percentage rollout","segment targeting","first match"],
    engine: "rvm",
    query: "data.flags.variant",
    whyBindings: true,
    whyFullValues: true,
    whyAllConditions: false,
    assumeUnknownInput: false,
    detail: "standard",
    policy: `package flags
import rego.v1

default variant := "control"

# VIP allowlist gets early access
variant := "early-access" if {
    input.user.id in data.flag_config.allowlist
}

# Beta testers get the new variant
variant := "beta" if {
    input.user.beta_tester
    input.user.account_age_days > 30
}

# Percentage rollout for remaining users in target region
variant := "treatment-a" if {
    input.user.region in data.flag_config.target_regions
    hash := strings.replace_n({" ": "", "-": ""}, input.user.id)
    bucket := count(hash) % 100
    bucket < data.flag_config.rollout_percent
}`,
    data: `{
  "flag_config": {
    "allowlist": ["user-ceo-001", "user-pm-042", "user-eng-099"],
    "target_regions": ["us-west", "eu-central"],
    "rollout_percent": 25
  }
}`,
    input: `{
  "user": {
    "id": "user-trial-555",
    "region": "us-west",
    "beta_tester": false,
    "account_age_days": 12,
    "plan": "free"
  }
}`
  },
  {
    id: "schema-validation",
    navTitle: "Schema Validation",
    navSubtitle: "Which fields failed type checks?",
    title: "Data pipeline schema validation with type builtins",
    summary: "Type-checking builtins like is_string and is_number trace each assertion. Two of four records pass cleanly — the explanation shows exactly which records and fields violate the expected schema.",
    focus: "Type-check builtin tracing",
    features: ["is_string","is_number","is_array","type builtins","data quality"],
    engine: "rvm",
    query: "data.schema.errors",
    whyBindings: true,
    whyFullValues: true,
    whyAllConditions: true,
    assumeUnknownInput: false,
    detail: "standard",
    policy: `package schema
import rego.v1

errors contains msg if {
    record := input.records[_]
    not is_string(record.email)
    msg := sprintf("record %v: email must be a string, got %v", [record.id, type_name(record.email)])
}

errors contains msg if {
    record := input.records[_]
    not is_number(record.age)
    msg := sprintf("record %v: age must be a number, got %v", [record.id, type_name(record.age)])
}

errors contains msg if {
    record := input.records[_]
    is_number(record.age)
    record.age < 0
    msg := sprintf("record %v: age cannot be negative (%v)", [record.id, record.age])
}

errors contains msg if {
    record := input.records[_]
    not is_array(record.tags)
    msg := sprintf("record %v: tags must be an array", [record.id])
}

errors contains msg if {
    record := input.records[_]
    is_string(record.email)
    not contains(record.email, "@")
    msg := sprintf("record %v: email '%v' missing @ symbol", [record.id, record.email])
}`,
    data: "{}",
    input: `{
  "records": [
    {
      "id": "r-001",
      "email": "alice@example.com",
      "age": 30,
      "tags": [
        "active",
        "premium"
      ]
    },
    {
      "id": "r-002",
      "email": 12345,
      "age": "twenty-five",
      "tags": "not-an-array"
    },
    {
      "id": "r-003",
      "email": "bob@example.com",
      "age": -3,
      "tags": [
        "trial"
      ]
    },
    {
      "id": "r-004",
      "email": "carol@example.com",
      "age": 42,
      "tags": [
        "active"
      ]
    }
  ]
}`
  },
  {
    id: "allowed-server",
    navTitle: "Allowed Server",
    navSubtitle: "Complete rule with helper-chain causality",
    title: "Complete-rule why chain",
    summary: "The allow decision is false because two servers violate the policy — one uses HTTP on a public network, another uses telnet. The causal chain walks from the top-level allow through the violation and public_server helpers, preserving every loop witness along the way.",
    focus: "Helper-chain preservation",
    features: ["complete rule","helper rule","loop witness","browser wasm"],
    engine: "rvm",
    query: "data.example.allow",
    whyBindings: false,
    whyFullValues: false,
    whyAllConditions: false,
    assumeUnknownInput: false,
    detail: "standard",
    policy: `package example
import rego.v1

default allow := false

allow := true if {
    count(violation) == 0
}

violation contains server.id if {
    some server
    public_server[server]
    server.protocols[_] == "http"
}

violation contains server.id if {
    server := input.servers[_]
    server.protocols[_] == "telnet"
}

public_server contains server if {
    some i, j
    server := input.servers[_]
    server.ports[_] == input.ports[i].id
    input.ports[i].network == input.networks[j].id
    input.networks[j].public
}`,
    data: "{}",
    input: `{
  "servers": [
    {"id": "app", "protocols": ["https", "ssh"], "ports": ["p1", "p2", "p3"]},
    {"id": "db", "protocols": ["mysql"], "ports": ["p3"]},
    {"id": "cache", "protocols": ["memcache"], "ports": ["p3"]},
    {"id": "ci", "protocols": ["http"], "ports": ["p1", "p2"]},
    {"id": "busybox", "protocols": ["telnet"], "ports": ["p1"]}
  ],
  "ports": [
    {"id": "p1", "network": "net1"},
    {"id": "p2", "network": "net3"},
    {"id": "p3", "network": "net2"}
  ],
  "networks": [
    {"id": "net1", "public": false},
    {"id": "net2", "public": false},
    {"id": "net3", "public": true},
    {"id": "net4", "public": true}
  ]
}`
  },
  {
    id: "timezone-negated",
    navTitle: "Negated Helper",
    navSubtitle: "Surface the failing inner condition",
    title: "Negation that still explains itself",
    summary: "Instead of only returning the outer not expression, why output reaches into the helper rule and exposes the failing inner condition.",
    focus: "Negated helper inlining",
    features: ["negation","helper rule","inner failing condition"],
    engine: "rvm",
    query: "data.demo.violations",
    whyBindings: false,
    whyFullValues: false,
    whyAllConditions: false,
    assumeUnknownInput: false,
    detail: "standard",
    policy: `package demo
import rego.v1

valid_clock_time_zone if {
    clock_timezone := data.config.DEVICE_METADATA.localhost
    clock_timezone.timezone == "UTC"
}

violations contains msg if {
    not valid_clock_time_zone
    msg := "The clock timezone is not set to UTC"
}`,
    data: `{
  "config": {
    "DEVICE_METADATA": {
      "localhost": {
        "timezone": "PST"
      }
    }
  }
}`,
    input: "{}"
  },
  {
    id: "secret-redaction",
    navTitle: "Secret Redaction",
    navSubtitle: "Compare redacted and full-value modes",
    title: "Reason capture without leaking secrets",
    summary: "The safe default keeps secret-looking values redacted while still preserving the causal record.",
    focus: "Redacted vs full values",
    features: ["binding capture","secret awareness","safe defaults"],
    engine: "rvm",
    query: "data.demo.violations",
    whyBindings: true,
    whyFullValues: false,
    whyAllConditions: true,
    assumeUnknownInput: false,
    detail: "standard",
    policy: `package demo
import rego.v1

violations contains msg if {
    request := input.requests[_]
    api_token := request.api_token
    request.path == "/admin"
    request.user != "admin"
    msg := sprintf("user %v attempted admin path", [request.user])
}

violations contains msg if {
    request := input.requests[_]
    password := request.password
    count(password) > 0
    request.path == "/login"
    request.user == "guest"
    msg := "guest login included password"
}`,
    data: "{}",
    input: `{
  "requests": [
    {
      "user": "alice",
      "path": "/admin",
      "api_token": "tok-prod-123",
      "password": ""
    },
    {
      "user": "guest",
      "path": "/login",
      "api_token": "",
      "password": "guest-password"
    }
  ]
}`
  },
  {
    id: "assumptions",
    navTitle: "Assumptions",
    navSubtitle: "What input makes this succeed?",
    title: "Input discovery via assumptions",
    summary: "When input is unknown or sparse, the engine assumes values that make the policy succeed and reports what it assumed.  This lets you discover what inputs a policy requires without supplying them upfront.",
    focus: "Assumed input paths",
    features: ["assume unknown input","input discovery","equality assumptions","alias tracking"],
    engine: "rvm",
    query: "data.deploy.allow",
    whyBindings: true,
    whyFullValues: true,
    whyAllConditions: true,
    assumeUnknownInput: true,
    detail: "full",
    policy: `package deploy
import rego.v1

default allow = false

role := input.identity.role
env  := input.target.environment

allow if {
    role == "release-admin"
    env  == "production"
}

allow if {
    role == "developer"
    env  == "staging"
}`,
    data: "{}",
    input: `{
  "identity": {
    "name": "alex"
  },
  "target": {
    "service": "api-gateway"
  }
}`
  }
];
