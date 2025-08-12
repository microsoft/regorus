// This module provides the full set of policies, inputs, and policy names for evaluation benchmarks.
// Policies and inputs are now loaded from external files.

use std::fs;
use std::path::Path;

pub fn policies_with_inputs() -> Vec<(String, Vec<String>)> {
    let policy_with_input_files = [
        (
            "rbac_policy.rego",
            vec!["rbac_input.json", "rbac_input2.json", "rbac_input3.json"],
        ),
        (
            "api_access_policy.rego",
            vec![
                "api_access_input.json",
                "api_access_input2.json",
                "api_access_input3.json",
            ],
        ),
        (
            "data_sensitivity_policy.rego",
            vec![
                "data_sensitivity_input.json",
                "data_sensitivity_input2.json",
                "data_sensitivity_input3.json",
            ],
        ),
        (
            "time_based_policy.rego",
            vec![
                "time_based_input.json",
                "time_based_input2.json",
                "time_based_input3.json",
            ],
        ),
        (
            "data_processing_policy.rego",
            vec![
                "data_processing_input.json",
                "data_processing_input2.json",
                "data_processing_input3.json",
            ],
        ),
        (
            "azure_vm_policy.rego",
            vec![
                "azure_vm_input.json",
                "azure_vm_input2.json",
                "azure_vm_input3.json",
            ],
        ),
        (
            "azure_storage_policy.rego",
            vec![
                "azure_storage_input.json",
                "azure_storage_input2.json",
                "azure_storage_input3.json",
            ],
        ),
        (
            "azure_keyvault_policy.rego",
            vec![
                "azure_keyvault_input.json",
                "azure_keyvault_input2.json",
                "azure_keyvault_input3.json",
            ],
        ),
        (
            "azure_nsg_policy.rego",
            vec![
                "azure_nsg_input.json",
                "azure_nsg_input2.json",
                "azure_nsg_input3.json",
            ],
        ),
    ];

    let mut policies_and_inputs = Vec::new();
    let base_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("benches")
        .join("evaluation")
        .join("test_data");

    for (policy_file, input_files) in policy_with_input_files.iter() {
        let policy_path = base_dir.join("policies").join(policy_file);

        let policy_content = fs::read_to_string(&policy_path)
            .unwrap_or_else(|e| panic!("Failed to read policy file {:?}: {}", policy_path, e));

        let mut input_contents = Vec::new();
        for input_file in input_files {
            let input_path = base_dir.join("inputs").join(input_file);
            let input_content = fs::read_to_string(&input_path)
                .unwrap_or_else(|e| panic!("Failed to read input file {:?}: {}", input_path, e));
            input_contents.push(input_content);
        }

        policies_and_inputs.push((policy_content, input_contents));
    }

    policies_and_inputs
}

pub fn policy_names() -> Vec<&'static str> {
    vec![
        "rbac_policy",
        "api_access_policy",
        "data_sensitivity_policy",
        "time_based_policy",
        "data_processing_policy",
        "azure_vm_policy",
        "azure_storage_policy",
        "azure_keyvault_policy",
        "azure_nsg_policy",
    ]
}
