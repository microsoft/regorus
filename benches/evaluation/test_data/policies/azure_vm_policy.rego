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
