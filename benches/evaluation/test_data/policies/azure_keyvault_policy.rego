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
