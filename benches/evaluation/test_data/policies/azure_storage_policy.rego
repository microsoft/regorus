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
