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
