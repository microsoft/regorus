package examples.assumptions

default allow := false

required_controls contains "owner approval" if {
    input.change.owner_approved == true
}

required_controls contains "security approval" if {
    input.change.security.approved == true
}

required_controls contains "prod maintenance window" if {
    input.release.environment == "prod"
    input.release.window.status == "approved"
}

role := input.identity.role
expected_role := "release-admin"

allow if {
    er := expected_role
    role == er
    count(required_controls) >= 2
}