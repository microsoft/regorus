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
