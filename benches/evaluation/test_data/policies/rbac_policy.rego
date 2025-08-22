package bench

default allow := false

allow if {
    input.user.role == "admin"
    input.action in ["read", "write", "delete"]
    input.resource.classification in ["public", "internal"]
    count(input.user.permissions) > 0
}
