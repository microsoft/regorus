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
