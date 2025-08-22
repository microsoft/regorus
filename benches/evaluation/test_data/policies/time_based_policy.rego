package bench

default allow := false

# Time-based access control with complex conditions
business_hours if {
    hour := time.clock([time.now_ns(), "America/New_York"])[0]
    hour >= 9
    hour < 17
}

allow if {
    input.user.department in ["engineering", "product"]
    input.action == "deploy"
    business_hours
    count([x | x := input.approvals[_]; x.status == "approved"]) >= 2
}

allow if {
    input.user.emergency_access == true
    input.action in ["read", "diagnose"]
    input.justification != ""
}
