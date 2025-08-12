package bench

default allow := false

valid_api_paths := ["/api/v1/", "/api/v2/", "/api/v3/"]

allow if {
    input.request.method == "GET"
    some path in valid_api_paths
    startswith(input.request.path, path)
    input.user.authenticated == true
    time.now_ns() - input.user.login_time < 86400000000000  # 24 hours in nanoseconds
}
