package test

y := 5 if {
	[1, 2]
	[{1, 3}, {4, 5}]
	[
		{"a": 5},
		{"a": 6},
	]
	[
		1 > 2,
		3 < 4,
		5 == 6,
	]
	input.type == "VM"
	input.location in ["eastus", "westus"]

	#input.zone == 5
	resource := input
        resource.location == "eastus"
        #{1} > {2}
}

is_valid := true if {
	 input.location in ["eastus", "universe"]
}

modify := a if {
       input.type == "VM"
       a := {
       	 "action": "append",
	 "param": 5
       }
}
