package extension_policy

import rego.v1

allowed_extensions[name] := extension if {
	some name, input_extension in input.incoming
	extension_is_allowed(input_extension, data.allowed[name])
	extension := object.union(input_extension, data.allowed[name])
}

extension_is_allowed(input_data, allowed_data) if {
	allowed_data
	check_optional_properties(input_data, allowed_data)
}

check_optional_properties(input_data, allowed) if {
	not allowed.version
} else if {
	allowed.version
	input_data.version == allowed.version
}

denied_extensions[name] := extension if {
	some name, input_extension in input.incoming
	not extension_is_allowed(input_extension, data.allowed[name])
	extension := input_extension
}
