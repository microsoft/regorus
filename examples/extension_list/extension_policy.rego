package extension_policy

import rego.v1

allowed_extensions[name] := extension if {
	check_all_data_allowed(data.allowed) # Checks if 'all' is a key in data.allowed
	some name, input_extension in input.incoming # Assign any incoming extension name to 'name'
	extension := input_extension # Assign the extension itself
}

allowed_extensions[name] := extension if {
	some name, input_extension in input.incoming
	extension_is_allowed(input_extension, data.allowed, name)
	extension := object.union(input_extension, data.allowed[name])
}

extension_is_allowed(input_data, allowed_data, name) if {
	allowed_data[name]
	check_optional_properties(input_data, allowed_data[name])
}

check_optional_properties(input_data, allowed) if {
	not allowed.version
} else if {
	allowed.version
	input_data.version == allowed.version
}

check_all_data_allowed(data_allowed) if {
	data_allowed.all
} else if {
	data_allowed.ALL
} else if {
	data_allowed.All
}

denied_extensions[name] := extension if {
	not check_all_data_allowed(data.allowed)
	some name, input_extension in input.incoming
	not extension_is_allowed(input_extension, data.allowed, name)
	extension := input_extension
}
