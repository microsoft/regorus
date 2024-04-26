# Copyright (c) 2023 Microsoft Corporation
#
# SPDX-License-Identifier: Apache-2.0
#
package agent_policy

import future.keywords.in
import future.keywords.every

import input

# Default values, returned by OPA when rules cannot be evaluated to true.
default AddARPNeighborsRequest := false
default AddSwapRequest := false
default CloseStdinRequest := false
default CopyFileRequest := false
default CreateContainerRequest := false
default CreateSandboxRequest := false
default DestroySandboxRequest := true
default ExecProcessRequest := false
default GetOOMEventRequest := true
default GuestDetailsRequest := true
default ListInterfacesRequest := false
default ListRoutesRequest := false
default MemHotplugByProbeRequest := false
default OnlineCPUMemRequest := true
default PauseContainerRequest := false
default ReadStreamRequest := false
default RemoveContainerRequest := true
default RemoveStaleVirtiofsShareMountsRequest := true
default ReseedRandomDevRequest := false
default ResumeContainerRequest := false
default SetGuestDateTimeRequest := false
default SetPolicyRequest := false
default SignalProcessRequest := true
default StartContainerRequest := true
default StartTracingRequest := false
default StatsContainerRequest := true
default StopTracingRequest := false
default TtyWinResizeRequest := true
default UpdateContainerRequest := false
default UpdateEphemeralMountsRequest := false
default UpdateInterfaceRequest := true
default UpdateRoutesRequest := true
default WaitProcessRequest := true
default WriteStreamRequest := false

# AllowRequestsFailingPolicy := true configures the Agent to *allow any
# requests causing a policy failure*. This is an unsecure configuration
# but is useful for allowing unsecure pods to start, then connect to
# them and inspect OPA logs for the root cause of a failure.
default AllowRequestsFailingPolicy := false

CreateContainerRequest {
    i_oci := input.OCI
    i_storages := input.storages

    print("CreateContainerRequest: i_oci.Hooks =", i_oci.Hooks)
    is_null(i_oci.Hooks)

    print("CreateContainerRequest: i_oci.Linux.Seccomp =", i_oci.Linux.Seccomp)
    is_null(i_oci.Linux.Seccomp)

    some p_container in policy_data.containers
    print("======== CreateContainerRequest: trying next policy container")

    p_pidns := p_container.sandbox_pidns
    i_pidns := input.sandbox_pidns
    print("CreateContainerRequest: p_pidns =", p_pidns, "i_pidns =", i_pidns)
    p_pidns == i_pidns

    p_oci := p_container.OCI

    print("CreateContainerRequest: p Version =", p_oci.Version, "i Version =", i_oci.Version)
    p_oci.Version == i_oci.Version

    print("CreateContainerRequest: p Readonly =", p_oci.Root.Readonly, "i Readonly =", i_oci.Root.Readonly)
    p_oci.Root.Readonly == i_oci.Root.Readonly

    allow_anno(p_oci, i_oci)

    p_storages := p_container.storages
    allow_by_anno(p_oci, i_oci, p_storages, i_storages)

    allow_linux(p_oci, i_oci)

    print("CreateContainerRequest: true")
}

# Reject unexpected annotations.
allow_anno(p_oci, i_oci) {
    print("allow_anno 1: start")

    not i_oci.Annotations

    print("allow_anno 1: true")
}
allow_anno(p_oci, i_oci) {
    print("allow_anno 2: p Annotations =", p_oci.Annotations)
    print("allow_anno 2: i Annotations =", i_oci.Annotations)

    i_keys := object.keys(i_oci.Annotations)
    print("allow_anno 2: i keys =", i_keys)

    every i_key in i_keys {
        allow_anno_key(i_key, p_oci)
    }

    print("allow_anno 2: true")
}

allow_anno_key(i_key, p_oci) {
    print("allow_anno_key 1: i key =", i_key)

    startswith(i_key, "io.kubernetes.cri.")

    print("allow_anno_key 1: true")
}
allow_anno_key(i_key, p_oci) {
    print("allow_anno_key 2: i key =", i_key)

    some p_key, _ in p_oci.Annotations
    p_key == i_key

    print("allow_anno_key 2: true")
}

# Get the value of the "io.kubernetes.cri.sandbox-name" annotation and
# correlate it with other annotations and process fields.
allow_by_anno(p_oci, i_oci, p_storages, i_storages) {
    print("allow_by_anno 1: start")

    s_name := "io.kubernetes.cri.sandbox-name"

    not p_oci.Annotations[s_name]

    i_s_name := i_oci.Annotations[s_name]
    print("allow_by_anno 1: i_s_name =", i_s_name)

    allow_by_sandbox_name(p_oci, i_oci, p_storages, i_storages, i_s_name)

    print("allow_by_anno 1: true")
}
allow_by_anno(p_oci, i_oci, p_storages, i_storages) {
    print("allow_by_anno 2: start")

    s_name := "io.kubernetes.cri.sandbox-name"

    p_s_name := p_oci.Annotations[s_name]
    i_s_name := i_oci.Annotations[s_name]
    print("allow_by_anno 2: i_s_name =", i_s_name, "p_s_name =", p_s_name)

    allow_sandbox_name(p_s_name, i_s_name)
    allow_by_sandbox_name(p_oci, i_oci, p_storages, i_storages, i_s_name)

    print("allow_by_anno 2: true")
}

allow_by_sandbox_name(p_oci, i_oci, p_storages, i_storages, s_name) {
    print("allow_by_sandbox_name: start")

    s_namespace := "io.kubernetes.cri.sandbox-namespace"

    p_namespace := p_oci.Annotations[s_namespace]
    i_namespace := i_oci.Annotations[s_namespace]
    print("allow_by_sandbox_name: p_namespace =", p_namespace, "i_namespace =", i_namespace)
    p_namespace == i_namespace

    allow_by_container_types(p_oci, i_oci, s_name, p_namespace)
    allow_by_bundle_or_sandbox_id(p_oci, i_oci, p_storages, i_storages)
    allow_process(p_oci, i_oci, s_name)

    print("allow_by_sandbox_name: true")
}

allow_sandbox_name(p_s_name, i_s_name) {
    print("allow_sandbox_name 1: start")

    p_s_name == i_s_name

    print("allow_sandbox_name 1: true")
}
allow_sandbox_name(p_s_name, i_s_name) {
    print("allow_sandbox_name 2: start")

    # TODO: should generated names be handled differently?
    contains(p_s_name, "$(generated-name)")

    print("allow_sandbox_name 2: true")
}

# Check that the "io.kubernetes.cri.container-type" and
# "io.katacontainers.pkg.oci.container_type" annotations designate the
# expected type - either a "sandbox" or a "container". Then, validate
# other annotations based on the actual "sandbox" or "container" value
# from the input container.
allow_by_container_types(p_oci, i_oci, s_name, s_namespace) {
    print("allow_by_container_types: checking io.kubernetes.cri.container-type")

    c_type := "io.kubernetes.cri.container-type"
    
    p_cri_type := p_oci.Annotations[c_type]
    i_cri_type := i_oci.Annotations[c_type]
    print("allow_by_container_types: p_cri_type =", p_cri_type, "i_cri_type =", i_cri_type)
    p_cri_type == i_cri_type

    allow_by_container_type(i_cri_type, p_oci, i_oci, s_name, s_namespace)

    print("allow_by_container_types: true")
}

allow_by_container_type(i_cri_type, p_oci, i_oci, s_name, s_namespace) {
    print("allow_by_container_type 1: i_cri_type =", i_cri_type)
    i_cri_type == "sandbox"

    i_kata_type := i_oci.Annotations["io.katacontainers.pkg.oci.container_type"]
    print("allow_by_container_type 1: i_kata_type =", i_kata_type)
    i_kata_type == "pod_sandbox"

    allow_sandbox_container_name(p_oci, i_oci)
    allow_sandbox_net_namespace(p_oci, i_oci)
    allow_sandbox_log_directory(p_oci, i_oci, s_name, s_namespace)

    print("allow_by_container_type 1: true")
}

allow_by_container_type(i_cri_type, p_oci, i_oci, s_name, s_namespace) {
    print("allow_by_container_type 2: i_cri_type =", i_cri_type)
    i_cri_type == "container"

    i_kata_type := i_oci.Annotations["io.katacontainers.pkg.oci.container_type"]
    print("allow_by_container_type 2: i_kata_type =", i_kata_type)
    i_kata_type == "pod_container"

    allow_container_name(p_oci, i_oci)
    allow_net_namespace(p_oci, i_oci)
    allow_log_directory(p_oci, i_oci)

    print("allow_by_container_type 2: true")
}

# "io.kubernetes.cri.container-name" annotation
allow_sandbox_container_name(p_oci, i_oci) {
    print("allow_sandbox_container_name: start")

    container_annotation_missing(p_oci, i_oci, "io.kubernetes.cri.container-name")

    print("allow_sandbox_container_name: true")
}

allow_container_name(p_oci, i_oci) {
    print("allow_container_name: start")

    allow_container_annotation(p_oci, i_oci, "io.kubernetes.cri.container-name")

    print("allow_container_name: true")
}

container_annotation_missing(p_oci, i_oci, key) {
    print("container_annotation_missing:", key)

    not p_oci.Annotations[key]
    not i_oci.Annotations[key]

    print("container_annotation_missing: true")
}

allow_container_annotation(p_oci, i_oci, key) {
    print("allow_container_annotation: key =", key)

    p_value := p_oci.Annotations[key]
    i_value := i_oci.Annotations[key]
    print("allow_container_annotation: p_value =", p_value, "i_value =", i_value)

    p_value == i_value

    print("allow_container_annotation: true")
}

# "nerdctl/network-namespace" annotation
allow_sandbox_net_namespace(p_oci, i_oci) {
    print("allow_sandbox_net_namespace: start")

    key := "nerdctl/network-namespace"

    p_namespace := p_oci.Annotations[key]
    i_namespace := i_oci.Annotations[key]
    print("allow_sandbox_net_namespace: p_namespace =", p_namespace, "i_namespace =", i_namespace)

    regex.match(p_namespace, i_namespace)

    print("allow_sandbox_net_namespace: true")
}

allow_net_namespace(p_oci, i_oci) {
    print("allow_net_namespace: start")

    key := "nerdctl/network-namespace"

    not p_oci.Annotations[key]
    not i_oci.Annotations[key]

    print("allow_net_namespace: true")
}

# "io.kubernetes.cri.sandbox-log-directory" annotation
allow_sandbox_log_directory(p_oci, i_oci, s_name, s_namespace) {
    print("allow_sandbox_log_directory: start")

    key := "io.kubernetes.cri.sandbox-log-directory"

    p_dir := p_oci.Annotations[key]
    regex1 := replace(p_dir, "$(sandbox-name)", s_name)
    regex2 := replace(regex1, "$(sandbox-namespace)", s_namespace)
    print("allow_sandbox_log_directory: regex2 =", regex2)

    i_dir := i_oci.Annotations[key]
    print("allow_sandbox_log_directory: i_dir =", i_dir)

    regex.match(regex2, i_dir)

    print("allow_sandbox_log_directory: true")
}

allow_log_directory(p_oci, i_oci) {
    print("allow_log_directory: start")

    key := "io.kubernetes.cri.sandbox-log-directory"

    not p_oci.Annotations[key]
    not i_oci.Annotations[key]

    print("allow_log_directory: true")
}

allow_linux(p_oci, i_oci) {
    p_namespaces := p_oci.Linux.Namespaces
    print("allow_linux: p namespaces =", p_namespaces)

    i_namespaces := i_oci.Linux.Namespaces
    print("allow_linux: i namespaces =", i_namespaces)

    p_namespaces == i_namespaces

    allow_masked_paths(p_oci, i_oci)
    allow_readonly_paths(p_oci, i_oci)

    print("allow_linux: true")
}

allow_masked_paths(p_oci, i_oci) {
    p_paths := p_oci.Linux.MaskedPaths
    print("allow_masked_paths 1: p_paths =", p_paths)

    i_paths := i_oci.Linux.MaskedPaths
    print("allow_masked_paths 1: i_paths =", i_paths)

    allow_masked_paths_array(p_paths, i_paths)

    print("allow_masked_paths 1: true")
}
allow_masked_paths(p_oci, i_oci) {
    print("allow_masked_paths 2: start")

    not p_oci.Linux.MaskedPaths
    not i_oci.Linux.MaskedPaths

    print("allow_masked_paths 2: true")
}

# All the policy masked paths must be masked in the input data too.
# Input is allowed to have more masked paths than the policy.
allow_masked_paths_array(p_array, i_array) {
    every p_elem in p_array {
        allow_masked_path(p_elem, i_array)
    }
}

allow_masked_path(p_elem, i_array) {
    print("allow_masked_path: p_elem =", p_elem)

    some i_elem in i_array
    p_elem == i_elem

    print("allow_masked_path: true")
}

allow_readonly_paths(p_oci, i_oci) {
    p_paths := p_oci.Linux.ReadonlyPaths
    print("allow_readonly_paths 1: p_paths =", p_paths)

    i_paths := i_oci.Linux.ReadonlyPaths
    print("allow_readonly_paths 1: i_paths =", i_paths)

    allow_readonly_paths_array(p_paths, i_paths, i_oci.Linux.MaskedPaths)

    print("allow_readonly_paths 1: true")
}
allow_readonly_paths(p_oci, i_oci) {
    print("allow_readonly_paths 2: start")

    not p_oci.Linux.ReadonlyPaths
    not i_oci.Linux.ReadonlyPaths

    print("allow_readonly_paths 2: true")
}

# All the policy readonly paths must be either:
# - Present in the input readonly paths, or
# - Present in the input masked paths.
# Input is allowed to have more readonly paths than the policy.
allow_readonly_paths_array(p_array, i_array, masked_paths) {
    every p_elem in p_array {
        allow_readonly_path(p_elem, i_array, masked_paths)
    }
}

allow_readonly_path(p_elem, i_array, masked_paths) {
    print("allow_readonly_path 1: p_elem =", p_elem)

    some i_elem in i_array
    p_elem == i_elem

    print("allow_readonly_path 1: true")
}
allow_readonly_path(p_elem, i_array, masked_paths) {
    print("allow_readonly_path 2: p_elem =", p_elem)

    some i_masked in masked_paths
    p_elem == i_masked

    print("allow_readonly_path 2: true")
}

# Check the consistency of the input "io.katacontainers.pkg.oci.bundle_path"
# and io.kubernetes.cri.sandbox-id" values with other fields.
allow_by_bundle_or_sandbox_id(p_oci, i_oci, p_storages, i_storages) {
    print("allow_by_bundle_or_sandbox_id: start")

    bundle_path := i_oci.Annotations["io.katacontainers.pkg.oci.bundle_path"]
    bundle_id := replace(bundle_path, "/run/containerd/io.containerd.runtime.v2.task/k8s.io/", "")

    key := "io.kubernetes.cri.sandbox-id"

    p_regex := p_oci.Annotations[key]
    sandbox_id := i_oci.Annotations[key]

    print("allow_by_bundle_or_sandbox_id: sandbox_id =", sandbox_id, "regex =", p_regex)
    regex.match(p_regex, sandbox_id)

    allow_root_path(p_oci, i_oci, bundle_id)

    every i_mount in input.OCI.Mounts {
        allow_mount(p_oci, i_mount, bundle_id, sandbox_id)
    }

    allow_storages(p_storages, i_storages, bundle_id, sandbox_id)

    print("allow_by_bundle_or_sandbox_id: true")
}

allow_process(p_oci, i_oci, s_name) {
    p_process := p_oci.Process
    i_process := i_oci.Process

    print("allow_process: i terminal =", i_process.Terminal, "p terminal =", p_process.Terminal)
    p_process.Terminal == i_process.Terminal

    print("allow_process: i cwd =", i_process.Cwd, "i cwd =", p_process.Cwd)
    p_process.Cwd == i_process.Cwd

    print("allow_process: i noNewPrivileges =", i_process.NoNewPrivileges, "p noNewPrivileges =", p_process.NoNewPrivileges)
    p_process.NoNewPrivileges == i_process.NoNewPrivileges

    allow_caps(p_process.Capabilities, i_process.Capabilities)
    allow_user(p_process, i_process)
    allow_args(p_process, i_process, s_name)
    allow_env(p_process, i_process, s_name)

    print("allow_process: true")
}

allow_user(p_process, i_process) {
    p_user := p_process.User
    i_user := i_process.User

    print("allow_user: input uid =", i_user.UID, "policy uid =", p_user.UID)
    p_user.UID == i_user.UID

    # TODO: track down the reason for registry.k8s.io/pause:3.9 being
    #       executed with gid = 0 despite having "65535:65535" in its container image
    #       config.
    #print("allow_user: input gid =", i_user.GID, "policy gid =", p_user.GID)
    #p_user.GID == i_user.GID

    # TODO: compare the additionalGids field too after computing its value
    # based on /etc/passwd and /etc/group from the container image.
}

allow_args(p_process, i_process, s_name) {
    print("allow_args 1: no args")

    not p_process.Args
    not i_process.Args

    print("allow_args 1: true")
}
allow_args(p_process, i_process, s_name) {
    print("allow_args 2: policy args =", p_process.Args)
    print("allow_args 2: input args =", i_process.Args)

    count(p_process.Args) == count(i_process.Args)

    every i, i_arg in i_process.Args {
        allow_arg(i, i_arg, p_process, s_name)
    }

    print("allow_args 2: true")
}
allow_arg(i, i_arg, p_process, s_name) {
    p_arg := p_process.Args[i]
    print("allow_arg 1: i =", i, "i_arg =", i_arg, "p_arg =", p_arg)

    p_arg2 := replace(p_arg, "$$", "$")
    p_arg2 == i_arg

    print("allow_arg 1: true")
}
allow_arg(i, i_arg, p_process, s_name) {
    p_arg := p_process.Args[i]
    print("allow_arg 2: i =", i, "i_arg =", i_arg, "p_arg =", p_arg)

    # TODO: can $(node-name) be handled better?
    contains(p_arg, "$(node-name)")

    print("allow_arg 2: true")
}
allow_arg(i, i_arg, p_process, s_name) {
    p_arg := p_process.Args[i]
    print("allow_arg 3: i =", i, "i_arg =", i_arg, "p_arg =", p_arg)

    p_arg2 := replace(p_arg, "$$", "$")
    p_arg3 := replace(p_arg2, "$(sandbox-name)", s_name)
    print("allow_arg 3: p_arg3 =", p_arg3)
    p_arg3 == i_arg

    print("allow_arg 3: true")
}

# OCI process.Env field
allow_env(p_process, i_process, s_name) {
    print("allow_env: p env =", p_process.Env)
    print("allow_env: i env =", i_process.Env)

    every i_var in i_process.Env {
        print("allow_env: i_var =", i_var)
        allow_var(p_process, i_process, i_var, s_name)
    }

    print("allow_env: true")
}

# Allow input env variables that are present in the policy data too.
allow_var(p_process, i_process, i_var, s_name) {
    some p_var in p_process.Env
    p_var == i_var
    print("allow_var 1: true")
}

# Match input with one of the policy variables, after substituting $(sandbox-name).
allow_var(p_process, i_process, i_var, s_name) {
    some p_var in p_process.Env
    p_var2 := replace(p_var, "$(sandbox-name)", s_name)

    print("allow_var 2: p_var2 =", p_var2)
    p_var2 == i_var

    print("allow_var 2: true")
}

# Allow input env variables that match with a request_defaults regex.
allow_var(p_process, i_process, i_var, s_name) {
    some p_regex1 in policy_data.request_defaults.CreateContainerRequest.allow_env_regex
    p_regex2 := replace(p_regex1, "$(ipv4_a)", policy_data.common.ipv4_a)
    p_regex3 := replace(p_regex2, "$(ip_p)", policy_data.common.ip_p)
    p_regex4 := replace(p_regex3, "$(svc_name)", policy_data.common.svc_name)
    p_regex5 := replace(p_regex4, "$(dns_label)", policy_data.common.dns_label)

    print("allow_var 3: p_regex5 =", p_regex5)
    regex.match(p_regex5, i_var)

    print("allow_var 3: true")
}

# Allow fieldRef "fieldPath: status.podIP" values.
allow_var(p_process, i_process, i_var, s_name) {
    name_value := split(i_var, "=")
    count(name_value) == 2
    is_ip(name_value[1])

    some p_var in p_process.Env
    allow_pod_ip_var(name_value[0], p_var)

    print("allow_var 4: true")
}

# Allow common fieldRef variables.
allow_var(p_process, i_process, i_var, s_name) {
    name_value := split(i_var, "=")
    count(name_value) == 2

    some p_var in p_process.Env
    p_name_value := split(p_var, "=")
    count(p_name_value) == 2

    p_name_value[0] == name_value[0]

    # TODO: should these be handled in a different way?
    always_allowed := ["$(host-name)", "$(node-name)", "$(pod-uid)"]
    some allowed in always_allowed
    contains(p_name_value[1], allowed)

    print("allow_var 5: true")
}

# Allow fieldRef "fieldPath: status.hostIP" values.
allow_var(p_process, i_process, i_var, s_name) {
    name_value := split(i_var, "=")
    count(name_value) == 2
    is_ip(name_value[1])

    some p_var in p_process.Env
    allow_host_ip_var(name_value[0], p_var)

    print("allow_var 6: true")
}

# Allow resourceFieldRef values (e.g., "limits.cpu").
allow_var(p_process, i_process, i_var, s_name) {
    name_value := split(i_var, "=")
    count(name_value) == 2

    some p_var in p_process.Env
    p_name_value := split(p_var, "=")
    count(p_name_value) == 2

    p_name_value[0] == name_value[0]

    # TODO: should these be handled in a different way?
    always_allowed = ["$(resource-field)", "$(todo-annotation)"]
    some allowed in always_allowed
    contains(p_name_value[1], allowed)

    print("allow_var 7: true")
}

allow_pod_ip_var(var_name, p_var) {
    print("allow_pod_ip_var: var_name =", var_name, "p_var =", p_var)

    p_name_value := split(p_var, "=")
    count(p_name_value) == 2

    p_name_value[0] == var_name
    p_name_value[1] == "$(pod-ip)"

    print("allow_pod_ip_var: true")
}

allow_host_ip_var(var_name, p_var) {
    print("allow_host_ip_var: var_name =", var_name, "p_var =", p_var)

    p_name_value := split(p_var, "=")
    count(p_name_value) == 2

    p_name_value[0] == var_name
    p_name_value[1] == "$(host-ip)"

    print("allow_host_ip_var: true")
}

is_ip(value) {
    bytes = split(value, ".")
    count(bytes) == 4

    is_ip_first_byte(bytes[0])
    is_ip_other_byte(bytes[1])
    is_ip_other_byte(bytes[2])
    is_ip_other_byte(bytes[3])
}
is_ip_first_byte(component) {
    number = to_number(component)
    number >= 1
    number <= 255
}
is_ip_other_byte(component) {
    number = to_number(component)
    number >= 0
    number <= 255
}

# OCI root.Path
allow_root_path(p_oci, i_oci, bundle_id) {
    i_path := i_oci.Root.Path
    p_path1 := p_oci.Root.Path
    print("allow_root_path: i_path =", i_path, "p_path1 =", p_path1)

    p_path2 := replace(p_path1, "$(cpath)", policy_data.common.cpath)
    print("allow_root_path: p_path2 =", p_path2)

    p_path3 := replace(p_path2, "$(bundle-id)", bundle_id)
    print("allow_root_path: p_path3 =", p_path3)

    p_path3 == i_path

    print("allow_root_path: true")
}

# device mounts
allow_mount(p_oci, i_mount, bundle_id, sandbox_id) {
    print("allow_mount: i_mount =", i_mount)

    some p_mount in p_oci.Mounts
    print("allow_mount: p_mount =", p_mount)
    check_mount(p_mount, i_mount, bundle_id, sandbox_id)

    # TODO: are there any other required policy checks for mounts - e.g.,
    #       multiple mounts with same source or destination?

    print("allow_mount: true")
}

check_mount(p_mount, i_mount, bundle_id, sandbox_id) {
    p_mount == i_mount
    print("check_mount 1: true")
}
check_mount(p_mount, i_mount, bundle_id, sandbox_id) {
    p_mount.destination == i_mount.destination
    p_mount.type_ == i_mount.type_
    p_mount.options == i_mount.options

    mount_source_allows(p_mount, i_mount, bundle_id, sandbox_id)

    print("check_mount 2: true")
}

mount_source_allows(p_mount, i_mount, bundle_id, sandbox_id) {
    regex1 := p_mount.source
    regex2 := replace(regex1, "$(sfprefix)", policy_data.common.sfprefix)
    regex3 := replace(regex2, "$(cpath)", policy_data.common.cpath)
    regex4 := replace(regex3, "$(bundle-id)", bundle_id)

    print("mount_source_allows 1: regex4 =", regex4)
    regex.match(regex4, i_mount.source)

    print("mount_source_allows 1: true")
}
mount_source_allows(p_mount, i_mount, bundle_id, sandbox_id) {
    regex1 := p_mount.source
    regex2 := replace(regex1, "$(sfprefix)", policy_data.common.sfprefix)
    regex3 := replace(regex2, "$(cpath)", policy_data.common.cpath)
    regex4 := replace(regex3, "$(sandbox-id)", sandbox_id)

    print("mount_source_allows 2: regex4 =", regex4)
    regex.match(regex4, i_mount.source)

    print("mount_source_allows 2: true")
}
mount_source_allows(p_mount, i_mount, bundle_id, sandbox_id) {
    print("mount_source_allows 3: i_mount.source=", i_mount.source)

    i_source_parts = split(i_mount.source, "/")
    b64_direct_vol_path = i_source_parts[count(i_source_parts) - 1]

    base64.is_valid(b64_direct_vol_path)

    source1 := p_mount.source
    print("mount_source_allows 3: source1 =", source1)

    source2 := replace(source1, "$(spath)", policy_data.common.spath)
    print("mount_source_allows 3: source2 =", source2)

    source3 := replace(source2, "$(b64-direct-vol-path)", b64_direct_vol_path)
    print("mount_source_allows 3: source3 =", source3)

    source3 == i_mount.source

    print("mount_source_allows 3: true")
}

######################################################################
# Create container Storages

allow_storages(p_storages, i_storages, bundle_id, sandbox_id) {
    p_count := count(p_storages)
    i_count := count(i_storages)
    print("allow_storages: p_count =", p_count, "i_count =", i_count)

    p_count == i_count

    # Get the container image layer IDs and verity root hashes, from the "overlayfs" storage.
    some overlay_storage in p_storages
    overlay_storage.driver == "overlayfs"
    print("allow_storages: overlay_storage =", overlay_storage)
    count(overlay_storage.options) == 2

    layer_ids := split(overlay_storage.options[0], ":")
    print("allow_storages: layer_ids =", layer_ids)

    root_hashes := split(overlay_storage.options[1], ":")
    print("allow_storages: root_hashes =", root_hashes)

    every i_storage in i_storages {
        allow_storage(p_storages, i_storage, bundle_id, sandbox_id, layer_ids, root_hashes)
    }

    print("allow_storages: true")
}

allow_storage(p_storages, i_storage, bundle_id, sandbox_id, layer_ids, root_hashes) {
    some p_storage in p_storages

    print("allow_storage: p_storage =", p_storage)
    print("allow_storage: i_storage =", i_storage)

    p_storage.driver           == i_storage.driver
    p_storage.driver_options   == i_storage.driver_options
    p_storage.fs_group         == i_storage.fs_group

    allow_storage_options(p_storage, i_storage, layer_ids, root_hashes)
    allow_mount_point(p_storage, i_storage, bundle_id, sandbox_id, layer_ids)

    # TODO: validate the source field too.

    print("allow_storage: true")
}

allow_storage_options(p_storage, i_storage, layer_ids, root_hashes) {
    print("allow_storage_options 1: start")

    p_storage.driver != "overlayfs"
    p_storage.options == i_storage.options

    print("allow_storage_options 1: true")
}
allow_storage_options(p_storage, i_storage, layer_ids, root_hashes) {
    print("allow_storage_options 2: start")

    p_storage.driver == "overlayfs"
    count(p_storage.options) == 2

    policy_ids := split(p_storage.options[0], ":")
    print("allow_storage_options 2: policy_ids =", policy_ids)
    policy_ids == layer_ids

    policy_hashes := split(p_storage.options[1], ":")
    print("allow_storage_options 2: policy_hashes =", policy_hashes)

    p_count := count(policy_ids)
    print("allow_storage_options 2: p_count =", p_count)
    p_count >= 1
    p_count == count(policy_hashes)

    i_count := count(i_storage.options)
    print("allow_storage_options 2: i_count =", i_count)
    i_count == p_count + 3

    print("allow_storage_options 2: i_storage.options[0] =", i_storage.options[0])
    i_storage.options[0] == "io.katacontainers.fs-opt.layer-src-prefix=/var/lib/containerd/io.containerd.snapshotter.v1.tardev/layers"

    print("allow_storage_options 2: i_storage.options[i_count - 2] =", i_storage.options[i_count - 2])
    i_storage.options[i_count - 2] == "io.katacontainers.fs-opt.overlay-rw"

    lowerdir := concat("=", ["lowerdir", p_storage.options[0]])
    print("allow_storage_options 2: lowerdir =", lowerdir)

    print("allow_storage_options 2: i_storage.options[i_count - 1] =", i_storage.options[i_count - 1])
    i_storage.options[i_count - 1] == lowerdir

    every i, policy_id in policy_ids {
        allow_overlay_layer(policy_id, policy_hashes[i], i_storage.options[i + 1])
    }

    print("allow_storage_options 2: true")
}
allow_storage_options(p_storage, i_storage, layer_ids, root_hashes) {
    print("allow_storage_options 3: start")

    p_storage.driver == "blk"
    count(p_storage.options) == 1

    startswith(p_storage.options[0], "$(hash")
    hash_suffix := trim_left(p_storage.options[0], "$(hash")

    endswith(hash_suffix, ")")
    hash_index := trim_right(hash_suffix, ")")
    i := to_number(hash_index)
    print("allow_storage_options 3: i =", i)

    hash_option := concat("=", ["io.katacontainers.fs-opt.root-hash", root_hashes[i]])
    print("allow_storage_options 3: hash_option =", hash_option)

    count(i_storage.options) == 4
    i_storage.options[0] == "ro"
    i_storage.options[1] == "io.katacontainers.fs-opt.block_device=file"
    i_storage.options[2] == "io.katacontainers.fs-opt.is-layer"
    i_storage.options[3] == hash_option

    print("allow_storage_options 3: true")
}
allow_storage_options(p_storage, i_storage, layer_ids, root_hashes) {
    print("allow_storage_options 4: start")

    p_storage.driver == "smb"
    count(i_storage.options) == 8
    i_storage.options[0] == "dir_mode=0666"
    i_storage.options[1] == "file_mode=0666"
    i_storage.options[2] == "mfsymlinks"    
    i_storage.options[3] == "cache=strict"  
    i_storage.options[4] == "nosharesock"
    i_storage.options[5] == "actimeo=30"    
    startswith(i_storage.options[6], "addr=")
    creds = split(i_storage.options[7], ",")
    count(creds) == 2
    startswith(creds[0], "username=")
    startswith(creds[1], "password=")
    
    print("allow_storage_options 4: true")
}

allow_overlay_layer(policy_id, policy_hash, i_option) {
    print("allow_overlay_layer: policy_id =", policy_id, "policy_hash =", policy_hash)
    print("allow_overlay_layer: i_option =", i_option)

    startswith(i_option, "io.katacontainers.fs-opt.layer=")
    i_value := replace(i_option, "io.katacontainers.fs-opt.layer=", "")
    i_value_decoded := base64.decode(i_value)
    print("allow_overlay_layer: i_value_decoded =", i_value_decoded)

    policy_suffix := concat("=", ["tar,ro,io.katacontainers.fs-opt.block_device=file,io.katacontainers.fs-opt.is-layer,io.katacontainers.fs-opt.root-hash", policy_hash])
    p_value := concat(",", [policy_id, policy_suffix])
    print("allow_overlay_layer: p_value =", p_value)

    p_value == i_value_decoded

    print("allow_overlay_layer: true")
}

allow_mount_point(p_storage, i_storage, bundle_id, sandbox_id, layer_ids) {
    p_storage.fstype == "tar"

    startswith(p_storage.mount_point, "$(layer")
    mount_suffix := trim_left(p_storage.mount_point, "$(layer")

    endswith(mount_suffix, ")")
    layer_index := trim_right(mount_suffix, ")")
    i := to_number(layer_index)
    print("allow_mount_point 1: i =", i)

    layer_id := layer_ids[i]
    print("allow_mount_point 1: layer_id =", layer_id)

    p_mount := concat("/", ["/run/kata-containers/sandbox/layers", layer_id])
    print("allow_mount_point 1: p_mount =", p_mount)

    p_mount == i_storage.mount_point

    print("allow_mount_point 1: true")
}
allow_mount_point(p_storage, i_storage, bundle_id, sandbox_id, layer_ids) {
    p_storage.fstype == "fuse3.kata-overlay"

    mount1 := replace(p_storage.mount_point, "$(cpath)", policy_data.common.cpath)
    mount2 := replace(mount1, "$(bundle-id)", bundle_id)
    print("allow_mount_point 2: mount2 =", mount2)

    mount2 == i_storage.mount_point

    print("allow_mount_point 2: true")
}
allow_mount_point(p_storage, i_storage, bundle_id, sandbox_id, layer_ids) {
    p_storage.fstype == "local"

    mount1 := p_storage.mount_point
    print("allow_mount_point 3: mount1 =", mount1)

    mount2 := replace(mount1, "$(cpath)", policy_data.common.cpath)
    print("allow_mount_point 3: mount2 =", mount2)

    mount3 := replace(mount2, "$(sandbox-id)", sandbox_id)
    print("allow_mount_point 3: mount3 =", mount3)

    regex.match(mount3, i_storage.mount_point)

    print("allow_mount_point 3: true")
}
allow_mount_point(p_storage, i_storage, bundle_id, sandbox_id, layer_ids) {
    p_storage.fstype == "bind"

    mount1 := p_storage.mount_point
    print("allow_mount_point 4: mount1 =", mount1)

    mount2 := replace(mount1, "$(cpath)", policy_data.common.cpath)
    print("allow_mount_point 4: mount2 =", mount2)

    mount3 := replace(mount2, "$(bundle-id)", bundle_id)
    print("allow_mount_point 4: mount3 =", mount3)

    regex.match(mount3, i_storage.mount_point)

    print("allow_mount_point 4: true")
}
allow_mount_point(p_storage, i_storage, bundle_id, sandbox_id, layer_ids) {
    p_storage.fstype == "tmpfs"

    mount1 := p_storage.mount_point
    print("allow_mount_point 5: mount1 =", mount1)

    regex.match(mount1, i_storage.mount_point)

    print("allow_mount_point 5: true")
}
allow_mount_point(p_storage, i_storage, bundle_id, sandbox_id, layer_ids) {
    print("allow_mount_point 6: i_storage.mount_point =", i_storage.mount_point)
    allow_direct_vol_driver(p_storage, i_storage)

    mount1 := p_storage.mount_point
    print("allow_mount_point 6: mount1 =", mount1)

    mount2 := replace(mount1, "$(spath)", policy_data.common.spath)
    print("allow_mount_point 6: mount2 =", mount2)

    direct_vol_path := i_storage.source
    mount3 := replace(mount2, "$(b64-direct-vol-path)", base64url.encode(direct_vol_path))
    print("allow_mount_point 6: mount3 =", mount3)

    mount3 == i_storage.mount_point

    print("allow_mount_point 6: true")
}

allow_direct_vol_driver(p_storage, i_storage) {
    print("allow_direct_vol_driver 1: start")
    p_storage.driver == "blk"
    print("allow_direct_vol_driver 1: true")
}
allow_direct_vol_driver(p_storage, i_storage) {
    print("allow_direct_vol_driver 2: start")
    p_storage.driver == "smb"
    print("allow_direct_vol_driver 2: true")
}

# process.Capabilities
allow_caps(p_caps, i_caps) {
    print("allow_caps: policy Ambient =", p_caps.Ambient)
    print("allow_caps: input Ambient =", i_caps.Ambient)
    match_caps(p_caps.Ambient, i_caps.Ambient)

    print("allow_caps: policy Bounding =", p_caps.Bounding)
    print("allow_caps: input Bounding =", i_caps.Bounding)
    match_caps(p_caps.Bounding, i_caps.Bounding)

    print("allow_caps: policy Effective =", p_caps.Effective)
    print("allow_caps: input Effective =", i_caps.Effective)
    match_caps(p_caps.Effective, i_caps.Effective)

    print("allow_caps: policy Inheritable =", p_caps.Inheritable)
    print("allow_caps: input Inheritable =", i_caps.Inheritable)
    match_caps(p_caps.Inheritable, i_caps.Inheritable)

    print("allow_caps: policy Permitted =", p_caps.Permitted)
    print("allow_caps: input Permitted =", i_caps.Permitted)
    match_caps(p_caps.Permitted, i_caps.Permitted)
}

match_caps(p_caps, i_caps) {
    print("match_caps 1: start")

    p_caps == i_caps

    print("match_caps 1: true")
}
match_caps(p_caps, i_caps) {
    print("match_caps 2: start")

    count(p_caps) == 1
    p_caps[0] == "$(default_caps)"

    print("match_caps 2: default_caps =", policy_data.common.default_caps)
    policy_data.common.default_caps == i_caps

    print("match_caps 2: true")
}
match_caps(p_caps, i_caps) {
    print("match_caps 3: start")

    count(p_caps) == 1
    p_caps[0] == "$(privileged_caps)"

    print("match_caps 3: privileged_caps =", policy_data.common.privileged_caps)
    policy_data.common.privileged_caps == i_caps

    print("match_caps 3: true")
}

######################################################################
check_directory_traversal(i_path) {
    contains(i_path, "../") == false
    endswith(i_path, "/..") == false
    i_path != ".."
}

check_symlink_source {
    # TODO: delete this rule once the symlink_src field gets implemented
    # by all/most Guest VMs.
    not input.symlink_src
}
check_symlink_source {
    i_src := input.symlink_src
    print("check_symlink_source: i_src =", i_src)

    startswith(i_src, "/") == false
    check_directory_traversal(i_src)
}

allow_sandbox_storages(i_storages) {
    print("allow_sandbox_storages: i_storages =", i_storages)

    p_storages := policy_data.sandbox.storages
    every i_storage in i_storages {
        allow_sandbox_storage(p_storages, i_storage)
    }

    print("allow_sandbox_storages: true")
}

allow_sandbox_storage(p_storages, i_storage) {
    print("allow_sandbox_storage: i_storage =", i_storage)

    some p_storage in p_storages
    print("allow_sandbox_storage: p_storage =", p_storage)
    i_storage == p_storage

    print("allow_sandbox_storage: true")
}

CopyFileRequest {
    print("CopyFileRequest: input.path =", input.path)

    check_symlink_source
    check_directory_traversal(input.path)

    some regex1 in policy_data.request_defaults.CopyFileRequest
    regex2 := replace(regex1, "$(sfprefix)", policy_data.common.sfprefix)
    regex3 := replace(regex2, "$(cpath)", policy_data.common.cpath)
    regex4 := replace(regex3, "$(bundle-id)", "[a-z0-9]{64}")
    print("CopyFileRequest: regex4 =", regex4)

    regex.match(regex4, input.path)

    print("CopyFileRequest: true")
}

CreateSandboxRequest {
    print("CreateSandboxRequest: input.guest_hook_path =", input.guest_hook_path)
    count(input.guest_hook_path) == 0

    print("CreateSandboxRequest: input.kernel_modules =", input.kernel_modules)
    count(input.kernel_modules) == 0

    i_pidns := input.sandbox_pidns
    print("CreateSandboxRequest: i_pidns =", i_pidns)
    i_pidns == false

    allow_sandbox_storages(input.storages)
}

ExecProcessRequest {
    print("ExecProcessRequest 1: input =", input)

    i_command = concat(" ", input.process.Args)
    print("ExecProcessRequest 1: i_command =", i_command)

    some p_command in policy_data.request_defaults.ExecProcessRequest.commands
    print("ExecProcessRequest 1: p_command =", p_command)
    p_command == i_command

    print("ExecProcessRequest 1: true")
}
ExecProcessRequest {
    print("ExecProcessRequest 2: input =", input)

    # TODO: match input container ID with its corresponding container.exec_commands.
    i_command = concat(" ", input.process.Args)
    print("ExecProcessRequest 3: i_command =", i_command)

    some container in policy_data.containers
    some p_command in container.exec_commands
    print("ExecProcessRequest 2: p_command =", p_command)

    # TODO: should other input data fields be validated as well?
    p_command == i_command

    print("ExecProcessRequest 2: true")
}
ExecProcessRequest {
    print("ExecProcessRequest 3: input =", input)

    i_command = concat(" ", input.process.Args)
    print("ExecProcessRequest 3: i_command =", i_command)

    some p_regex in policy_data.request_defaults.ExecProcessRequest.regex
    print("ExecProcessRequest 3: p_regex =", p_regex)

    regex.match(p_regex, i_command)

    print("ExecProcessRequest 3: true")
}

CloseStdinRequest {
    policy_data.request_defaults.CloseStdinRequest == true
}

ReadStreamRequest {
    policy_data.request_defaults.ReadStreamRequest == true
}

UpdateEphemeralMountsRequest {
    policy_data.request_defaults.UpdateEphemeralMountsRequest == true
}

WriteStreamRequest {
    policy_data.request_defaults.WriteStreamRequest == true
}

policy_data := {
  "containers": [
    {
      "OCI": {
        "Version": "1.1.0-rc.1",
        "Process": {
          "Terminal": false,
          "User": {
            "UID": 65535,
            "GID": 65535,
            "AdditionalGids": [],
            "Username": ""
          },
          "Args": [
            "/pause"
          ],
          "Env": [
            "PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"
          ],
          "Cwd": "/",
          "Capabilities": {
            "Ambient": [],
            "Bounding": [
              "$(default_caps)"
            ],
            "Effective": [
              "$(default_caps)"
            ],
            "Inheritable": [],
            "Permitted": [
              "$(default_caps)"
            ]
          },
          "NoNewPrivileges": true
        },
        "Root": {
          "Path": "$(cpath)/$(bundle-id)",
          "Readonly": true
        },
        "Mounts": [
          {
            "destination": "/proc",
            "source": "proc",
            "type_": "proc",
            "options": [
              "nosuid",
              "noexec",
              "nodev"
            ]
          },
          {
            "destination": "/dev",
            "source": "tmpfs",
            "type_": "tmpfs",
            "options": [
              "nosuid",
              "strictatime",
              "mode=755",
              "size=65536k"
            ]
          },
          {
            "destination": "/dev/pts",
            "source": "devpts",
            "type_": "devpts",
            "options": [
              "nosuid",
              "noexec",
              "newinstance",
              "ptmxmode=0666",
              "mode=0620",
              "gid=5"
            ]
          },
          {
            "destination": "/dev/shm",
            "source": "/run/kata-containers/sandbox/shm",
            "type_": "bind",
            "options": [
              "rbind"
            ]
          },
          {
            "destination": "/dev/mqueue",
            "source": "mqueue",
            "type_": "mqueue",
            "options": [
              "nosuid",
              "noexec",
              "nodev"
            ]
          },
          {
            "destination": "/sys",
            "source": "sysfs",
            "type_": "sysfs",
            "options": [
              "nosuid",
              "noexec",
              "nodev",
              "ro"
            ]
          },
          {
            "destination": "/etc/resolv.conf",
            "source": "$(sfprefix)resolv.conf$",
            "type_": "bind",
            "options": [
              "rbind",
              "ro",
              "nosuid",
              "nodev",
              "noexec"
            ]
          }
        ],
        "Annotations": {
          "io.katacontainers.pkg.oci.bundle_path": "/run/containerd/io.containerd.runtime.v2.task/k8s.io/$(bundle-id)",
          "io.katacontainers.pkg.oci.container_type": "pod_sandbox",
          "io.kubernetes.cri.container-type": "sandbox",
          "io.kubernetes.cri.sandbox-id": "^[a-z0-9]{64}$",
          "io.kubernetes.cri.sandbox-log-directory": "^/var/log/pods/$(sandbox-namespace)_$(sandbox-name)_[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$",
          "io.kubernetes.cri.sandbox-name": "dns-test-f880e73f-1718-4455-9a78-766679e22471",
          "io.kubernetes.cri.sandbox-namespace": "dns-9988",
          "nerdctl/network-namespace": "^/var/run/netns/cni-[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$"
        },
        "Linux": {
          "Namespaces": [
            {
              "Type": "ipc",
              "Path": ""
            },
            {
              "Type": "uts",
              "Path": ""
            },
            {
              "Type": "mount",
              "Path": ""
            }
          ],
          "MaskedPaths": [
            "/proc/acpi",
            "/proc/asound",
            "/proc/kcore",
            "/proc/keys",
            "/proc/latency_stats",
            "/proc/timer_list",
            "/proc/timer_stats",
            "/proc/sched_debug",
            "/sys/firmware",
            "/proc/scsi"
          ],
          "ReadonlyPaths": [
            "/proc/bus",
            "/proc/fs",
            "/proc/irq",
            "/proc/sys",
            "/proc/sysrq-trigger"
          ]
        }
      },
      "storages": [
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash0)"
          ],
          "mount_point": "$(layer0)",
          "fs_group": null
        },
        {
          "driver": "overlayfs",
          "driver_options": [],
          "source": "",
          "fstype": "fuse3.kata-overlay",
          "options": [
            "5a5aad80055ff20012a50dc25f8df7a29924474324d65f7d5306ee8ee27ff71d",
            "817250f1a3e336da76f5bd3fa784e1b26d959b9c131876815ba2604048b70c18"
          ],
          "mount_point": "$(cpath)/$(bundle-id)",
          "fs_group": null
        }
      ],
      "sandbox_pidns": false,
      "exec_commands": []
    },
    {
      "OCI": {
        "Version": "1.1.0-rc.1",
        "Process": {
          "Terminal": false,
          "User": {
            "UID": 0,
            "GID": 0,
            "AdditionalGids": [],
            "Username": ""
          },
          "Args": [
            "/agnhost",
            "test-webserver"
          ],
          "Env": [
            "PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
            "HOSTNAME=$(host-name)"
          ],
          "Cwd": "/",
          "Capabilities": {
            "Ambient": [],
            "Bounding": [
              "$(default_caps)"
            ],
            "Effective": [
              "$(default_caps)"
            ],
            "Inheritable": [],
            "Permitted": [
              "$(default_caps)"
            ]
          },
          "NoNewPrivileges": false
        },
        "Root": {
          "Path": "$(cpath)/$(bundle-id)",
          "Readonly": false
        },
        "Mounts": [
          {
            "destination": "/proc",
            "source": "proc",
            "type_": "proc",
            "options": [
              "nosuid",
              "noexec",
              "nodev"
            ]
          },
          {
            "destination": "/dev",
            "source": "tmpfs",
            "type_": "tmpfs",
            "options": [
              "nosuid",
              "strictatime",
              "mode=755",
              "size=65536k"
            ]
          },
          {
            "destination": "/dev/pts",
            "source": "devpts",
            "type_": "devpts",
            "options": [
              "nosuid",
              "noexec",
              "newinstance",
              "ptmxmode=0666",
              "mode=0620",
              "gid=5"
            ]
          },
          {
            "destination": "/dev/shm",
            "source": "/run/kata-containers/sandbox/shm",
            "type_": "bind",
            "options": [
              "rbind"
            ]
          },
          {
            "destination": "/dev/mqueue",
            "source": "mqueue",
            "type_": "mqueue",
            "options": [
              "nosuid",
              "noexec",
              "nodev"
            ]
          },
          {
            "destination": "/sys",
            "source": "sysfs",
            "type_": "sysfs",
            "options": [
              "nosuid",
              "noexec",
              "nodev",
              "ro"
            ]
          },
          {
            "destination": "/sys/fs/cgroup",
            "source": "cgroup",
            "type_": "cgroup",
            "options": [
              "nosuid",
              "noexec",
              "nodev",
              "relatime",
              "ro"
            ]
          },
          {
            "destination": "/etc/hosts",
            "source": "$(sfprefix)hosts$",
            "type_": "bind",
            "options": [
              "rbind",
              "rprivate",
              "rw"
            ]
          },
          {
            "destination": "/dev/termination-log",
            "source": "$(sfprefix)termination-log$",
            "type_": "bind",
            "options": [
              "rbind",
              "rprivate",
              "rw"
            ]
          },
          {
            "destination": "/etc/hostname",
            "source": "$(sfprefix)hostname$",
            "type_": "bind",
            "options": [
              "rbind",
              "rprivate",
              "rw"
            ]
          },
          {
            "destination": "/etc/resolv.conf",
            "source": "$(sfprefix)resolv.conf$",
            "type_": "bind",
            "options": [
              "rbind",
              "rprivate",
              "rw"
            ]
          },
          {
            "destination": "/var/run/secrets/kubernetes.io/serviceaccount",
            "source": "$(sfprefix)serviceaccount$",
            "type_": "bind",
            "options": [
              "rbind",
              "rprivate",
              "ro"
            ]
          },
          {
            "destination": "/var/run/secrets/azure/tokens",
            "source": "$(sfprefix)tokens$",
            "type_": "bind",
            "options": [
              "rbind",
              "rprivate",
              "ro"
            ]
          },
          {
            "destination": "/results",
            "source": "^$(cpath)/$(sandbox-id)/local/results$",
            "type_": "local",
            "options": [
              "rbind",
              "rprivate",
              "rw"
            ]
          }
        ],
        "Annotations": {
          "io.katacontainers.pkg.oci.bundle_path": "/run/containerd/io.containerd.runtime.v2.task/k8s.io/$(bundle-id)",
          "io.katacontainers.pkg.oci.container_type": "pod_container",
          "io.kubernetes.cri.container-name": "webserver",
          "io.kubernetes.cri.container-type": "container",
          "io.kubernetes.cri.image-name": "registry.k8s.io/e2e-test-images/agnhost:2.43",
          "io.kubernetes.cri.sandbox-id": "^[a-z0-9]{64}$",
          "io.kubernetes.cri.sandbox-name": "dns-test-f880e73f-1718-4455-9a78-766679e22471",
          "io.kubernetes.cri.sandbox-namespace": "dns-9988"
        },
        "Linux": {
          "Namespaces": [
            {
              "Type": "ipc",
              "Path": ""
            },
            {
              "Type": "uts",
              "Path": ""
            },
            {
              "Type": "mount",
              "Path": ""
            }
          ],
          "MaskedPaths": [
            "/proc/acpi",
            "/proc/kcore",
            "/proc/keys",
            "/proc/latency_stats",
            "/proc/timer_list",
            "/proc/timer_stats",
            "/proc/sched_debug",
            "/proc/scsi",
            "/sys/firmware"
          ],
          "ReadonlyPaths": [
            "/proc/asound",
            "/proc/bus",
            "/proc/fs",
            "/proc/irq",
            "/proc/sys",
            "/proc/sysrq-trigger"
          ]
        }
      },
      "storages": [
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash0)"
          ],
          "mount_point": "$(layer0)",
          "fs_group": null
        },
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash1)"
          ],
          "mount_point": "$(layer1)",
          "fs_group": null
        },
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash2)"
          ],
          "mount_point": "$(layer2)",
          "fs_group": null
        },
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash3)"
          ],
          "mount_point": "$(layer3)",
          "fs_group": null
        },
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash4)"
          ],
          "mount_point": "$(layer4)",
          "fs_group": null
        },
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash5)"
          ],
          "mount_point": "$(layer5)",
          "fs_group": null
        },
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash6)"
          ],
          "mount_point": "$(layer6)",
          "fs_group": null
        },
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash7)"
          ],
          "mount_point": "$(layer7)",
          "fs_group": null
        },
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash8)"
          ],
          "mount_point": "$(layer8)",
          "fs_group": null
        },
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash9)"
          ],
          "mount_point": "$(layer9)",
          "fs_group": null
        },
        {
          "driver": "overlayfs",
          "driver_options": [],
          "source": "",
          "fstype": "fuse3.kata-overlay",
          "options": [
            "51f1d5df9e5b64632779c996a3abb9b32cc69c76e0c17620ed6ceff15d3f281a:bf4d0147f3abea55550a8a612bdc1144b96966d520c267e15516d5157cb39bab:b1bb57a3e5d062f9a3de4fe1c2ad2328233a6817aa04bb28f83b86d81452af5b:daed717ef210067422c927c4edf220c433a8070cd7f0ac09c45079da2475c4f3:e1f6979b86c8eae10c68c19f3b05032dfab1d770182729adb3d808c70f7b9f7f:1535f78a07d52405ad7317cbfcedf04d600de40b17e31f5ab2556611004a5b5a:1918a052ffd206e459a2adb71cabebef00ccf744c22da64a8d8a94e093d6803b:207ea00b5dad0445a6c465826f2fb5713bb4dcca369531e2a7f595f537395596:9500e46617fb4582824921ce21f55aeaa95a319bb34ebfc119042bde19996edb:da5980a7e3434409da1232417a1d1cc02967b62a099502cacd13cc2e34206fa4",
            "ece5ef216c40047accf38d3a8b16899d13b2712067dd478a2178378ec7fcbfc6:17a838b0234782eb7f6bcaa0fb28bef9f630268d2e12c3b28022dabf1cdba812:9310f4b7c8d730be055096fb9e0dbb79649b02d097837d6609f92097ab808194:1a64471f3e96306020f55f8cf17ab69bc260370dfccf32620042ff2c606767fb:f4d2b244842f05f4b1be77069461ebdce73945d430b05f49af9c540a7ad6fee1:a71f00d258abee410ba922b4b54c30d7ea8dcdc05ae345e35ceb1e8a7fb0fdb9:215a7eb0b4ad484d599f945a5afb3700818cbcf79787c5931cb33e0bd2fa8df5:b11ec2290597597135a91df848128747ba768ad3fcaf0bb750b29216e2e3c2d1:9f1a82445901154cf99ed76e2b00797afafbe2b14136151aa0a7dea56a5c9f63:254c5314873c27a8de3db5347f56ebd9eb2bf46cc8812a43611f98e38ac37ba2"
          ],
          "mount_point": "$(cpath)/$(bundle-id)",
          "fs_group": null
        },
        {
          "driver": "local",
          "driver_options": [],
          "source": "local",
          "fstype": "local",
          "options": [
            "mode=0777"
          ],
          "mount_point": "^$(cpath)/$(sandbox-id)/local/results$",
          "fs_group": null
        }
      ],
      "sandbox_pidns": false,
      "exec_commands": []
    },
    {
      "OCI": {
        "Version": "1.1.0-rc.1",
        "Process": {
          "Terminal": false,
          "User": {
            "UID": 0,
            "GID": 0,
            "AdditionalGids": [],
            "Username": ""
          },
          "Args": [
            "sh",
            "-c",
            "for i in `seq 1 600`; do check=\"$$(dig +notcp +noall +answer +search kubernetes.default.svc.cluster.local A)\" && test -n \"$$check\" && echo OK > /results/wheezy_udp@kubernetes.default.svc.cluster.local;check=\"$$(dig +tcp +noall +answer +search kubernetes.default.svc.cluster.local A)\" && test -n \"$$check\" && echo OK > /results/wheezy_tcp@kubernetes.default.svc.cluster.local;sleep 1; done"
          ],
          "Env": [
            "PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
            "HOSTNAME=$(host-name)"
          ],
          "Cwd": "/",
          "Capabilities": {
            "Ambient": [],
            "Bounding": [
              "$(default_caps)"
            ],
            "Effective": [
              "$(default_caps)"
            ],
            "Inheritable": [],
            "Permitted": [
              "$(default_caps)"
            ]
          },
          "NoNewPrivileges": false
        },
        "Root": {
          "Path": "$(cpath)/$(bundle-id)",
          "Readonly": false
        },
        "Mounts": [
          {
            "destination": "/proc",
            "source": "proc",
            "type_": "proc",
            "options": [
              "nosuid",
              "noexec",
              "nodev"
            ]
          },
          {
            "destination": "/dev",
            "source": "tmpfs",
            "type_": "tmpfs",
            "options": [
              "nosuid",
              "strictatime",
              "mode=755",
              "size=65536k"
            ]
          },
          {
            "destination": "/dev/pts",
            "source": "devpts",
            "type_": "devpts",
            "options": [
              "nosuid",
              "noexec",
              "newinstance",
              "ptmxmode=0666",
              "mode=0620",
              "gid=5"
            ]
          },
          {
            "destination": "/dev/shm",
            "source": "/run/kata-containers/sandbox/shm",
            "type_": "bind",
            "options": [
              "rbind"
            ]
          },
          {
            "destination": "/dev/mqueue",
            "source": "mqueue",
            "type_": "mqueue",
            "options": [
              "nosuid",
              "noexec",
              "nodev"
            ]
          },
          {
            "destination": "/sys",
            "source": "sysfs",
            "type_": "sysfs",
            "options": [
              "nosuid",
              "noexec",
              "nodev",
              "ro"
            ]
          },
          {
            "destination": "/sys/fs/cgroup",
            "source": "cgroup",
            "type_": "cgroup",
            "options": [
              "nosuid",
              "noexec",
              "nodev",
              "relatime",
              "ro"
            ]
          },
          {
            "destination": "/etc/hosts",
            "source": "$(sfprefix)hosts$",
            "type_": "bind",
            "options": [
              "rbind",
              "rprivate",
              "rw"
            ]
          },
          {
            "destination": "/dev/termination-log",
            "source": "$(sfprefix)termination-log$",
            "type_": "bind",
            "options": [
              "rbind",
              "rprivate",
              "rw"
            ]
          },
          {
            "destination": "/etc/hostname",
            "source": "$(sfprefix)hostname$",
            "type_": "bind",
            "options": [
              "rbind",
              "rprivate",
              "rw"
            ]
          },
          {
            "destination": "/etc/resolv.conf",
            "source": "$(sfprefix)resolv.conf$",
            "type_": "bind",
            "options": [
              "rbind",
              "rprivate",
              "rw"
            ]
          },
          {
            "destination": "/var/run/secrets/kubernetes.io/serviceaccount",
            "source": "$(sfprefix)serviceaccount$",
            "type_": "bind",
            "options": [
              "rbind",
              "rprivate",
              "ro"
            ]
          },
          {
            "destination": "/var/run/secrets/azure/tokens",
            "source": "$(sfprefix)tokens$",
            "type_": "bind",
            "options": [
              "rbind",
              "rprivate",
              "ro"
            ]
          },
          {
            "destination": "/results",
            "source": "^$(cpath)/$(sandbox-id)/local/results$",
            "type_": "local",
            "options": [
              "rbind",
              "rprivate",
              "rw"
            ]
          }
        ],
        "Annotations": {
          "io.katacontainers.pkg.oci.bundle_path": "/run/containerd/io.containerd.runtime.v2.task/k8s.io/$(bundle-id)",
          "io.katacontainers.pkg.oci.container_type": "pod_container",
          "io.kubernetes.cri.container-name": "querier",
          "io.kubernetes.cri.container-type": "container",
          "io.kubernetes.cri.image-name": "registry.k8s.io/e2e-test-images/agnhost:2.43",
          "io.kubernetes.cri.sandbox-id": "^[a-z0-9]{64}$",
          "io.kubernetes.cri.sandbox-name": "dns-test-f880e73f-1718-4455-9a78-766679e22471",
          "io.kubernetes.cri.sandbox-namespace": "dns-9988"
        },
        "Linux": {
          "Namespaces": [
            {
              "Type": "ipc",
              "Path": ""
            },
            {
              "Type": "uts",
              "Path": ""
            },
            {
              "Type": "mount",
              "Path": ""
            }
          ],
          "MaskedPaths": [
            "/proc/acpi",
            "/proc/kcore",
            "/proc/keys",
            "/proc/latency_stats",
            "/proc/timer_list",
            "/proc/timer_stats",
            "/proc/sched_debug",
            "/proc/scsi",
            "/sys/firmware"
          ],
          "ReadonlyPaths": [
            "/proc/asound",
            "/proc/bus",
            "/proc/fs",
            "/proc/irq",
            "/proc/sys",
            "/proc/sysrq-trigger"
          ]
        }
      },
      "storages": [
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash0)"
          ],
          "mount_point": "$(layer0)",
          "fs_group": null
        },
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash1)"
          ],
          "mount_point": "$(layer1)",
          "fs_group": null
        },
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash2)"
          ],
          "mount_point": "$(layer2)",
          "fs_group": null
        },
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash3)"
          ],
          "mount_point": "$(layer3)",
          "fs_group": null
        },
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash4)"
          ],
          "mount_point": "$(layer4)",
          "fs_group": null
        },
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash5)"
          ],
          "mount_point": "$(layer5)",
          "fs_group": null
        },
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash6)"
          ],
          "mount_point": "$(layer6)",
          "fs_group": null
        },
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash7)"
          ],
          "mount_point": "$(layer7)",
          "fs_group": null
        },
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash8)"
          ],
          "mount_point": "$(layer8)",
          "fs_group": null
        },
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash9)"
          ],
          "mount_point": "$(layer9)",
          "fs_group": null
        },
        {
          "driver": "overlayfs",
          "driver_options": [],
          "source": "",
          "fstype": "fuse3.kata-overlay",
          "options": [
            "51f1d5df9e5b64632779c996a3abb9b32cc69c76e0c17620ed6ceff15d3f281a:bf4d0147f3abea55550a8a612bdc1144b96966d520c267e15516d5157cb39bab:b1bb57a3e5d062f9a3de4fe1c2ad2328233a6817aa04bb28f83b86d81452af5b:daed717ef210067422c927c4edf220c433a8070cd7f0ac09c45079da2475c4f3:e1f6979b86c8eae10c68c19f3b05032dfab1d770182729adb3d808c70f7b9f7f:1535f78a07d52405ad7317cbfcedf04d600de40b17e31f5ab2556611004a5b5a:1918a052ffd206e459a2adb71cabebef00ccf744c22da64a8d8a94e093d6803b:207ea00b5dad0445a6c465826f2fb5713bb4dcca369531e2a7f595f537395596:9500e46617fb4582824921ce21f55aeaa95a319bb34ebfc119042bde19996edb:da5980a7e3434409da1232417a1d1cc02967b62a099502cacd13cc2e34206fa4",
            "ece5ef216c40047accf38d3a8b16899d13b2712067dd478a2178378ec7fcbfc6:17a838b0234782eb7f6bcaa0fb28bef9f630268d2e12c3b28022dabf1cdba812:9310f4b7c8d730be055096fb9e0dbb79649b02d097837d6609f92097ab808194:1a64471f3e96306020f55f8cf17ab69bc260370dfccf32620042ff2c606767fb:f4d2b244842f05f4b1be77069461ebdce73945d430b05f49af9c540a7ad6fee1:a71f00d258abee410ba922b4b54c30d7ea8dcdc05ae345e35ceb1e8a7fb0fdb9:215a7eb0b4ad484d599f945a5afb3700818cbcf79787c5931cb33e0bd2fa8df5:b11ec2290597597135a91df848128747ba768ad3fcaf0bb750b29216e2e3c2d1:9f1a82445901154cf99ed76e2b00797afafbe2b14136151aa0a7dea56a5c9f63:254c5314873c27a8de3db5347f56ebd9eb2bf46cc8812a43611f98e38ac37ba2"
          ],
          "mount_point": "$(cpath)/$(bundle-id)",
          "fs_group": null
        },
        {
          "driver": "local",
          "driver_options": [],
          "source": "local",
          "fstype": "local",
          "options": [
            "mode=0777"
          ],
          "mount_point": "^$(cpath)/$(sandbox-id)/local/results$",
          "fs_group": null
        }
      ],
      "sandbox_pidns": false,
      "exec_commands": []
    },
    {
      "OCI": {
        "Version": "1.1.0-rc.1",
        "Process": {
          "Terminal": false,
          "User": {
            "UID": 0,
            "GID": 0,
            "AdditionalGids": [],
            "Username": ""
          },
          "Args": [
            "sh",
            "-c",
            "for i in `seq 1 600`; do check=\"$$(dig +notcp +noall +answer +search kubernetes.default.svc.cluster.local A)\" && test -n \"$$check\" && echo OK > /results/jessie_udp@kubernetes.default.svc.cluster.local;check=\"$$(dig +tcp +noall +answer +search kubernetes.default.svc.cluster.local A)\" && test -n \"$$check\" && echo OK > /results/jessie_tcp@kubernetes.default.svc.cluster.local;sleep 1; done"
          ],
          "Env": [
            "PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
            "HOSTNAME=$(host-name)"
          ],
          "Cwd": "/",
          "Capabilities": {
            "Ambient": [],
            "Bounding": [
              "$(default_caps)"
            ],
            "Effective": [
              "$(default_caps)"
            ],
            "Inheritable": [],
            "Permitted": [
              "$(default_caps)"
            ]
          },
          "NoNewPrivileges": false
        },
        "Root": {
          "Path": "$(cpath)/$(bundle-id)",
          "Readonly": false
        },
        "Mounts": [
          {
            "destination": "/proc",
            "source": "proc",
            "type_": "proc",
            "options": [
              "nosuid",
              "noexec",
              "nodev"
            ]
          },
          {
            "destination": "/dev",
            "source": "tmpfs",
            "type_": "tmpfs",
            "options": [
              "nosuid",
              "strictatime",
              "mode=755",
              "size=65536k"
            ]
          },
          {
            "destination": "/dev/pts",
            "source": "devpts",
            "type_": "devpts",
            "options": [
              "nosuid",
              "noexec",
              "newinstance",
              "ptmxmode=0666",
              "mode=0620",
              "gid=5"
            ]
          },
          {
            "destination": "/dev/shm",
            "source": "/run/kata-containers/sandbox/shm",
            "type_": "bind",
            "options": [
              "rbind"
            ]
          },
          {
            "destination": "/dev/mqueue",
            "source": "mqueue",
            "type_": "mqueue",
            "options": [
              "nosuid",
              "noexec",
              "nodev"
            ]
          },
          {
            "destination": "/sys",
            "source": "sysfs",
            "type_": "sysfs",
            "options": [
              "nosuid",
              "noexec",
              "nodev",
              "ro"
            ]
          },
          {
            "destination": "/sys/fs/cgroup",
            "source": "cgroup",
            "type_": "cgroup",
            "options": [
              "nosuid",
              "noexec",
              "nodev",
              "relatime",
              "ro"
            ]
          },
          {
            "destination": "/etc/hosts",
            "source": "$(sfprefix)hosts$",
            "type_": "bind",
            "options": [
              "rbind",
              "rprivate",
              "rw"
            ]
          },
          {
            "destination": "/dev/termination-log",
            "source": "$(sfprefix)termination-log$",
            "type_": "bind",
            "options": [
              "rbind",
              "rprivate",
              "rw"
            ]
          },
          {
            "destination": "/etc/hostname",
            "source": "$(sfprefix)hostname$",
            "type_": "bind",
            "options": [
              "rbind",
              "rprivate",
              "rw"
            ]
          },
          {
            "destination": "/etc/resolv.conf",
            "source": "$(sfprefix)resolv.conf$",
            "type_": "bind",
            "options": [
              "rbind",
              "rprivate",
              "rw"
            ]
          },
          {
            "destination": "/var/run/secrets/kubernetes.io/serviceaccount",
            "source": "$(sfprefix)serviceaccount$",
            "type_": "bind",
            "options": [
              "rbind",
              "rprivate",
              "ro"
            ]
          },
          {
            "destination": "/var/run/secrets/azure/tokens",
            "source": "$(sfprefix)tokens$",
            "type_": "bind",
            "options": [
              "rbind",
              "rprivate",
              "ro"
            ]
          },
          {
            "destination": "/results",
            "source": "^$(cpath)/$(sandbox-id)/local/results$",
            "type_": "local",
            "options": [
              "rbind",
              "rprivate",
              "rw"
            ]
          }
        ],
        "Annotations": {
          "io.katacontainers.pkg.oci.bundle_path": "/run/containerd/io.containerd.runtime.v2.task/k8s.io/$(bundle-id)",
          "io.katacontainers.pkg.oci.container_type": "pod_container",
          "io.kubernetes.cri.container-name": "jessie-querier",
          "io.kubernetes.cri.container-type": "container",
          "io.kubernetes.cri.image-name": "registry.k8s.io/e2e-test-images/jessie-dnsutils:1.7",
          "io.kubernetes.cri.sandbox-id": "^[a-z0-9]{64}$",
          "io.kubernetes.cri.sandbox-name": "dns-test-f880e73f-1718-4455-9a78-766679e22471",
          "io.kubernetes.cri.sandbox-namespace": "dns-9988"
        },
        "Linux": {
          "Namespaces": [
            {
              "Type": "ipc",
              "Path": ""
            },
            {
              "Type": "uts",
              "Path": ""
            },
            {
              "Type": "mount",
              "Path": ""
            }
          ],
          "MaskedPaths": [
            "/proc/acpi",
            "/proc/kcore",
            "/proc/keys",
            "/proc/latency_stats",
            "/proc/timer_list",
            "/proc/timer_stats",
            "/proc/sched_debug",
            "/proc/scsi",
            "/sys/firmware"
          ],
          "ReadonlyPaths": [
            "/proc/asound",
            "/proc/bus",
            "/proc/fs",
            "/proc/irq",
            "/proc/sys",
            "/proc/sysrq-trigger"
          ]
        }
      },
      "storages": [
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash0)"
          ],
          "mount_point": "$(layer0)",
          "fs_group": null
        },
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash1)"
          ],
          "mount_point": "$(layer1)",
          "fs_group": null
        },
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash2)"
          ],
          "mount_point": "$(layer2)",
          "fs_group": null
        },
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash3)"
          ],
          "mount_point": "$(layer3)",
          "fs_group": null
        },
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash4)"
          ],
          "mount_point": "$(layer4)",
          "fs_group": null
        },
        {
          "driver": "blk",
          "driver_options": [],
          "source": "",
          "fstype": "tar",
          "options": [
            "$(hash5)"
          ],
          "mount_point": "$(layer5)",
          "fs_group": null
        },
        {
          "driver": "overlayfs",
          "driver_options": [],
          "source": "",
          "fstype": "fuse3.kata-overlay",
          "options": [
            "10b56c75689b2d3fd34dab586e284c8917baa7f2445b6439d78ab6d9645a60b3:e500049613eb4ef02e03e6580e80c5a826730a944521daff1eef776b2fcc0f20:ac83f4a372b3402193ea314ec7e8a87b91c59c73e23ba79cec92c1a41c8aaf54:0b2c5c3c4633820b5b4f6d77ea22c5ed0e3d3c33209165c2b181587b2d8be312:73fa0aa996a374cc846728f726393cfcff46c982dcf62d2d259f6006dee5e2bd:35f78af10b63402bb89da161513fa563465bcc1d4343c4f7d49811ff9b70dda9",
            "2bdc2fae3c87acc6a186336f8b3065502d1be7bcfaac32157dfc48c4b4c1d7f6:ebe623866ab372c5101baaf767b281de7100b9342696bcc82ff4f061f4b15966:213f840b100690804a76a1a9d3ce3c0531381b0a7607625803a6f867134412db:67450082ab56da1aecc5eae2f18d980cd9e7306e79334a1a826a91cfd90114a8:0859e5531fd7f8b17071414a082afb65b2be702ecdafa007dd0577aea86f8593:06f89c275dc34f26b9db0cf0102b2a899de6555105852d0af2bb95f374f7144d"
          ],
          "mount_point": "$(cpath)/$(bundle-id)",
          "fs_group": null
        },
        {
          "driver": "local",
          "driver_options": [],
          "source": "local",
          "fstype": "local",
          "options": [
            "mode=0777"
          ],
          "mount_point": "^$(cpath)/$(sandbox-id)/local/results$",
          "fs_group": null
        }
      ],
      "sandbox_pidns": false,
      "exec_commands": []
    }
  ],
  "common": {
    "cpath": "/run/kata-containers/shared/containers",
    "sfprefix": "^$(cpath)/$(bundle-id)-[a-z0-9]{16}-",
    "spath": "/run/kata-containers/sandbox/storage",
    "ipv4_a": "((25[0-5]|(2[0-4]|1\\d|[1-9]|)\\d)\\.?\\b){4}",
    "ip_p": "[0-9]{1,5}",
    "svc_name": "[A-Z0-9_\\.\\-]+",
    "dns_label": "[a-zA-Z0-9_\\.\\-]+",
    "default_caps": [
      "CAP_CHOWN",
      "CAP_DAC_OVERRIDE",
      "CAP_FSETID",
      "CAP_FOWNER",
      "CAP_MKNOD",
      "CAP_NET_RAW",
      "CAP_SETGID",
      "CAP_SETUID",
      "CAP_SETFCAP",
      "CAP_SETPCAP",
      "CAP_NET_BIND_SERVICE",
      "CAP_SYS_CHROOT",
      "CAP_KILL",
      "CAP_AUDIT_WRITE"
    ],
    "privileged_caps": [
      "CAP_CHOWN",
      "CAP_DAC_OVERRIDE",
      "CAP_DAC_READ_SEARCH",
      "CAP_FOWNER",
      "CAP_FSETID",
      "CAP_KILL",
      "CAP_SETGID",
      "CAP_SETUID",
      "CAP_SETPCAP",
      "CAP_LINUX_IMMUTABLE",
      "CAP_NET_BIND_SERVICE",
      "CAP_NET_BROADCAST",
      "CAP_NET_ADMIN",
      "CAP_NET_RAW",
      "CAP_IPC_LOCK",
      "CAP_IPC_OWNER",
      "CAP_SYS_MODULE",
      "CAP_SYS_RAWIO",
      "CAP_SYS_CHROOT",
      "CAP_SYS_PTRACE",
      "CAP_SYS_PACCT",
      "CAP_SYS_ADMIN",
      "CAP_SYS_BOOT",
      "CAP_SYS_NICE",
      "CAP_SYS_RESOURCE",
      "CAP_SYS_TIME",
      "CAP_SYS_TTY_CONFIG",
      "CAP_MKNOD",
      "CAP_LEASE",
      "CAP_AUDIT_WRITE",
      "CAP_AUDIT_CONTROL",
      "CAP_SETFCAP",
      "CAP_MAC_OVERRIDE",
      "CAP_MAC_ADMIN",
      "CAP_SYSLOG",
      "CAP_WAKE_ALARM",
      "CAP_BLOCK_SUSPEND",
      "CAP_AUDIT_READ",
      "CAP_PERFMON",
      "CAP_BPF",
      "CAP_CHECKPOINT_RESTORE"
    ],
    "virtio_blk_storage_classes": [
      "cc-local-csi",
      "cc-managed-csi",
      "cc-managed-premium-csi"
    ],
    "smb_storage_classes": [
      "cc-azurefile-csi",
      "cc-azurefile-premium-csi"
    ]
  },
  "sandbox": {
    "storages": [
      {
        "driver": "ephemeral",
        "driver_options": [],
        "source": "shm",
        "fstype": "tmpfs",
        "options": [
          "noexec",
          "nosuid",
          "nodev",
          "mode=1777",
          "size=67108864"
        ],
        "mount_point": "/run/kata-containers/sandbox/shm",
        "fs_group": null
      }
    ]
  },
  "request_defaults": {
    "CreateContainerRequest": {
      "allow_env_regex": [
        "^HOSTNAME=$(dns_label)$",
        "^$(svc_name)_PORT_$(ip_p)_TCP=tcp://$(ipv4_a):$(ip_p)$",
        "^$(svc_name)_PORT_$(ip_p)_TCP_PROTO=tcp$",
        "^$(svc_name)_PORT_$(ip_p)_TCP_PORT=$(ip_p)$",
        "^$(svc_name)_PORT_$(ip_p)_TCP_ADDR=$(ipv4_a)$",
        "^$(svc_name)_SERVICE_HOST=$(ipv4_a)$",
        "^$(svc_name)_SERVICE_PORT=$(ip_p)$",
        "^$(svc_name)_SERVICE_PORT_$(dns_label)=$(ip_p)$",
        "^$(svc_name)_PORT=tcp://$(ipv4_a):$(ip_p)$",
        "^AZURE_CLIENT_ID=[A-Fa-f0-9-]*$",
        "^AZURE_TENANT_ID=[A-Fa-f0-9-]*$",
        "^AZURE_FEDERATED_TOKEN_FILE=/var/run/secrets/azure/tokens/azure-identity-token$",
        "^AZURE_AUTHORITY_HOST=https://login\\.microsoftonline\\.com/$"
      ]
    },
    "CopyFileRequest": [
      "$(sfprefix)"
    ],
    "ExecProcessRequest": {
      "commands": [],
      "regex": []
    },
    "CloseStdinRequest": false,
    "ReadStreamRequest": true,
    "UpdateEphemeralMountsRequest": false,
    "WriteStreamRequest": false
  }
} 