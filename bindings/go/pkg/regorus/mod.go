package regorus

// #cgo LDFLAGS: -L ../../../../target/release -lregorus_ffi
// #include "../../../ffi/regorus.h"
import "C"
import (
	"fmt"
	"unsafe"
)

type Engine struct {
	e *C.RegorusEngine
}

func NewEngine() *Engine {
	e := new(Engine)
	e.e = C.regorus_engine_new()
	return e
}

func (e *Engine) Close() {
	C.regorus_engine_drop(e.e)
}

func (e *Engine) Clone() *Engine {
	c := new(Engine)
	c.e = C.regorus_engine_clone(e.e)
	return c
}

func (e *Engine) AddPolicy(path string, rego string) error {
	path_c := C.CString(path)
	defer C.free(unsafe.Pointer(path_c))

	rego_c := C.CString(rego)
	defer C.free(unsafe.Pointer(rego_c))

	result := C.regorus_engine_add_policy(e.e, path_c, rego_c)
	defer C.regorus_result_drop(result)
	if result.status != C.RegorusStatusOk {
		return fmt.Errorf("%s", C.GoString(result.error_message))
	}
	return nil
}

func (e *Engine) AddPolicyFromFile(path string) error {
	path_c := C.CString(path)
	defer C.free(unsafe.Pointer(path_c))

	result := C.regorus_engine_add_policy_from_file(e.e, path_c)
	defer C.regorus_result_drop(result)
	if result.status != C.RegorusStatusOk {
		return fmt.Errorf("%s", C.GoString(result.error_message))
	}
	return nil
}

func (e *Engine) AddDataJson(data string) error {
	data_c := C.CString(data)
	defer C.free(unsafe.Pointer(data_c))

	result := C.regorus_engine_add_data_json(e.e, data_c)
	defer C.regorus_result_drop(result)
	if result.status != C.RegorusStatusOk {
		return fmt.Errorf("%s", C.GoString(result.error_message))
	}
	return nil
}

func (e *Engine) AddDataFromJsonFile(path string) error {
	path_c := C.CString(path)
	defer C.free(unsafe.Pointer(path_c))

	result := C.regorus_engine_add_data_from_json_file(e.e, path_c)
	defer C.regorus_result_drop(result)
	if result.status != C.RegorusStatusOk {
		return fmt.Errorf("%s", C.GoString(result.error_message))
	}
	return nil
}

func (e *Engine) SetInputJson(input string) error {
	input_c := C.CString(input)
	defer C.free(unsafe.Pointer(input_c))

	result := C.regorus_engine_set_input_json(e.e, input_c)
	defer C.regorus_result_drop(result)
	if result.status != C.RegorusStatusOk {
		return fmt.Errorf("%s", C.GoString(result.error_message))
	}
	return nil
}

func (e *Engine) SetInputFromJsonFile(path string) error {
	path_c := C.CString(path)
	defer C.free(unsafe.Pointer(path_c))

	result := C.regorus_engine_set_input_from_json_file(e.e, path_c)
	defer C.regorus_result_drop(result)
	if result.status != C.RegorusStatusOk {
		return fmt.Errorf("%s", C.GoString(result.error_message))
	}
	return nil
}

func (e *Engine) EvalQuery(query string) (string, error) {
	query_c := C.CString(query)
	defer C.free(unsafe.Pointer(query_c))

	result := C.regorus_engine_eval_query(e.e, query_c)
	defer C.regorus_result_drop(result)
	if result.status != C.RegorusStatusOk {
		return "", fmt.Errorf("%s", C.GoString(result.error_message))
	}

	return C.GoString(result.output), nil
}
