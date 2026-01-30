package regorus

// #cgo LDFLAGS: -L ../../../ffi/target/release -L ../../../ffi/target/debug -lregorus_ffi
// #include "../../../ffi/regorus.h"
import "C"
import (
	"fmt"
	"unsafe"
)

type PolicyModule struct {
	Id      string
	Content string
}

type Program struct {
	p *C.RegorusProgram
}

type Rvm struct {
	vm *C.RegorusRvm
}

type Buffer struct {
	b *C.RegorusBuffer
}

func (b *Buffer) Close() {
	if b != nil && b.b != nil {
		C.regorus_buffer_drop(b.b)
		b.b = nil
	}
}

func (b *Buffer) Bytes() []byte {
	if b == nil || b.b == nil || b.b.data == nil || b.b.len == 0 {
		return nil
	}
	return C.GoBytes(unsafe.Pointer(b.b.data), C.int(b.b.len))
}

func (p *Program) Close() {
	if p != nil && p.p != nil {
		C.regorus_program_drop(p.p)
		p.p = nil
	}
}

func (p *Program) SerializeBinary() ([]byte, error) {
	result := C.regorus_program_serialize_binary(p.p)
	defer C.regorus_result_drop(result)
	if result.status != C.Ok {
		return nil, fmt.Errorf("%s", C.GoString(result.error_message))
	}
	buffer := &Buffer{b: (*C.RegorusBuffer)(result.pointer_value)}
	defer buffer.Close()
	return buffer.Bytes(), nil
}

func (p *Program) GenerateListing() (string, error) {
	result := C.regorus_program_generate_listing(p.p)
	defer C.regorus_result_drop(result)
	if result.status != C.Ok {
		return "", fmt.Errorf("%s", C.GoString(result.error_message))
	}
	return C.GoString(result.output), nil
}

func (p *Program) GenerateTabularListing() (string, error) {
	result := C.regorus_program_generate_tabular_listing(p.p)
	defer C.regorus_result_drop(result)
	if result.status != C.Ok {
		return "", fmt.Errorf("%s", C.GoString(result.error_message))
	}
	return C.GoString(result.output), nil
}

func DeserializeProgram(data []byte) (*Program, bool, error) {
	if len(data) == 0 {
		return nil, false, fmt.Errorf("empty program data")
	}
	var isPartial C.bool
	result := C.regorus_program_deserialize_binary((*C.uchar)(unsafe.Pointer(&data[0])), C.ulong(len(data)), (*C.bool)(unsafe.Pointer(&isPartial)))
	defer C.regorus_result_drop(result)
	if result.status != C.Ok {
		return nil, false, fmt.Errorf("%s", C.GoString(result.error_message))
	}
	return &Program{p: (*C.RegorusProgram)(result.pointer_value)}, bool(isPartial), nil
}

func CompileProgramFromModules(data string, modules []PolicyModule, entryPoints []string) (*Program, error) {
	dataC := C.CString(data)
	defer C.free(unsafe.Pointer(dataC))

	cModules := make([]C.RegorusPolicyModule, len(modules))
	moduleIdPtrs := make([]*C.char, len(modules))
	moduleContentPtrs := make([]*C.char, len(modules))
	for i, module := range modules {
		idC := C.CString(module.Id)
		contentC := C.CString(module.Content)
		moduleIdPtrs[i] = idC
		moduleContentPtrs[i] = contentC
		cModules[i].id = idC
		cModules[i].content = contentC
	}
	defer func() {
		for i := range moduleIdPtrs {
			if moduleIdPtrs[i] != nil {
				C.free(unsafe.Pointer(moduleIdPtrs[i]))
			}
			if moduleContentPtrs[i] != nil {
				C.free(unsafe.Pointer(moduleContentPtrs[i]))
			}
		}
	}()

	entryPtrs := make([]*C.char, len(entryPoints))
	for i, entry := range entryPoints {
		entryPtrs[i] = C.CString(entry)
	}
	defer func() {
		for _, ptr := range entryPtrs {
			C.free(unsafe.Pointer(ptr))
		}
	}()

	var modulesPtr *C.RegorusPolicyModule
	if len(cModules) > 0 {
		modulesPtr = (*C.RegorusPolicyModule)(unsafe.Pointer(&cModules[0]))
	}
	var entryPtr **C.char
	if len(entryPtrs) > 0 {
		entryPtr = (**C.char)(unsafe.Pointer(&entryPtrs[0]))
	}

	result := C.regorus_program_compile_from_modules(
		dataC,
		modulesPtr,
		C.ulong(len(cModules)),
		entryPtr,
		C.ulong(len(entryPtrs)),
	)
	defer C.regorus_result_drop(result)
	if result.status != C.Ok {
		return nil, fmt.Errorf("%s", C.GoString(result.error_message))
	}
	return &Program{p: (*C.RegorusProgram)(result.pointer_value)}, nil
}

func CompileProgramFromEngine(engine *Engine, entryPoints []string) (*Program, error) {
	entryPtrs := make([]*C.char, len(entryPoints))
	for i, entry := range entryPoints {
		entryPtrs[i] = C.CString(entry)
	}
	defer func() {
		for _, ptr := range entryPtrs {
			C.free(unsafe.Pointer(ptr))
		}
	}()

	var entryPtr **C.char
	if len(entryPtrs) > 0 {
		entryPtr = (**C.char)(unsafe.Pointer(&entryPtrs[0]))
	}

	result := C.regorus_engine_compile_program_with_entrypoints(
		engine.e,
		entryPtr,
		C.ulong(len(entryPtrs)),
	)
	defer C.regorus_result_drop(result)
	if result.status != C.Ok {
		return nil, fmt.Errorf("%s", C.GoString(result.error_message))
	}
	return &Program{p: (*C.RegorusProgram)(result.pointer_value)}, nil
}

func NewRvm() (*Rvm, error) {
	vm := C.regorus_rvm_new()
	if vm == nil {
		return nil, fmt.Errorf("failed to create RVM")
	}
	return &Rvm{vm: vm}, nil
}

func (r *Rvm) Close() {
	if r != nil && r.vm != nil {
		C.regorus_rvm_drop(r.vm)
		r.vm = nil
	}
}

func (r *Rvm) LoadProgram(program *Program) error {
	result := C.regorus_rvm_load_program(r.vm, program.p)
	defer C.regorus_result_drop(result)
	if result.status != C.Ok {
		return fmt.Errorf("%s", C.GoString(result.error_message))
	}
	return nil
}

func (r *Rvm) SetDataJson(data string) error {
	dataC := C.CString(data)
	defer C.free(unsafe.Pointer(dataC))
	result := C.regorus_rvm_set_data(r.vm, dataC)
	defer C.regorus_result_drop(result)
	if result.status != C.Ok {
		return fmt.Errorf("%s", C.GoString(result.error_message))
	}
	return nil
}

func (r *Rvm) SetInputJson(input string) error {
	inputC := C.CString(input)
	defer C.free(unsafe.Pointer(inputC))
	result := C.regorus_rvm_set_input(r.vm, inputC)
	defer C.regorus_result_drop(result)
	if result.status != C.Ok {
		return fmt.Errorf("%s", C.GoString(result.error_message))
	}
	return nil
}

func (r *Rvm) SetExecutionMode(mode byte) error {
	result := C.regorus_rvm_set_execution_mode(r.vm, C.uchar(mode))
	defer C.regorus_result_drop(result)
	if result.status != C.Ok {
		return fmt.Errorf("%s", C.GoString(result.error_message))
	}
	return nil
}

func (r *Rvm) Execute() (string, error) {
	result := C.regorus_rvm_execute(r.vm)
	defer C.regorus_result_drop(result)
	if result.status != C.Ok {
		return "", fmt.Errorf("%s", C.GoString(result.error_message))
	}
	return C.GoString(result.output), nil
}

func (r *Rvm) ExecuteEntryPoint(name string) (string, error) {
	nameC := C.CString(name)
	defer C.free(unsafe.Pointer(nameC))
	result := C.regorus_rvm_execute_entry_point_by_name(r.vm, nameC)
	defer C.regorus_result_drop(result)
	if result.status != C.Ok {
		return "", fmt.Errorf("%s", C.GoString(result.error_message))
	}
	return C.GoString(result.output), nil
}

func (r *Rvm) ExecuteEntryPointIndex(index uint64) (string, error) {
	result := C.regorus_rvm_execute_entry_point_by_index(r.vm, C.ulong(index))
	defer C.regorus_result_drop(result)
	if result.status != C.Ok {
		return "", fmt.Errorf("%s", C.GoString(result.error_message))
	}
	return C.GoString(result.output), nil
}

func (r *Rvm) Resume(resumeValue string, hasValue bool) (string, error) {
	var valueC *C.char
	if hasValue {
		valueC = C.CString(resumeValue)
		defer C.free(unsafe.Pointer(valueC))
	}
	result := C.regorus_rvm_resume(r.vm, valueC, C.bool(hasValue))
	defer C.regorus_result_drop(result)
	if result.status != C.Ok {
		return "", fmt.Errorf("%s", C.GoString(result.error_message))
	}
	return C.GoString(result.output), nil
}

func (r *Rvm) GetExecutionState() (string, error) {
	result := C.regorus_rvm_get_execution_state(r.vm)
	defer C.regorus_result_drop(result)
	if result.status != C.Ok {
		return "", fmt.Errorf("%s", C.GoString(result.error_message))
	}
	return C.GoString(result.output), nil
}
