package flagopt

import (
	"errors"
	"reflect"
	"strconv"
	"strings"
)

// Caller is the interface to the command value stored in a FlagSet.
type Caller interface {
	Call() error
}

var _ Caller = (*Func)(nil)

// Setter is the optional interface used to set arguments for the caller.
type Setter interface {
	// Set is called for each non-option argument until it returns true,
	// indicating that there are no more arguments to be set.
	//
	// An ErrBreak error can be returned to stop the parser.
	Set(string) (bool, error)
}

var _ Setter = (*Func)(nil)

// From is the optional interface used by the parser to inform the Caller
// what is the current command argument.
//
// Use this interface to implement deprecated commands.
type From interface {
	// From is the same interface as Caller.Set but is called with the
	// argument used to set the current FlagSet.
	//
	// An ErrBreak error can be returned to stop the parser.
	From(string) (bool, error)
}

var _ From = (*Func)(nil)

// Signature is the optional interface used to describe the Caller in Usage.
type Signature interface {
	Signature() string
}

var _ Signature = (*Func)(nil)

// IsOption is the optional interface used to determine when an option should
// be treated as an argument.
type IsOption interface {
	IsOption(string) bool
}

var _ IsOption = (*Func)(nil)

type setFinalizer interface {
	set(string) (bool, error)
	finalize() error
}

type valueKind int

const (
	pointer valueKind = iota + 1
	variadic
	slice
	mapvalue
	iterator
)

type arg struct {
	v     reflect.Value
	value Value
	kind  valueKind
	next  *arg
}

// Func represents a runtime function value.
type Func struct {
	v       interface{}
	argv    []reflect.Value
	canErr  bool
	current *arg
	first   *arg
}

var (
	errTooManyArguments   = errors.New("too many arguments")
	errNotEnoughArguments = errors.New("not enough arguments")
)

func (f *Func) IsOption(arg string) bool {
	if f.current == nil {
		return true
	}
	i, ok := f.current.value.(isNumFlag)
	if !ok {
		return true
	}
	var err error
	switch i.isNumFlag() {
	case numInt:
		_, err = strconv.ParseInt(arg, 0, 64)
	case numFloat:
		_, err = strconv.ParseFloat(arg, 64)
	default:
		return true
	}
	return err != nil
}

// From returns true when function f holds zero parameters.
func (f *Func) From(string) (bool, error) {
	return f.current == nil, nil
}

// Set is used to prepare the arguments needed for function f.
func (f *Func) Set(arg string) (bool, error) {
	if f.current == nil {
		return false, errTooManyArguments
	}
	if f.current.value == nil {
		return false, errTooManyArguments
	}

	var (
		err  error
		next bool
	)
	if fv, ok := f.current.value.(setFinalizer); ok {
		next, err = fv.set(arg)
	} else {
		err = f.current.value.Set(arg)
	}
	if err != nil {
		return false, err
	}

	if f.current.kind <= pointer || next {
		f.argv = append(f.argv, f.current.v.Elem())
		f.current = f.current.next
	}
	return f.current.value == nil, nil
}

func (f *Func) reset() {
	f.argv = nil
	f.current = f.first
	for n := f.current; n != nil; n = n.next {
		if n.value == nil {
			break
		}
		n.v.Elem().Set(reflect.Zero(n.v.Elem().Type()))
	}
}

func (f *Func) set(arg ...string) (ok bool, err error) {
	for _, v := range arg {
		ok, err = f.Set(v)
		if err != nil {
			break
		}
	}
	return
}

func (f *Func) finalize() error {
	// no function arguments
	if f.current == nil {
		return nil
	}

	var v reflect.Value
	if f.current.v.IsValid() {
		v = f.current.v.Elem()
	}
	switch f.current.kind {
	case mapvalue:
		f.argv = append(f.argv, v)
	case iterator:
		err := f.current.value.(setFinalizer).finalize()
		if err != nil {
			return err
		}
		f.argv = append(f.argv, v)
	case slice:
		// slices require atleast one argument
		if v.Len() == 0 {
			return errNotEnoughArguments
		}
		f.argv = append(f.argv, v)
	case variadic:
		for i := 0; i < v.Len(); i++ {
			f.argv = append(f.argv, v.Index(i))
		}
	case pointer:
		for n := f.current; n != nil; n = n.next {
			if n.value == nil {
				break
			}
			switch n.kind {
			case variadic, mapvalue:
			case pointer:
				f.argv = append(f.argv, n.v.Elem())
			default:
				return errNotEnoughArguments
			}
		}
	default:
		if f.current.value != nil {
			return errNotEnoughArguments
		}
	}
	return nil
}

// Call runs function f with arguments prepared by Set.
func (f *Func) Call() error {
	if err := f.finalize(); err != nil {
		return err
	}
	err := reflect.ValueOf(f.v).Call(f.argv)
	if !f.canErr {
		return nil
	}
	if e, ok := err[0].Interface().(error); ok {
		return e
	}
	return nil
}

type invalidSigError struct{ error }

func (e invalidSigError) Error() string {
	return "invalid function signature: " + e.error.Error()
}

func (e invalidSigError) Unwrap() error { return e.error }

var (
	errNonFinalSlice  = errors.New("slice as non-final parameter")
	errNonFinalMap    = errors.New("map as non-final parameter")
	errMultipleReturn = errors.New("multiple return values")
	errReturnNotError = errors.New("return value does not implement the error interface")
)

var errorT = reflect.TypeOf((*error)(nil)).Elem()

func newFunc(v interface{}) (_ *Func, err error) {
	rv := reflect.ValueOf(v)
	if !rv.IsValid() {
		return nil, errors.New("invalid function value")
	}
	rt := rv.Type()
	if rt.Kind() != reflect.Func {
		return nil, errors.New("value is not a function type")
	}
	if rv.IsNil() {
		return nil, errors.New("nil function value")
	}

	cmd := &Func{v: v}
	var args *arg
	for i, in := 0, rt.NumIn(); i < in; i++ {
		if cmd.current == nil {
			cmd.current = new(arg)
			cmd.first = cmd.current
			args = cmd.current
		}

		ri := rt.In(i)
		args.v = reflect.New(ri)
		args.value, err = newValue(args.v.Interface())
		if err != nil {
			return nil, err
		}
		switch ri.Kind() {
		case reflect.Slice:
			if i != in-1 {
				return nil, invalidSigError{errNonFinalSlice}
			}
			if rt.IsVariadic() {
				args.kind = variadic
			} else {
				args.kind = slice
			}
		case reflect.Map:
			if i != in-1 {
				return nil, invalidSigError{errNonFinalMap}
			}
			args.kind = mapvalue
		case reflect.Ptr:
			args.kind = pointer
		default:
			if _, ok := args.value.(setFinalizer); ok {
				args.kind = iterator
			}
		}

		args.next = new(arg)
		args = args.next
	}

	if i := rt.NumOut(); i == 0 {
		return cmd, nil
	} else if i > 1 {
		return nil, invalidSigError{errMultipleReturn}
	} else {
		cmd.canErr = true
	}
	if !rt.Out(0).Implements(errorT) {
		return nil, invalidSigError{errReturnNotError}
	}
	return cmd, nil
}

// Signature describes the parameters of runtime function f.
func (f *Func) Signature() string {
	if f.first == nil {
		return ""
	}
	b := new(strings.Builder)
	for p := f.first; p != nil; p = p.next {
		if p.value == nil {
			break
		}
		switch p.kind {
		case pointer, variadic, mapvalue:
			b.WriteString("[")
		}
		b.WriteString(p.value.Type())
		switch p.kind {
		case pointer:
			b.WriteString("]")
		case slice:
			b.WriteString("...")
		case variadic, mapvalue:
			b.WriteString("...]")
		}
		if p.next.value != nil {
			b.WriteString(" ")
		}
	}
	return b.String()
}

// NewFunc takes a function value fn and returns a value that implements
// the Caller interface used by FlagSet.
//
// Function may take any number of parameters and return a value that
// implements the error interface. It must not have slices, maps or variadic
// values as non-final parameters. Pointers are optional unless they are followed
// by non-pointer values. Slices require atleast one argument.
//
// All function parameters are set by using NewValue.
//
// It panics if fn is not a function or does not have the correct signature.
func NewFunc(fn interface{}) *Func {
	f, err := newFunc(fn)
	if err != nil {
		panic(err)
	}
	return f
}
