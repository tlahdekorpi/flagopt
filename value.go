package flagopt

import (
	"errors"
	"flag"
	"fmt"
	"reflect"
	"strconv"
	"strings"
	"unicode"
)

// Type is the interface used to describe the type of a value.
type Type interface {
	Type() string
}

type numKind int

const (
	numNan numKind = iota
	numInt
	numFloat
)

type isNumFlag interface {
	isNumFlag() numKind
}

// Value is the flag.Value interface containing the Type interface.
type Value interface {
	flag.Value
	Type
}

type stringValue string

func (s *stringValue) Type() (empty string)       { return "string" }
func (s *stringValue) String() string             { return string(*s) }
func (s *stringValue) Set(v string) (empty error) { *(*string)(s) = v; return }

type boolValue bool

func (b *boolValue) IsBoolFlag() bool { return true }
func (b *boolValue) Type() string     { return "bool" }
func (b *boolValue) String() string {
	return strconv.FormatBool(bool(*b))
}
func (b *boolValue) Set(value string) error {
	v, err := strconv.ParseBool(value)
	if err == nil {
		*(*bool)(b) = v
		return nil
	}
	var ne *strconv.NumError
	if !errors.As(err, &ne) {
		return err
	}
	return numError{NumError: ne, t: reflect.Bool}
}

type boolInverse bool

func (b *boolInverse) IsBoolFlag() bool { return true }
func (b *boolInverse) Type() string     { return "bool" }
func (b *boolInverse) String() string   { return (*boolValue)(b).String() }
func (b *boolInverse) Set(value string) (err error) {
	if err = (*boolValue)(b).Set(value); err == nil {
		*b = !*b
	}
	return
}

type pointerValue struct {
	v reflect.Value
}

func (p pointerValue) new() interface{} {
	t := p.v.Type()
	for i := p.v.Type(); i.Kind() == reflect.Ptr; i = i.Elem() {
		t = i
	}
	return reflect.New(t.Elem()).Interface()
}
func (p pointerValue) make() {
	for ; p.v.Type().Kind() == reflect.Ptr; p.v = p.v.Elem() {
		if !p.v.IsNil() {
			break
		}
		p.v.Set(reflect.New(p.v.Type().Elem()))
	}
}
func (p pointerValue) isNumFlag() (_ numKind) {
	if !p.v.IsValid() {
		return
	}
	if i, ok := NewValue(p.new()).(isNumFlag); ok {
		return i.isNumFlag()
	}
	return
}
func (p pointerValue) IsBoolFlag() bool {
	if !p.v.IsValid() {
		return false
	}
	if i, ok := NewValue(p.new()).(boolFlag); ok {
		return i.IsBoolFlag()
	}
	return false
}
func (p pointerValue) String() string {
	if !p.v.IsValid() {
		return ""
	}
	return NewValue(p.new()).String()
}
func (p pointerValue) Type() string {
	if !p.v.IsValid() {
		return "ptr"
	}
	return NewValue(p.new()).Type()
}
func (p pointerValue) Set(v string) error {
	p.make()
	return NewValue(p.v.Interface()).Set(v)
}

type strconvBool struct{ strconvValue }

func (strconvBool) IsBoolFlag() bool { return true }

type strconvComplex struct{ strconvValue }

func (v strconvComplex) String() string {
	if !v.strconvValue.v.IsValid() {
		return "(0+0i)"
	}
	return fmt.Sprint(v.strconvValue.v)
}

type strconvValue struct {
	v reflect.Value
}

func (v strconvValue) Type() string {
	if t, ok := v.v.Interface().(Type); ok {
		return t.Type()
	}
	return v.v.Kind().String()
}

func (v strconvValue) String() string {
	if !v.v.IsValid() {
		return "0"
	}
	return fmt.Sprint(v.v)
}

type numError struct {
	*strconv.NumError
	t reflect.Kind
}

func (n numError) Error() string {
	return fmt.Sprintf("unable to parse as %s, %s", n.t, n.Err)
}

func (v strconvValue) isNumFlag() (_ numKind) {
	if !v.v.IsValid() {
		return
	}
	switch v.v.Kind() {
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64,
		reflect.Bool, reflect.String:
		return
	case reflect.Float32, reflect.Float64:
		return numFloat
	}
	return numInt
}

func (v strconvValue) Set(value string) (err error) {
	switch k := v.v.Kind(); k {
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		var i int64
		if i, err = strconv.ParseInt(value, 0, v.v.Type().Bits()); err == nil {
			v.v.SetInt(i)
		}
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64:
		var i uint64
		if i, err = strconv.ParseUint(value, 0, v.v.Type().Bits()); err == nil {
			v.v.SetUint(i)
		}
	case reflect.Float32, reflect.Float64:
		var i float64
		if i, err = strconv.ParseFloat(value, v.v.Type().Bits()); err == nil {
			v.v.SetFloat(i)
		}
	case reflect.Complex64, reflect.Complex128:
		var i complex128
		if i, err = strconv.ParseComplex(value, v.v.Type().Bits()); err == nil {
			v.v.SetComplex(i)
		}
	case reflect.Bool:
		var i bool
		if i, err = strconv.ParseBool(value); err == nil {
			v.v.SetBool(i)
		}
	case reflect.String:
		v.v.SetString(value)
		return
	default:
		panic(fmt.Sprintf("not implemented: %s", k))
	}
	if err == nil {
		return
	}
	var ne *strconv.NumError
	if !errors.As(err, &ne) {
		return
	}
	return numError{NumError: ne, t: v.v.Kind()}
}

type sliceValue struct {
	v reflect.Value
}

func (p sliceValue) new() reflect.Value { return reflect.New(p.v.Type().Elem()) }
func (p sliceValue) Type() string       { return NewValue(p.new().Interface()).Type() }
func (p sliceValue) isNumFlag() (_ numKind) {
	if i, ok := NewValue(p.new().Interface()).(isNumFlag); ok {
		return i.isNumFlag()
	}
	return
}
func (p sliceValue) IsBoolFlag() bool {
	if i, ok := NewValue(p.new().Interface()).(boolFlag); ok {
		return i.IsBoolFlag()
	}
	return false
}
func (p sliceValue) String() string {
	if !p.v.IsValid() || p.v.Len() == 0 {
		return "[]"
	}
	b := new(strings.Builder)
	b.WriteByte('[')
	for i, j := 0, p.v.Len(); i < j; i++ {
		b.WriteString(ptrValue(p.v.Index(i)).String())
		if i < j-1 {
			b.WriteByte(',')
		}
	}
	b.WriteByte(']')
	return b.String()
}
func (p sliceValue) Set(v string) (err error) {
	nv := p.new()
	if err = NewValue(nv.Interface()).Set(v); err == nil {
		p.v.Set(reflect.Append(p.v, nv.Elem()))
	}
	return
}

type mapValue struct {
	v reflect.Value
}

func (m mapValue) isNumFlag() (_ numKind) {
	if i, ok := NewValue(reflect.New(
		m.v.Type().Key(),
	).Interface()).(isNumFlag); ok {
		return i.isNumFlag()
	}
	return
}

func (m mapValue) Type() string {
	rt := m.v.Type()
	k, v := reflect.New(rt.Key()), reflect.New(rt.Elem())
	return NewValue(k.Interface()).Type() + "=" + NewValue(v.Interface()).Type()
}

func ptrValue(v reflect.Value) Value {
	i := reflect.New(v.Type())
	i.Elem().Set(v)
	return NewValue(i.Interface())
}

func (m mapValue) String() (out string) {
	if !m.v.IsValid() {
		return
	}
	for i := m.v.MapRange(); i.Next(); {
		out += fmt.Sprintf("%s=%s, ", ptrValue(i.Key()), ptrValue(i.Value()))
	}
	if len(out) > 2 {
		return out[:len(out)-2]
	}
	return ""
}

func (m mapValue) Set(value string) (err error) {
	var i int
	if i = strings.IndexByte(value, '='); i == -1 {
		return errors.New("invalid map syntax")
	}
	if m.v.IsNil() {
		m.v.Set(reflect.MakeMap(m.v.Type()))
	}
	k := reflect.New(m.v.Type().Key())
	if err = NewValue(k.Interface()).Set(value[:i]); err != nil {
		return
	}
	v, mv := reflect.New(m.v.Type().Elem()), m.v.MapIndex(k.Elem())
	if mv.IsValid() {
		v.Elem().Set(mv)
	}
	if err = NewValue(v.Interface()).Set(value[i+1:]); err != nil {
		return
	}
	m.v.SetMapIndex(k.Elem(), v.Elem())
	return
}

type flagValue struct {
	flag.Value
}

func (v flagValue) isNumFlag() (_ numKind) {
	if i, ok := v.Value.(isNumFlag); ok {
		return i.isNumFlag()
	}
	return
}
func (v flagValue) IsBoolFlag() bool {
	if i, ok := v.Value.(boolFlag); ok {
		return i.IsBoolFlag()
	}
	return false
}
func (v flagValue) Type() string {
	rt := reflect.ValueOf(v.Value).Type()
	for ; rt.Kind() == reflect.Ptr; rt = rt.Elem() {
	}
	return rt.Kind().String()
}

type funcFlag struct {
	*Func
}

func (f funcFlag) isNumFlag() (_ numKind) {
	if f.Func.current == nil || f.Func.current.value == nil {
		return
	}
	if i, ok := f.Func.current.value.(isNumFlag); ok {
		return i.isNumFlag()
	}
	return
}
func (f funcFlag) IsBoolFlag() bool {
	return f.Func.first == nil || f.Func.first.kind == variadic
}
func (f funcFlag) Type() string           { return f.Func.Signature() }
func (f funcFlag) String() (empty string) { return }
func (f funcFlag) Set(value string) (err error) {
	if f.Func.first == nil {
		return f.Func.Call()
	}
	if f.Func.first.kind == variadic && value == "true" {
		return f.Func.Call()
	}
	// TODO: Implement setFinalizer
	_, err = f.Func.set(strings.Split(value, ",")...)
	if err == nil {
		defer f.reset()
		err = f.Func.Call()
	}
	return err
}

type structFlag struct {
	v       reflect.Value
	current *arg
	first   *arg
}

var _ setFinalizer = (*structFlag)(nil)

func (s *structFlag) isNumFlag() (_ numKind) {
	if s.current == nil || s.current.value == nil {
		return
	}
	if i, ok := s.current.value.(isNumFlag); ok {
		return i.isNumFlag()
	}
	return
}
func (s *structFlag) IsBoolFlag() bool {
	if s.current == nil || s.current.value == nil {
		return false
	}
	if i, ok := s.current.value.(boolFlag); ok {
		return i.IsBoolFlag()
	}
	return false
}
func (f *structFlag) Type() string                 { return (&Func{first: f.first}).Signature() }
func (f *structFlag) String() (empty string)       { return }
func (f *structFlag) Set(value string) (err error) { _, err = f.set(value); return }

func (f *structFlag) set(arg string) (bool, error) {
	if f.current == nil {
		return false, errTooManyArguments
	}
	if f.current.value == nil {
		return false, errTooManyArguments
	}
	if err := f.current.value.Set(arg); err != nil {
		return false, err
	}
	if f.current.kind <= pointer {
		f.current = f.current.next
	}
	return f.current.value == nil, nil
}

func (f *structFlag) finalize() error {
	// no function arguments
	if f.current == nil {
		return nil
	}

	var v reflect.Value
	if f.current.v.IsValid() {
		v = f.current.v.Elem()
	}
	switch f.current.kind {
	case slice:
		// slices require atleast one argument
		if v.Len() == 0 {
			return errNotEnoughArguments
		}
		fallthrough
	case mapvalue:
	case pointer:
		for n := f.current; n != nil; n = n.next {
			if n.value == nil {
				break
			}
			switch n.kind {
			case variadic, mapvalue:
			case pointer:
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

type errInvalidStruct string

func (e errInvalidStruct) Error() string {
	return "invalid struct signature: " + string(e)
}

func newStructFlag(v reflect.Value) (*structFlag, error) {
	f := &structFlag{v: v}
	var args *arg
	for i, in := 0, v.NumField(); i < in; i++ {
		t := parseFieldFlag(v.Type().Field(i))
		if t == nil {
			continue
		}
		if f.current == nil {
			f.current = new(arg)
			f.first = f.current
			args = f.current
		}

		args.v = v.Field(i).Addr()
		nv, err := newValue(args.v.Interface())
		if err != nil {
			return nil, err
		}
		args.value = tagValue{Value: nv, typ: t.typ}

		switch args.v.Elem().Kind() {
		case reflect.Slice:
			if i != in-1 {
				return nil, errInvalidStruct(
					"slice as non-final field",
				)
			}
			args.kind = slice
		case reflect.Map:
			if i != in-1 {
				return nil, errInvalidStruct(
					"map as non-final field",
				)
			}
			args.kind = mapvalue
		case reflect.Ptr:
			args.kind = pointer
		}
		args.next = new(arg)
		args = args.next
	}
	return f, nil
}

type tagValue struct {
	Value
	typ string
}

func (t tagValue) isNumFlag() (_ numKind) {
	if f, ok := t.Value.(isNumFlag); ok {
		return f.isNumFlag()
	}
	return
}
func (t tagValue) IsBoolFlag() bool {
	if f, ok := t.Value.(boolFlag); ok {
		return f.IsBoolFlag()
	}
	return false
}
func (t tagValue) Type() string {
	if t.typ != "" {
		return t.typ
	}
	return t.Value.Type()
}

var flagValueType = reflect.TypeOf((*flag.Value)(nil)).Elem()

// NewValue returns the Value interface for most basic types including
// structs and functions.
func NewValue(v interface{}) Value {
	fv, err := newValue(v)
	if err != nil {
		panic(err)
	}
	return fv
}

var errNonPointerInterface = errors.New("interface is not a pointer to a value")

func newValue(v interface{}) (Value, error) {
	switch iv := v.(type) {
	case Value:
		return iv, nil
	case flag.Value:
		return flagValue{iv}, nil
	case *string:
		return (*stringValue)(iv), nil
	case *bool:
		if iv == nil || !*iv {
			return (*boolValue)(iv), nil
		}
		return (*boolInverse)(iv), nil
	}

	rv := reflect.ValueOf(v)
	switch rv.Kind() {
	case reflect.Ptr:
	case reflect.Func:
		return funcFlag{NewFunc(v)}, nil
	default:
		return nil, errNonPointerInterface
	}

	switch re := rv.Elem(); re.Kind() {
	case reflect.Ptr:
		return pointerValue{re}, nil
	case reflect.Slice:
		return sliceValue{re}, nil
	case reflect.Map:
		return mapValue{re}, nil
	case reflect.Func:
		return funcFlag{NewFunc(re.Interface())}, nil
	case reflect.Struct:
		return newStructFlag(re)
	case reflect.Complex64, reflect.Complex128:
		return strconvComplex{strconvValue{re}}, nil
	case reflect.Bool:
		return strconvBool{strconvValue{re}}, nil
	default:
		return strconvValue{re}, nil
	}

	// Not implemented, unreachable.
	// reflect.Interface, reflect.Chan, reflect.Array
	// panic(fmt.Sprintf("not implemented: %s", rv.Elem().Kind()))
}

type structTag struct {
	long  string
	short string
	auto  bool
	desc  string
	typ   string
}

func parseFieldFlag(v reflect.StructField) (t *structTag) {
	if t = parseFieldTag(v, true); t != nil {
		t.typ = t.long
	}
	return
}

func parseFieldTag(v reflect.StructField, raw bool) *structTag {
	const flagTag = "flag"
	if raw {
		return parseStructTag(normalize(v.Name), string(v.Tag))
	}
	return parseStructTag(normalize(v.Name), v.Tag.Get(flagTag))
}

func parseStructTag(name, tag string) *structTag {
	if tag == "-" {
		return nil
	}

	st := &structTag{auto: true, long: name}
	if tag == "" {
		return st
	}
	if tag[0] == ';' {
		st.desc = tag[1:]
		return st
	}

	var data string
	if i := strings.IndexByte(tag, ';'); i != -1 && tag[i-1] != '\\' {
		data, st.desc = tag[:i], tag[i+1:]
	} else {
		st.desc = tag
		return st
	}
	if data == "" {
		return st
	}

	st.auto = false
	if i := strings.IndexByte(data, ','); i == -1 {
		st.long = data
		st.auto = len(data) > 1
	} else {
		st.short, st.long = data[:i], data[i+1:]
	}
	if len(st.short) == 0 && len(st.long) == 1 {
		st.short, st.long = st.long, ""
	}
	if i := strings.IndexByte(st.long, ','); i != -1 {
		st.typ, st.short, st.long = st.short, st.long[:i], st.long[i+1:]
	}

	return st
}

func (f *FlagSet) addTag(t *structTag, v Value) (err error) {
	fl := &Flag{
		Value: tagValue{Value: v, typ: t.typ},
		Desc:  t.desc,
	}
	_, ok := v.(*boolInverse)
	if len(t.long) > 1 {
		if ok && !strings.HasPrefix(t.long, "no-") {
			fl.Long = []string{"no-" + t.long}
		} else {
			fl.Long = []string{t.long}
		}
	}
	if len(t.short) > 1 {
		s, err := f.next(t.short)
		if err != nil {
			return err
		}
		fl.Short = []rune{s}
	} else if len(t.short) == 1 {
		fl.Short = []rune(t.short)[:1]
	}
	if t.auto {
		s, err := f.next(t.long)
		if err != nil {
			return err
		}
		fl.Short = []rune{s}
	}
	return f.add(fl)
}

func normalize(name string) string {
	var (
		j, k int
		l    bool
	)
	r := []rune(name)
	for k = len(r) - 1; k > 0; k-- {
		if !unicode.IsUpper(r[k]) {
			break
		}
	}
	if k == 0 {
		return strings.ToLower(name)
	}
	b := new(strings.Builder)
	for i := range r[:k+1] {
		if i == 0 {
			b.WriteRune(unicode.ToLower(r[i]))
			continue
		}
		if r[i] == '_' {
			continue
		}
		u := i == len(r)-1
		if i < len(r)-1 {
			u = unicode.IsUpper(r[i+1]) || r[i+1] == '_'
		}
		if l == u {
			b.WriteRune(unicode.ToLower(r[i]))
			continue
		}
		if j > 0 && l != u {
			b.WriteRune('-')
			j = 0
		} else {
			j++
		}
		l = u
		b.WriteRune(unicode.ToLower(r[i]))
	}
	k++
	if k < len(name)-2 {
		b.WriteRune('-')
	}
	b.WriteString(strings.ToLower(string(r[k:])))
	return b.String()
}

func (f *FlagSet) loadStruct(v reflect.Value, raw bool) (err error) {
	for i := 0; i < v.NumField(); i++ {
		rf := v.Field(i)
		if !rf.CanSet() {
			continue
		}
		fi := parseFieldTag(v.Type().Field(i), raw)
		if fi == nil {
			continue
		}
		switch rf.Kind() {
		case reflect.Uintptr, reflect.UnsafePointer:
			// not handled
		case reflect.Struct:
			if !reflect.PtrTo(rf.Type()).Implements(flagValueType) {
				err = f.loadStruct(rf, raw)
				break
			}
			fallthrough
		default:
			var nv Value
			nv, err = newValue(rf.Addr().Interface())
			if err == nil {
				err = f.addTag(fi, nv)
			}
		}
		if err != nil {
			break
		}
	}
	return
}

func (f *FlagSet) load(v interface{}, raw bool) error {
	rv := reflect.ValueOf(v)
	if !rv.IsValid() {
		return nil
	}
	if rv.Kind() != reflect.Ptr {
		return errors.New("non-pointer value")
	}
	if rv = rv.Elem(); rv.Kind() != reflect.Struct {
		return errors.New("non-struct pointer")
	}
	return f.loadStruct(rv, raw)
}

// Load uses runtime reflection to set long and short options for f.
// The struct tag "flag" can be used to describe and modify the option names.
func (f *FlagSet) Load(v interface{}) {
	if err := f.load(v, false); err != nil {
		panic(err)
	}
}

// LoadRaw is the same as Load except the struct tag is parsed as-is.
func (f *FlagSet) LoadRaw(v interface{}) {
	if err := f.load(v, true); err != nil {
		panic(err)
	}
}
