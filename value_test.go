package flagopt

import (
	"reflect"
	"testing"
)

func TestParseTag(t *testing.T) {
	for _, v := range []struct {
		name string
		tag  string
		out  *structTag
	}{
		{tag: `Description\; foo, bar`, name: "Foo", out: &structTag{
			auto: true, long: "Foo", desc: `Description\; foo, bar`,
		}},
		{tag: `;Description; foo, bar`, name: "Foo", out: &structTag{
			auto: true, long: "Foo", desc: `Description; foo, bar`,
		}},
		{tag: "long;Description", out: &structTag{
			auto: true, long: "long", desc: "Description",
		}},
		{tag: ",long;Description", out: &structTag{
			long: "long", desc: "Description",
		}},
		{tag: "s;Description", out: &structTag{
			short: "s", desc: "Description",
		}},
		{tag: "s,long;Description", out: &structTag{
			long: "long", short: "s", desc: "Description",
		}},
		{tag: "type,short,long;Description", out: &structTag{
			typ: "type", long: "long", short: "short", desc: "Description",
		}},
		{tag: "-", out: nil},
	} {
		out := parseStructTag(v.name, v.tag)
		if v.out == nil {
			if out != nil {
				t.Errorf("unexpected non-nil output: %#v", *out)
			}
			continue
		}
		if *out != *v.out {
			t.Errorf("parseStructTag(%q, %q):\nwant %#v\nhave %#v",
				v.name, v.tag, *v.out, *out,
			)
		}
	}
}

func TestNormalize(t *testing.T) {
	for _, v := range []struct {
		in  string
		out string
	}{
		{in: "FOO", out: "foo"},
		{in: "FOO_BAR", out: "foo-bar"},
		{in: "FooBAR", out: "foo-bar"},
		{in: "FooBar", out: "foo-bar"},
		{in: "FOOBar", out: "foo-bar"},
		{in: "FOOBarBAZ", out: "foo-bar-baz"},
		{in: "FooBARBaz", out: "foobar-baz"},
		{in: "IPAddress", out: "ip-address"},
		{in: "IP_Address", out: "ip-address"},
		{in: "Ip_Address", out: "ip-address"},
		{in: "HTTPServerProtocolType", out: "http-server-protocol-type"},
		{in: "HTTPServerProtocolTYPE", out: "http-server-protocol-type"},
		{in: "RootFS", out: "rootfs"},
		{in: "BugURL", out: "bug-url"},
	} {
		have := normalize(v.in)
		if have != v.out {
			t.Errorf("normalize(%q): want %q != have %q", v.in, v.out, have)
		}
	}
}

func TestAddTag(t *testing.T) {
	for _, v := range []struct {
		name string
		in   interface{}
		out  interface{}
		fv   Value
		tag  *structTag
	}{
		{name: "long", out: "foo", tag: &structTag{long: "foo"}},
		{name: "long-bool", out: "no-foo", tag: &structTag{long: "foo"},
			fv: new(boolInverse)},

		{name: "short", out: 'f', tag: &structTag{short: "f"}},
		{name: "short-next", in: 'f', out: []rune{'f', 'F'},
			tag: &structTag{short: "foo"}},

		{name: "long+short",
			in:  []interface{}{'f', "foo"},
			out: []interface{}{'f', 'F', "foo", "bar"},
			tag: &structTag{
				short: "foo",
				long:  "bar",
			},
		},

		{name: "auto",
			in:  'f',
			out: []interface{}{'f', 'F', "foo"},
			tag: &structTag{
				long: "foo",
				auto: true,
			},
		},
	} {
		t.Run(v.name, func(t *testing.T) {
			var (
				fs  *FlagSet
				err error
			)
			if v.in == nil {
				fs = new(FlagSet)
			} else {
				fs, err = flagSetWith(v.in)
			}
			if err != nil {
				t.Fatalf("flagset error: %v", err)
			}
			if err := fs.addTag(v.tag, v.fv); err != nil {
				t.Fatalf("addTag(%#v): %v", *v.tag, err)
			}
			checkFlags(t, fs, v.out)
		})
	}
}

func testValueNoEqual(t *testing.T, i interface{}, args ...string) Value {
	t.Helper()
	nv, err := newValue(i)
	if err != nil {
		t.Fatalf("newValue() error: %v", err)
	}
	for _, arg := range args {
		if err := nv.Set(arg); err != nil {
			t.Fatalf("Set(%q): %v", arg, err)
		}
	}
	return nv
}

func testValueType(t *testing.T, i, v interface{}, args ...string) Value {
	t.Helper()
	nv, err := newValue(i)
	if err != nil {
		t.Fatalf("newValue() error: %v", err)
	}
	for _, arg := range args {
		if err := nv.Set(arg); err != nil {
			t.Fatalf("Set(%q): %v", arg, err)
		}
	}
	if !reflect.DeepEqual(i, v) {
		t.Fatalf("invalid value, want != have\n%#v\n%#v",
			reflect.Indirect(reflect.ValueOf(v)),
			reflect.Indirect(reflect.ValueOf(i)),
		)
	}
	return nv
}

// testFlagValue is same as testFlag but does not implement the Type interface.
type testFlagValue struct {
	b   bool
	set bool
	arg string
}

func (t *testFlagValue) Set(v string) (empty error) { t.arg, t.set = v, true; return }
func (t *testFlagValue) String() (empty string)     { return }
func (t *testFlagValue) IsBoolFlag() bool           { return t.b }

func TestValueTypes(t *testing.T) {
	t.Run("string", func(t *testing.T) {
		var a, b string = "", "foo"
		v := testValueType(t, &a, &b, b)
		if _, ok := v.(*stringValue); !ok {
			t.Fatalf("unexpected value type: %#v", v)
		}
	})
	t.Run("bool", func(t *testing.T) {
		var a, b bool = false, true
		v := testValueType(t, &a, &b, "true")
		if _, ok := v.(*boolValue); !ok {
			t.Fatalf("unexpected value type: %T", v)
		}
	})
	t.Run("invert", func(t *testing.T) {
		var a, b bool = true, false
		v := testValueType(t, &a, &b, "true")
		if _, ok := v.(*boolInverse); !ok {
			t.Fatalf("unexpected value type: %T", v)
		}
	})
	t.Run("flag", func(t *testing.T) {
		var a, b testFlagValue
		b.arg, b.set = "arg", true
		v := testValueType(t, &a, &b, "arg")
		if _, ok := v.(flagValue); !ok {
			t.Fatalf("unexpected value type: %T", v)
		}
	})
	t.Run("value", func(t *testing.T) {
		var a, b testFlag
		b.arg, b.set = "arg", true
		v := testValueType(t, &a, &b, "arg")
		if _, ok := v.(*testFlag); !ok {
			t.Fatalf("unexpected value type: %T", v)
		}
	})
	t.Run("pointer", func(t *testing.T) {
		var a, b **string
		b = new(*string)
		*b = new(string)
		**b = "arg"
		testValueType(t, &a, &b, "arg")
	})
	t.Run("unset-pointer", func(t *testing.T) {
		var a, b **string
		v := testValueType(t, &a, &b)
		_ = v.String()
		_ = v.Type()
		if b != nil {
			t.Fatalf("pointer modified")
		}
	})
	t.Run("slice-ptr", func(t *testing.T) {
		var a, b []*string
		for _, v := range []string{"foo", "bar", "baz"} {
			v := v
			b = append(b, &v)
		}
		testValueType(t, &a, &b, "foo", "bar", "baz")
	})
	t.Run("map-ptr", func(t *testing.T) {
		var a map[**string]**string
		b := map[string]string{
			"foo": "100",
			"bar": "200",
			"baz": "300",
		}
		testValueNoEqual(t, &a, "foo=100", "bar=200", "baz=300")
		if len(a) != len(b) {
			t.Errorf("map: length mismatch want %d != have %d", len(b), len(a))
		}
		np := make(map[string]string)
		for k, v := range a {
			if k == nil || v == nil {
				t.Fatal("unexpected nil key/value")
			}
			np[**k] = **v
		}
		if !reflect.DeepEqual(np, b) {
			t.Errorf("map: value mismatch want != have\n%q\n%q", b, np)
		}
	})
	t.Run("func", func(t *testing.T) {
		// TODO: Function value separation for flags is currently
		// implemented by splitting the argument by ","
		// This could be improved by making the option parser
		// deal with the setFinalizer interface.
		type in struct{ A, B string }
		var a, b in
		testValueNoEqual(t, func(v in) { a = v }, "foo,bar")

		b = in{A: "foo", B: "bar"}
		if !reflect.DeepEqual(a, b) {
			t.Errorf("func: value mismatch want != have\n%#v\n%#v", a, b)
		}
	})
	t.Run("non-pointer", func(t *testing.T) {
		_, err := newValue("not a pointer")
		if err != errNonPointerInterface {
			t.Fatalf("unexpected error: %v", err)
		}
	})
}

func makeFuncFlag(t *testing.T, v interface{}) funcFlag {
	t.Helper()
	fn, err := newFunc(v)
	if err != nil {
		t.Fatalf("newFunc(): %v", err)
	}
	return funcFlag{fn}
}

func TestFuncFlag(t *testing.T) {
	t.Run("bool-empty", func(t *testing.T) {
		var ok bool
		fv := makeFuncFlag(t, func() { ok = true })
		if !fv.IsBoolFlag() {
			t.Fatalf("func not bool")
		}
		if err := fv.Set("true"); err != nil {
			t.Fatalf("Set(): %v", err)
		}
		if !ok {
			t.Fatalf("func not called")
		}
	})
	t.Run("bool-variadic", func(t *testing.T) {
		var ok bool
		fv := makeFuncFlag(t, func(v ...string) { ok = true })
		if !fv.IsBoolFlag() {
			t.Fatalf("func not bool")
		}
		if err := fv.Set("true"); err != nil {
			t.Fatalf("Set(): %v", err)
		}
		if !ok {
			t.Fatalf("func not called")
		}
	})
	t.Run("args", func(t *testing.T) {
		want := []string{"foo", "bar", "baz"}
		var have []string
		fv := makeFuncFlag(t, func(a, b, c string) {
			have = append(have, a, b, c)
		})
		if err := fv.Set("foo,bar,baz"); err != nil {
			t.Fatalf("Set(): %v", err)
		}
		if !reflect.DeepEqual(want, have) {
			t.Fatalf("func args mismatch: want != have\n%q\n%q", want, have)
		}
	})
}

func testStructFlag(t *testing.T, v interface{}, args ...string) *structFlag {
	t.Helper()
	rv := reflect.ValueOf(v)
	fv, err := newStructFlag(rv.Elem())
	if err != nil {
		t.Fatalf("newStructFlag(): %v", err)
	}
	for _, arg := range args {
		_, err := fv.set(arg)
		if err != nil {
			t.Fatalf("set(%q): %v", arg, err)
		}
	}
	if err := fv.finalize(); err != nil {
		t.Fatalf("finalize(): %v", err)
	}
	return fv
}

func TestStructFlag(t *testing.T) {
	t.Run("args", func(t *testing.T) {
		type st struct{ A, B string }
		var a, b st
		b.A, b.B = "foo", "bar"
		testStructFlag(t, &a, "foo", "bar")
		if a != b {
			t.Fatalf("struct want != have\n%#v\n%#v", a, b)
		}
	})
	t.Run("args-ptr", func(t *testing.T) {
		type st struct{ A, B *string }
		var a, b st
		a1, a2 := "foo", "bar"
		b.A, b.B = &a1, &a2
		testStructFlag(t, &a, "foo", "bar")
		if !reflect.DeepEqual(a, b) {
			t.Fatalf("struct want != have\n%#v\n%#v", a, b)
		}
	})
	t.Run("args-ptr-optional", func(t *testing.T) {
		type st struct{ A, B *string }
		var a, b st
		a1 := "foo"
		b.A = &a1
		testStructFlag(t, &a, "foo")
		if !reflect.DeepEqual(a, b) {
			t.Fatalf("struct want != have\n%#v\n%#v", a, b)
		}
	})
	t.Run("slice", func(t *testing.T) {
		type st struct{ A []string }
		var a, b st
		b.A = []string{"foo", "bar", "baz"}
		testStructFlag(t, &a, "foo", "bar", "baz")
		if !reflect.DeepEqual(a, b) {
			t.Fatalf("struct want != have\n%#v\n%#v", a, b)
		}
	})
	t.Run("map", func(t *testing.T) {
		type st struct{ A map[string]string }
		var a, b st
		b.A = map[string]string{"foo": "bar", "baz": "arg"}
		testStructFlag(t, &a, "foo=bar", "baz=arg")
		if !reflect.DeepEqual(a, b) {
			t.Fatalf("struct want != have\n%#v\n%#v", a, b)
		}
	})
	t.Run("invalid-slice", func(t *testing.T) {
		var st struct {
			A []string
			B string
		}
		_, err := newStructFlag(reflect.ValueOf(&st).Elem())
		if err == nil {
			t.Errorf("unexpected non-nil error: %v", err)
		}
	})
	t.Run("invalid-map", func(t *testing.T) {
		var st struct {
			A map[string]string
			B string
		}
		_, err := newStructFlag(reflect.ValueOf(&st).Elem())
		if err == nil {
			t.Errorf("unexpected non-nil error: %v", err)
		}
	})
	t.Run("ignore", func(t *testing.T) {
		type st struct {
			A string
			// go vet warning
			// Not used by reflect.StructTag.Get, valid syntax.
			I string `-`
			B string
		}
		var a, b st
		b.A, b.B = "foo", "bar"
		testStructFlag(t, &a, "foo", "bar")
		if !reflect.DeepEqual(a, b) {
			t.Fatalf("struct want != have\n%#v\n%#v", a, b)
		}
	})
}

func TestValueConv(t *testing.T) {
	t.Run("int", func(t *testing.T) {
		type T int
		var a, b T = 0, -123
		testValueType(t, &a, &b, "-123")
	})
	t.Run("uint", func(t *testing.T) {
		type T uint
		var a, b T = 0, 123
		testValueType(t, &a, &b, "123")
	})
	t.Run("float", func(t *testing.T) {
		type T float64
		var a, b T = 0, -123.5
		testValueType(t, &a, &b, "-123.5")
	})
	t.Run("complex", func(t *testing.T) {
		type T complex128
		var a, b T = 0, 2i
		testValueType(t, &a, &b, "2i")
	})
	t.Run("bool", func(t *testing.T) {
		type T bool
		var a, b T = false, true
		testValueType(t, &a, &b, "true")
	})
	t.Run("string", func(t *testing.T) {
		type T string
		var a, b T = "", "foo"
		testValueType(t, &a, &b, "foo")
	})
	t.Run("func", func(t *testing.T) {
		var set string
		type T func(string)
		var a T = func(v string) { set = v }
		testValueNoEqual(t, &a, "foo")
		if set != "foo" {
			t.Fatalf("unset value from func")
		}
	})
}

func TestLoadStruct(t *testing.T) {
	type T struct {
		Foo string
		bar string //lint:ignore U1000 false positive
		Bar struct {
			Bar string
		}
		Baz     testFlag
		Ignored testFlag `flag:"-"`
	}
	t.Run("load", func(t *testing.T) {
		var st T
		fs := new(FlagSet)
		err := fs.loadStruct(reflect.ValueOf(&st).Elem(), false)
		if err != nil {
			t.Fatalf("loadStruct(): %v", err)
		}
		checkFlags(t, fs, "foo", "bar", "baz")
	})
	t.Run("parse", func(t *testing.T) {
		var st, out T
		fs := new(FlagSet)
		err := fs.loadStruct(reflect.ValueOf(&st).Elem(), false)
		if err != nil {
			t.Fatalf("loadStruct(): %v", err)
		}
		out.Foo, out.Bar.Bar = "foo", "bar"
		out.Baz.arg, out.Baz.set = "baz", true
		if _, _, err := fs.Parse([]string{
			"--foo", "foo",
			"--bar", "bar",
			"--baz", "baz",
		}); err != nil {
			t.Fatalf("Parse(): %v", err)
		}
		if st != out {
			t.Fatalf("invalid value: want != have\n%#v\n%#v", out, st)
		}
	})
}

func TestMapValue(t *testing.T) {
	t.Run("slice", func(t *testing.T) {
		var v map[string][]string
		fv := NewValue(&v)
		fv.Set("foo=bar")
		fv.Set("foo=baz")
		if !reflect.DeepEqual(v["foo"], []string{"bar", "baz"}) {
			t.Fatalf("%#v", v)
		}
	})
	t.Run("map", func(t *testing.T) {
		var v map[string]map[string]string
		fv := NewValue(&v)
		fv.Set("foo=bar=1")
		fv.Set("foo=baz=2")
		if !reflect.DeepEqual(v["foo"], map[string]string{"bar": "1", "baz": "2"}) {
			t.Fatalf("%#v", v)
		}
	})
}
