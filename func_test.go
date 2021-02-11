package flagopt

import (
	"errors"
	"reflect"
	"strconv"
	"testing"
)

func testFunc(t *testing.T, name string, fn interface{}, args ...string) {
	v, err := newFunc(fn)
	if err != nil {
		t.Fatalf("newFunc(%s) error %v", name, err)
	}
	if _, err := v.set(args...); err != nil {
		t.Fatalf("%s: set() error: %v", name, err)
	}
	if err := v.Call(); err != nil {
		t.Fatalf("%s: Call() error: %v", name, err)
	}
}

func TestFuncOptional(t *testing.T) {
	t.Run("empty", func(t *testing.T) {
		testFunc(t, "empty", func(i0 *string) {
			if i0 != nil {
				t.Fatal("unexpected non-nil argument")
			}
		})
	})
	t.Run("full", func(t *testing.T) {
		arg := "foo"
		testFunc(t, "full", func(i0 *string) {
			if i0 == nil {
				t.Fatal("unexpected nil argument")
			}
			if *i0 != arg {
				t.Fatalf("have %q != want %q",
					*i0, arg)
			}
		}, arg)
	})
	t.Run("partial", func(t *testing.T) {
		in := []string{"a", "b"}
		testFunc(t, "partial", func(i0, i1, i2 *string) {
			for i, v := range []*string{i0, i1} {
				if v == nil {
					t.Fatalf("arg(%d) is nil", i)
				}
				if have, want := *v, in[i]; have != want {
					t.Fatalf("arg(%d) have %q != want %q",
						i, have, want,
					)
				}
			}
			if i2 != nil {
				t.Fatalf("arg(i2) is not nil")
			}
		}, in...)
	})
	t.Run("mixed", func(t *testing.T) {
		i3a := 123
		in := []string{"a", "b", "c", strconv.Itoa(i3a)}
		testFunc(t, "mixed", func(i0, i1, i2 *string, i3 int) {
			for i, v := range []*string{i0, i1, i2} {
				if v == nil {
					t.Fatalf("arg(%d) is nil", i)
				}
				if have, want := *v, in[i]; have != want {
					t.Fatalf("arg(%d) have %q, want %q",
						i, have, want,
					)
				}
			}
			if i3 != i3a {
				t.Fatalf("arg(3) have %d, want %d", i3, i3a)
			}
		}, in...)
	})
}

func TestFunc(t *testing.T) {
	t.Run("slice", func(t *testing.T) {
		in := []string{"a", "b", "c"}
		testFunc(t, "slice", func(i0 []string) {
			for i, v := range i0 {
				if have, want := v, in[i]; have != want {
					t.Fatalf("idx(%d) have %q != want %q",
						i, have, want,
					)
				}
			}
		}, in...)
	})
	t.Run("variadic full", func(t *testing.T) {
		in := []string{"a", "b", "c"}
		testFunc(t, "variadic", func(i0 ...string) {
			if i0 == nil {
				t.Fatal("i0 is nil")
			}
			for i, v := range i0 {
				if have, want := v, in[i]; have != want {
					t.Fatalf("idx(%d) have %q != want %q",
						i, have, want,
					)
				}
			}
		}, in...)
	})
	t.Run("variadic empty", func(t *testing.T) {
		i0v := "variadic"
		testFunc(t, "variadic", func(i0 string, iv ...string) {
			if i0 != i0v {
				t.Fatalf("i0v want %q != have %q", i0v, i0)
			}
			if len(iv) != 0 {
				t.Fatalf("variadic iv is not empty: %q", i0)
			}
		}, i0v)
	})
	t.Run("value", func(t *testing.T) {
		arg := "test"
		testFunc(t, "value", func(v testFlag) {
			if v.arg != arg {
				t.Fatalf("want %q != have %q", arg, v.arg)
			}
		}, arg)
	})
	t.Run("error", func(t *testing.T) {
		want := errors.New("error")
		v, err := newFunc(func() error { return want })
		if err != nil {
			t.Fatalf("newFunc() error: %v", err)
		}
		if have := v.Call(); have != want {
			t.Fatalf("have %v != want %v", have, want)
		}
	})
	t.Run("map", func(t *testing.T) {
		want := map[string]string{
			"foo": "1",
			"bar": "2",
			"baz": "3",
		}
		testFunc(t, "map", func(i0 map[string]string) {
			if i0 == nil {
				t.Fatalf("unexpected nil map")
			}
			if !reflect.DeepEqual(i0, want) {
				t.Fatalf("have != want\n%q\n%q", i0, want)
			}
		}, "foo=1", "bar=2", "baz=3")
	})
	t.Run("combined", func(t *testing.T) {
		want := map[string]string{
			"foo": "1",
			"bar": "2",
			"baz": "3",
		}
		testFunc(t, "map", func(i0 string, i1 map[string]string) {
			if i0 != "arg" {
				t.Fatalf("i0 want %q != have %q", "arg", i0)
			}
			if i1 == nil {
				t.Fatalf("unexpected nil map")
			}
			if !reflect.DeepEqual(i1, want) {
				t.Fatalf("have != want\n%q\n%q", i1, want)
			}
		}, "arg", "foo=1", "bar=2", "baz=3")
	})
}

type testError struct{}

func (testError) Error() string { return "testError" }

func TestInvalidFunc(t *testing.T) {
	for _, v := range []struct {
		name string
		err  error
		fn   interface{}
	}{
		{name: "non-final-slice", err: errNonFinalSlice,
			fn: func([]string, string) {}},
		{name: "non-final-map", err: errNonFinalMap,
			fn: func(map[string]string, string) {}},
		{name: "multi-return", err: errMultipleReturn,
			fn: func() (_ error, _ error) { return }},
		{name: "return-not-error", err: errReturnNotError,
			fn: func() (_ int) { return }},
		{name: "non-err-return", err: nil,
			fn: func() (_ testError) { return }},
	} {
		t.Run(v.name, func(t *testing.T) {
			_, err := newFunc(v.fn)
			if !errors.Is(err, v.err) {
				t.Errorf("unexpected error: want != have\n%v\n%v",
					v.err, err)
			}
		})
	}
}

type testSetFinalizer struct {
	testFlag
	in        []string
	finalized bool
}

func (t *testSetFinalizer) set(v string) (_ bool, _ error) { t.in = append(t.in, v); return }
func (t *testSetFinalizer) finalize() (empty error)        { t.finalized = true; return }

var _ setFinalizer = (*testSetFinalizer)(nil)

func TestFuncFinalize(t *testing.T) {
	t.Run("slice", func(t *testing.T) {
		fn, err := newFunc(func([]string) {})
		if err != nil {
			t.Fatalf("newFunc(): error %v", err)
		}
		err = fn.Call()
		if !errors.Is(err, errNotEnoughArguments) {
			t.Fatalf("Call(): unexpected error %v", err)
		}
	})
	t.Run("pointer", func(t *testing.T) {
		// When a non-pointer is after a pointer all arguments up
		// to are not optional.
		fn, err := newFunc(func(
			*string, // non-optional pointer
			string, // because of this
			*string, // optional
		) {
		})
		if err != nil {
			t.Fatalf("newFunc(): error %v", err)
		}
		err = fn.Call()
		if !errors.Is(err, errNotEnoughArguments) {
			t.Fatalf("Call(): unexpected error %v", err)
		}
	})
	t.Run("pointer-error", func(t *testing.T) {
		fn, err := newFunc(func(
			string, // required
			*string, // non-optional
			string, // because of this
		) {
		})
		if err != nil {
			t.Fatalf("newFunc(): error %v", err)
		}
		ok, err := fn.set("1")
		if err != nil {
			t.Fatalf("set(): error %v", err)
		}
		if ok {
			t.Fatalf("set(): unexpected ok")
		}
		err = fn.Call()
		if !errors.Is(err, errNotEnoughArguments) {
			t.Fatalf("Call(): unexpected error %v", err)
		}
	})
	t.Run("no-arguments", func(t *testing.T) {
		fn, err := newFunc(func(string) {})
		if err != nil {
			t.Fatalf("newFunc(): error %v", err)
		}
		err = fn.Call()
		if !errors.Is(err, errNotEnoughArguments) {
			t.Fatalf("Call(): unexpected error %v", err)
		}
	})
	t.Run("empty-func", func(t *testing.T) {
		fn, err := newFunc(func() {})
		if err != nil {
			t.Fatalf("newFunc(): error %v", err)
		}
		_, err = fn.set("arg")
		if !errors.Is(err, errTooManyArguments) {
			t.Fatalf("Set(): unexpected error %v", err)
		}
	})
	t.Run("too-many-args", func(t *testing.T) {
		fn, err := newFunc(func(string) {})
		if err != nil {
			t.Fatalf("newFunc(): error %v", err)
		}
		_, err = fn.set("arg1", "arg2")
		if !errors.Is(err, errTooManyArguments) {
			t.Fatalf("Set(): unexpected error %v", err)
		}
	})
	t.Run("iterator", func(t *testing.T) {
		var have testSetFinalizer
		fn, err := newFunc(func(v testSetFinalizer) { have = v })
		if err != nil {
			t.Fatalf("newFunc(): error %v", err)
		}
		args := []string{"foo", "bar", "baz"}
		ok, err := fn.set(args...)
		if err != nil {
			t.Fatalf("set(): error %v", err)
		}
		if ok {
			t.Fatalf("set(): unexpected ok")
		}
		if err := fn.Call(); err != nil {
			t.Fatalf("Call(): error %v", err)
		}
		want := testSetFinalizer{finalized: true, in: args}
		if !reflect.DeepEqual(want, have) {
			t.Fatalf("finalizer: want != have\n%#v\n%#v", want, have)
		}
	})
}

func testFuncSignature(t *testing.T, sig string, fn interface{}) {
	t.Helper()
	v, err := newFunc(fn)
	if err != nil {
		t.Fatalf("newFunc(): error %v", err)
	}
	have := v.Signature()
	if sig != have {
		t.Fatalf("Signature(): want != have\n%q\n%q", sig, have)
	}
}

func (t *testFlag) Type() string { return "T" }

func TestFuncSignature(t *testing.T) {
	for _, v := range []struct {
		name string
		sig  string
		fn   interface{}
	}{
		{name: "empty", sig: "",
			fn: func() {}},
		{name: "single", sig: "T",
			fn: func(testFlag) {}},
		{name: "dual", sig: "T T",
			fn: func(_, _ testFlag) {}},
		{name: "variadic", sig: "[T...]",
			fn: func(...testFlag) {}},
		{name: "slice", sig: "T...",
			fn: func([]testFlag) {}},
		{name: "map", sig: "[T=T...]",
			fn: func(map[testFlag]testFlag) {}},
		{name: "pointer", sig: "[T]",
			fn: func(*testFlag) {}},
		{name: "single+variadic", sig: "T [T...]",
			fn: func(testFlag, ...testFlag) {}},
		{name: "variadic-pointer", sig: "[T...]",
			fn: func(...*testFlag) {}},
	} {
		t.Run(v.name, func(t *testing.T) {
			testFuncSignature(t, v.sig, v.fn)
		})
	}
}
