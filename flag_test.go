package flagopt

import (
	"errors"
	"flag"
	"reflect"
	"sort"
	"testing"
)

func TestLookup(t *testing.T) {
	keys := []string{"foo", "bar", "baz"}
	sort.Strings(keys)
	for i, v := range []struct {
		prefix string
		ps     []string
		i      int
	}{
		{prefix: "b", i: 0, ps: []string{"bar", "baz"}},
		{prefix: "baz", i: 1, ps: []string{"baz"}},
		{prefix: "f", i: 2, ps: []string{"foo"}},
		{prefix: "foo", i: 2, ps: []string{"foo"}},
		{prefix: "no-match", i: 3, ps: nil},
		{prefix: "a", i: 0, ps: nil},
	} {
		ps, j := lookup(keys, v.prefix)
		if v.i != j {
			t.Errorf("lookup(%d): index mismatch want %d != have %d",
				i, j, v.i,
			)
			continue
		}
		if reflect.DeepEqual(v.ps, ps) {
			continue
		}
		t.Errorf("lookup(%d): want != have\n%q\n%q", i, v.ps, ps)
	}
}

func TestUniq(t *testing.T) {
	want := []string{"foo", "bar", "baz"}
	have := want
	for i := 0; i < 5; i++ {
		have = append(have, have...)
	}
	sort.Strings(want)
	sort.Strings(have)
	have = uniq(have)
	if !reflect.DeepEqual(want, have) {
		t.Fatalf("uniq want != have\n%q\n%q", want, have)
	}
}

func splitArgs(i ...interface{}) (r []rune, s []string) {
	for _, v := range i {
		switch t := v.(type) {
		case []rune:
			r = append(r, t...)
		case []string:
			s = append(s, t...)
		case rune:
			r = append(r, t)
		case string:
			s = append(s, t)
		case []interface{}:
			ir, is := splitArgs(t...)
			s = append(s, is...)
			r = append(r, ir...)
		case nil, bool:
		default:
			panic("splitArgs: invalid type")
		}
	}
	return
}

func makeFlag(i ...interface{}) (fl *Flag) {
	fl = new(Flag)
	fl.Short, fl.Long = splitArgs(i...)
	return
}

func makeFlagV(v flag.Value, i ...interface{}) (fl *Flag) {
	fl = makeFlag(i...)
	fl.Value = v
	return
}

func flagSetWith(i ...interface{}) (*FlagSet, error) {
	fs := new(FlagSet)
	return fs, fs.add(makeFlag(i...))
}

func checkFlags(t *testing.T, fs *FlagSet, i ...interface{}) {
	t.Helper()
	sf, lf := splitArgs(i...)
	for _, v := range sf {
		_, ok := fs.short[v]
		if !ok {
			t.Errorf("missing short option: -%s from flagset", string(v))
			continue
		}
	}
	var ll []string
	for _, v := range lf {
		_, ok := fs.long[v]
		if !ok {
			t.Errorf("missing long option: --%s from flagset", v)
			continue
		}
		ll = append(ll, v)
	}
	if t.Failed() {
		return
	}
	if !reflect.DeepEqual(ll, fs.ll) {
		t.Errorf("flagset ll mismatch: want != have\n%q\n%q", ll, fs.ll)
	}
	if len(sf)+len(lf) > 0 && len(fs.ident) == 0 {
		t.Errorf("flagset zero length ident")
	}
	for _, fl := range fs.ident {
		for _, v := range fl.Short {
			have := fs.short[v]
			if have == fl {
				continue
			}
			t.Errorf("ident short reverse mismatch: want != have"+
				"\n%#v\n%#v", fl, have)
		}
		for _, v := range fl.Long {
			have := fs.long[v]
			if have == fl {
				continue
			}
			t.Errorf("ident long reverse mismatch: want != have"+
				"\n%#v\n%#v", fl, have)
		}
	}
}

func TestFlagNext(t *testing.T) {
	fs, err := flagSetWith([]rune("foFObBaR"))
	if err != nil {
		t.Fatalf("flagset error: %v", err)
	}
	for _, v := range []struct {
		name string
		in   string
		r    rune
		err  bool
	}{
		{"add", "foo-bar", 'A', false},
		{"next", "bar", 'r', false},
		{"full", "foo", -1, true},
		{"invalid", "-", -1, true},
	} {
		t.Run(v.name, func(t *testing.T) {
			r, err := fs.next(v.in)
			if !v.err && err != nil {
				t.Errorf("unexpected error: %v", err)
				return
			} else if v.err && err == nil {
				t.Error("unexpected nil error")
				return
			}
			if r == v.r {
				fs.short[r] = nil
				return
			}
			t.Errorf("invalid next rune: w:%q != h:%q",
				string(v.r), string(r),
			)
		})
	}
}

func TestFlagAdd(t *testing.T) {
	tc := []struct {
		name string
		err  error
		in   interface{}
	}{
		{"long", nil, []string{"foo", "bar", "baz"}},
		{"short", nil, []rune{'a', 'b', 'c'}},
		{"long+short", nil, []interface{}{"foo", "bar", 'a', 'b'}},
		{"none", errNoOptions, nil},
	}
	for _, v := range tc {
		t.Run(v.name, func(t *testing.T) {
			fs, err := flagSetWith(v.in)
			if err == v.err {
				checkFlags(t, fs, v.in)
				return
			}
			t.Errorf("flagset(%q): \nwant: %v\nhave: %v",
				v.in, v.err, err,
			)
		})
	}
	t.Run("exists", func(t *testing.T) {
		fs, err := flagSetWith("foo", 'f')
		if err != nil {
			t.Fatalf("flagset error: %v", err)
		}
		t.Run("long", func(t *testing.T) {
			err := fs.add(makeFlag("foo"))
			if err == nil {
				t.Errorf("unexpected nil error")
			}
		})
		t.Run("short", func(t *testing.T) {
			err := fs.add(makeFlag('f'))
			if err == nil {
				t.Errorf("unexpected nil error")
			}
		})
	})
}

func TestFlagSetSet(t *testing.T) {
	t.Run("long", func(t *testing.T) {
		fs := new(FlagSet)
		in := []string{"foo", "bar", "baz"}
		for _, v := range in {
			if _, err := fs.set(v, "desc", nil); err != nil {
				t.Fatalf("flagset.set(%q) error: %v", v, err)
			}
		}
		checkFlags(t, fs, in)
	})
	t.Run("short", func(t *testing.T) {
		fs := new(FlagSet)
		in := []string{"f", "b", "B"}
		for _, v := range in {
			if _, err := fs.set(v, "desc", nil); err != nil {
				t.Fatalf("flagset.set(%q) error: %v", v, err)
			}
		}
		checkFlags(t, fs, 'f', 'b', 'B')
	})
}

func TestFlagSetFlags(t *testing.T) {
	t.Run("autohelp", func(t *testing.T) {
		t.Run("unset", func(t *testing.T) {
			fs := new(FlagSet)
			fs.Add(makeFlagV(&testFlag{}, 't'))
			checkFlags(t, fs, 't')
		})
		t.Run("flag", func(t *testing.T) {
			fs := &FlagSet{flags: FlagHelp}
			fs.Add(makeFlagV(&testFlag{}, 't'))
			checkFlags(t, fs, 'h', "help", 't')
		})
		t.Run("subset", func(t *testing.T) {
			fs := &FlagSet{flags: FlagHelp}
			fn := new(FlagSet)
			fs.Register(fn, "test")
			checkFlags(t, fs, 'h', "help")
			checkFlags(t, fn)
		})
	})
}

type testFlag struct {
	b   bool
	set bool
	arg string
}

func (t *testFlag) Set(v string) (empty error) { t.arg, t.set = v, true; return }
func (t *testFlag) String() (empty string)     { return }
func (t *testFlag) IsBoolFlag() bool           { return t.b }

func mapFlagSet(t *testing.T, i ...interface{}) (
	*FlagSet, map[string]*testFlag,
) {
	fs := new(FlagSet)
	fsm := make(map[string]*testFlag)
	var lfv *testFlag
	for _, v := range i {
		fv := &testFlag{}
		switch vt := v.(type) {
		case rune:
			fsm[string(vt)] = fv
		case string:
			fsm[vt] = fv
		case bool:
			if lfv == nil {
				panic("invalid syntax")
			}
			lfv.b = vt
			lfv = nil
			continue
		default:
			panic("invalid type")
		}
		if err := fs.add(
			makeFlagV(fv, v),
		); err != nil {
			t.Fatalf("flagset error: %v", err)
		}
		lfv = fv
	}
	return fs, fsm
}

func TestFlagParse(t *testing.T) {
	t.Run("short", func(t *testing.T) {
		fs, m := mapFlagSet(t, 'a', true, 'b', 'c')
		for _, v := range []struct {
			name string
			args []string
			fv   testFlag
		}{
			{name: "a", fv: testFlag{arg: "true", set: true, b: true},
				args: []string{"-a=true"}},
			{name: "b", fv: testFlag{arg: "arg1", set: true},
				args: []string{"-barg1"}},
			{name: "c", fv: testFlag{arg: "arg2", set: true},
				args: []string{"-c", "arg2"}},
		} {
			_, _, err := fs.Parse(v.args)
			if err != nil {
				t.Errorf("%s: Parse(%q): %v", v.name, v.args, err)
				return
			}
			if a, b := v.fv, *m[v.name]; a != b {
				t.Errorf("flag mismatch %q, want != have\n%#v\n%#v", v.name, a, b)
			}
		}
	})
	t.Run("short-multi", func(t *testing.T) {
		fs, m := mapFlagSet(t, 'a', true, 'b', 'c')
		for _, v := range []struct {
			name string
			args []string
			fv   *testFlag
		}{
			{name: "ac", args: []string{"-acb"}},
			{name: "a", fv: &testFlag{arg: "true", set: true, b: true}},
			{name: "b", fv: &testFlag{}}, // unset
			{name: "c", fv: &testFlag{arg: "b", set: true}},
		} {
			var err error
			if v.args != nil {
				_, _, err = fs.Parse(v.args)
			}
			if err != nil {
				t.Errorf("%s: Parse(%q): %v", v.name, v.args, err)
				return
			}
			if v.fv == nil {
				continue
			}
			if a, b := *v.fv, *m[v.name]; a != b {
				t.Errorf("flag mismatch %q, want != have\n%#v\n%#v", v.name, a, b)
			}
		}
	})
	t.Run("short-range", func(t *testing.T) {
		type tm map[string]*testFlag
		for _, v := range []struct {
			args []string
			fv   tm
		}{
			{args: []string{"-42"}, fv: tm{
				"#": {arg: "42", set: true},
			}},
			{args: []string{"-b42"}, fv: tm{
				"#": {},
				"b": {arg: "42", set: true},
			}},
			{args: []string{"-42bc"}, fv: tm{
				"#": {arg: "42", set: true},
				"b": {arg: "c", set: true},
				"c": {},
			}},
			{args: []string{"-a42c2b"}, fv: tm{
				"a": {arg: "true", set: true, b: true},
				"#": {arg: "42", set: true},
				"c": {arg: "2b", set: true},
				"b": {},
			}},
		} {
			fs, m := mapFlagSet(t, 'a', true, 'b', 'c')
			tr := &testFlag{}
			if _, err := fs.setRange("", "", tr); err != nil {
				t.Errorf("setRange(%q): %v", v.args, err)
			}
			_, _, err := fs.Parse(v.args)
			if err != nil {
				t.Errorf("Parse(%q): %v", v.args, err)
				return
			}
			for name, fv := range v.fv {
				var vt *testFlag
				if name == "#" {
					vt = tr
				} else {
					vt = m[name]
				}
				if a, b := *fv, *vt; a != b {
					t.Errorf("flag mismatch %q, want != have\n%#v\n%#v", name, a, b)
				}
			}
		}
	})
	t.Run("long", func(t *testing.T) {
		fs, m := mapFlagSet(t,
			"foo", true,
			"bar", true,
			"baz", "b",
			"unset",
		)
		for _, v := range []struct {
			name string
			args []string
			fv   *testFlag
		}{
			{name: "foo", fv: &testFlag{arg: "true", set: true, b: true},
				args: []string{"--foo=true"}},
			{name: "bar", fv: &testFlag{arg: "true", set: true, b: true},
				args: []string{"--bar"}},
			{name: "baz", fv: &testFlag{arg: "arg1", set: true},
				args: []string{"--baz", "arg1"}},
			{name: "b", fv: &testFlag{arg: "arg2", set: true},
				args: []string{"--b=arg2"}},
			{name: "unset", fv: &testFlag{}},
		} {
			var err error
			if v.args != nil {
				_, _, err = fs.Parse(v.args)
			}
			if err != nil {
				t.Errorf("%s: Parse(%q): %v", v.name, v.args, err)
				return
			}
			if v.fv == nil {
				continue
			}
			if a, b := *v.fv, *m[v.name]; a != b {
				t.Errorf("flag mismatch %q, want != have\n%#v\n%#v", v.name, a, b)
			}
		}
	})
	t.Run("long-ambigous", func(t *testing.T) {
		fs, m := mapFlagSet(t,
			"foo", true,
			"baz", "b", true,
			"bar",
			"unset",
		)
		for _, v := range []struct {
			name string
			args []string
			fv   *testFlag
		}{
			{name: "foo", fv: &testFlag{arg: "true", set: true, b: true},
				args: []string{"--f"}},
			{name: "b", fv: &testFlag{arg: "true", set: true, b: true},
				args: []string{"--b"}},
			{name: "baz", fv: &testFlag{arg: "arg", set: true},
				args: []string{"--baz", "arg"}},
			{name: "bar", fv: &testFlag{}},
			{name: "unset", fv: &testFlag{}},
		} {
			var err error
			if v.args != nil {
				_, _, err = fs.Parse(v.args)
			}
			if err != nil {
				t.Errorf("%s: Parse(%q): %v", v.name, v.args, err)
				return
			}
			if v.fv == nil {
				continue
			}
			if a, b := *v.fv, *m[v.name]; a != b {
				t.Errorf("flag mismatch %q, want != have\n%#v\n%#v", v.name, a, b)
			}
		}
	})
	t.Run("prev-lookup", func(t *testing.T) {
		fs, m := mapFlagSet(t, "foo", 'b', "bar", "unset")
		fsn, mn := mapFlagSet(t, "foo", true, 'b', true)

		if err := fs.register(fsn, "next"); err != nil {
			t.Errorf("register(): %v", err)
		}

		args := []string{"--f=arg1", "-b=arg2", "next", "--f", "-b", "--ba", "arg3"}
		if _, _, err := fs.Parse(args); err != nil {
			t.Errorf("Parse(%q): %v", args, err)
			return
		}
		for _, v := range []struct {
			name string
			fm   map[string]*testFlag
			fv   *testFlag
		}{
			{name: "foo", fm: mn, fv: &testFlag{arg: "true", set: true, b: true}},
			{name: "b", fm: mn, fv: &testFlag{arg: "true", set: true, b: true}},

			{name: "foo", fm: m, fv: &testFlag{arg: "arg1", set: true}},
			{name: "b", fm: m, fv: &testFlag{arg: "arg2", set: true}},
			{name: "bar", fm: m, fv: &testFlag{arg: "arg3", set: true}},

			{name: "unset", fm: m, fv: &testFlag{}},
		} {
			if a, b := *v.fv, *v.fm[v.name]; a != b {
				t.Errorf("flag mismatch %q, want != have\n%#v\n%#v", v.name, a, b)
			}
		}
	})
}

type testCaller struct {
	called bool
	from   string
	argc   int
	set    []string
}

func (t *testCaller) Call() (empty error) { t.called = true; return }
func (t *testCaller) Set(v string) (bool, error) {
	if len(t.set)+1 > t.argc {
		return false, errTooManyArguments
	}
	t.set = append(t.set, v)
	return t.argc == len(t.set), nil
}
func (t *testCaller) From(v string) (bool, error) {
	t.from = v
	return t.argc == 0, nil
}

type FromCaller interface {
	From
	Caller
}

var _ FromCaller = (*testCaller)(nil)

func makeFlagSet(t *testing.T, i ...interface{}) *FlagSet {
	var (
		lc  *testCaller
		lfs *FlagSet
	)
	fs := new(FlagSet)
	for _, v := range i {
		tc := &testCaller{}
		nfs := new(FlagSet)
		switch vt := v.(type) {
		case string:
			nfs.Func(tc)
			fs.Register(nfs, vt)
		case []string:
			nfs.Func(tc)
			fs.Register(nfs, vt...)
		case int:
			if lc != nil {
				lc.argc = vt
				lc = nil
				continue
			}
			if lfs != nil {
				lfs.ct = vt
				lfs = nil
				continue
			}
			panic("invalid syntax")
		case nil:
			if lfs == nil {
				panic("invalid syntax")
			}
			lfs.cmd = nil
			lfs = nil
			continue
		default:
			panic("invalid type")
		}
		lc, lfs = tc, nfs
	}
	return fs
}

func TestFlagArg(t *testing.T) {
	t.Run("parse", func(t *testing.T) {
		in := []interface{}{
			"foo", nil,
			"bar", 2,
			"baz", 0,
			"command", 0, 3,
			"negative", 0, -1,
		}
		for _, v := range []struct {
			name            string
			args, rest, set []string
			nc              bool
		}{
			{name: "empty", nc: true,
				args: []string{""},
				rest: []string{""},
			},
			{name: "foo", nc: true,
				args: []string{"foo", "bar", "baz"},
				rest: []string{"bar", "baz"},
			},
			{name: "bar",
				args: []string{"bar", "baz", "arg", "foo"},
				set:  []string{"baz", "arg"},
				rest: []string{"foo"},
			},
			{name: "baz",
				args: []string{"baz", "arg", "--", "-a", "--b", "arg"},
				rest: []string{"arg", "-a", "--b", "arg"},
			},
			{name: "command", nc: true, // no match
				args: []string{"com", "bar"},
				rest: []string{"com", "bar"},
			},
			{name: "command",
				args: []string{"comm", "bar"},
				rest: []string{"bar"},
			},
			{name: "negative",
				args: []string{"n", "bar"},
				rest: []string{"bar"},
			},
			{name: "no-match", nc: true,
				args: []string{"b", "bar"},
				rest: []string{"b", "bar"},
			},
		} {
			fs := makeFlagSet(t, in...)
			rest, _, err := fs.Parse(v.args)
			if err != nil {
				t.Errorf("%s: Parse(%q): error %v", v.name, v.args, err)
				continue
			}
			if !reflect.DeepEqual(rest, v.rest) {
				t.Errorf("%s: Parse(%q): return args: want != have\n%q\n%q",
					v.name, v.args, v.rest, rest)
				continue
			}
			if v.nc {
				continue
			}
			var tc *testCaller
			if sl := fs.sublookup(v.name); len(sl) != 1 {
				t.Errorf("sublookup(%s): %#v", v.name, sl)
				continue
			} else {
				tc = sl[0].fs.cmd.(*testCaller)
			}
			if a, b := v.name, tc.from; a != b {
				t.Errorf("%s: From mismatch: want %q != have %q", v.name, a, b)
				continue
			}
			if a, b := v.set, tc.set; !reflect.DeepEqual(a, b) {
				t.Errorf("%s: Set mismatch: want %q != have %q", v.name, a, b)
				continue
			}
			if a, b := tc.argc, len(tc.set); a != b {
				t.Errorf("%s: missing arguments: want %d != have %d", v.name, a, b)
				continue
			}
		}
	})
	t.Run("call", func(t *testing.T) {
		var a, b, c testCaller
		fs := new(FlagSet)
		f1 := fs.New("foo", "desc")
		f1.Func(&a)
		f2 := f1.New("bar", "desc")
		f2.Func(&b)
		f3 := f2.New("baz", "desc")
		f3.Func(&c)

		if _, _, err := fs.Parse([]string{"foo", "bar", "baz"}); err != nil {
			t.Errorf("Parse(): error: %v", err)
			return
		}
		if _, err := fs.Call(); err != nil {
			t.Errorf("Call(): error: %v", err)
			return
		}
		for _, v := range []struct {
			name   string
			tc     testCaller
			called bool
		}{
			{name: "foo", tc: a, called: false},
			{name: "bar", tc: b, called: false},
			{name: "baz", tc: c, called: true},
		} {
			if v.tc.called == v.called {
				continue
			}
			t.Errorf("%s: unexpected Call()", v.name)
		}
	})
	t.Run("exec", func(t *testing.T) {
		var a, b, c testCaller
		fs := new(FlagSet)
		f1 := fs.New("foo", "desc")
		f1.Func(&a)
		f2 := f1.New("bar", "desc")
		f2.Func(&b)
		f3 := f2.New("baz", "desc")
		f3.Func(&c)

		if _, _, err := fs.Parse([]string{"foo", "bar", "baz"}); err != nil {
			t.Errorf("Parse(): error: %v", err)
			return
		}
		if err := fs.Exec(); err != nil {
			t.Errorf("Exec(): error: %v", err)
			return
		}
		for _, v := range []struct {
			name string
			tc   testCaller
		}{
			{name: "foo", tc: a},
			{name: "bar", tc: b},
			{name: "baz", tc: c},
		} {
			if v.tc.called {
				continue
			}
			t.Errorf("%s: not Called()", v.name)
		}
	})
	t.Run("caller", func(t *testing.T) {
		for _, v := range []struct {
			name string
			args []string
			ok   bool
		}{
			{name: "empty", ok: true},
			{name: "arg", args: []string{"baz"}, ok: true},
			{name: "cmd", args: []string{"bar"}},
		} {
			fs := makeFlagSet(t, "foo", "bar")
			if _, _, err := fs.Parse(v.args); err != nil {
				t.Errorf("Parse(): error: %v", err)
				continue
			}
			if ok := fs == fs.Caller(); ok == v.ok {
				continue
			}
			t.Errorf("%s: Caller() mismatch: %q", v.name, v.args)
		}
	})
}

func testRegister(t *testing.T, fs, fn *FlagSet, names ...string) {
	t.Helper()
	fm := make(map[string]*FlagSet)
	for _, v := range fs.cl {
		fm[v.name] = v.fs
	}
	for i, v := range names {
		vs, ok := fm[v]
		if !ok {
			t.Fatal("registered flagset not found")
		}
		if vs != fn {
			t.Fatal("invalid flagset")
		}
		if i > 0 {
			// alias
			continue
		}
		if fn.name != v {
			t.Fatalf("flagset name mismatch: %q", fn.name)
		}
	}
}

func TestRegister(t *testing.T) {
	t.Run("empty", func(t *testing.T) {
		fs := new(FlagSet)
		fn := new(FlagSet)
		if err := fs.register(fn, "foo"); err != nil {
			t.Fatalf("register error: %v", err)
		}
		testRegister(t, fs, fn, "foo")
	})
	t.Run("named", func(t *testing.T) {
		fs := new(FlagSet)
		fn := new(FlagSet)
		fn.name = "foo"
		if err := fs.register(fn); err != nil {
			t.Fatalf("register error: %v", err)
		}
		testRegister(t, fs, fn, "foo")
	})
	t.Run("alias", func(t *testing.T) {
		fs := new(FlagSet)
		fn := new(FlagSet)
		fn.name = "foo"
		alias := []string{"bar", "baz"}
		if err := fs.register(fn, alias...); err != nil {
			t.Fatalf("register error: %v", err)
		}
		testRegister(t, fs, fn, "foo", "bar", "baz")
		if !reflect.DeepEqual(fn.alias, alias) {
			t.Fatalf("alias mismatch: want != have\n%q\n%q",
				alias, fs.alias,
			)
		}
	})
}

type testBreakCaller struct{ testCaller }

func (t *testBreakCaller) From(string) (bool, error) { return false, BreakError{} }

type testBreakFlag struct{ testFlag }

func (t *testBreakFlag) Set(string) error { return BreakError{} }

func testBreak(t *testing.T, fs *FlagSet, args ...string) {
	t.Helper()
	rest, done, err := fs.Parse(args)
	if !done {
		t.Fatalf("Parse(%q): done != true", args)
	}
	if !errors.Is(err, BreakError{}) {
		t.Fatalf("Parse(%q): unexpected error: %v", args, err)
	}
	if a, b := args[1:], rest; !reflect.DeepEqual(a, b) {
		t.Fatalf("Parse(%q): return arguments, want != have\n%q\n%q", args, a, b)
	}
}

func TestBreak(t *testing.T) {
	t.Run("cmd", func(t *testing.T) {
		fs := new(FlagSet)
		fs.New("foo", "desc").Func(&testBreakCaller{})
		testBreak(t, fs, "foo", "-a", "-b", "--", "--c")
	})
	t.Run("short", func(t *testing.T) {
		fs := new(FlagSet)
		fs.Add(makeFlagV(&testBreakFlag{}, 'f'))
		testBreak(t, fs, "-f", "--", "-f")
	})
	t.Run("long", func(t *testing.T) {
		fs := new(FlagSet)
		fs.Add(makeFlagV(&testBreakFlag{}, "foo"))
		testBreak(t, fs, "--foo", "--", "-f")
	})
}

type isOptionCaller struct{ testCaller }

func (i *isOptionCaller) IsOption(string) bool { return false }

var _ IsOption = (*isOptionCaller)(nil)

func testIsOption(t *testing.T, fs *FlagSet, args ...string) {
	t.Helper()
	rest, _, err := fs.Parse(args)
	if err != nil {
		t.Fatalf("Parse(%q): error: %v", args, err)
	}
	if a, b := args[1:], rest; !reflect.DeepEqual(a, b) {
		t.Fatalf("Parse(%q): return arguments, want != have\n%q\n%q", args, a, b)
	}
}

func TestIsOption(t *testing.T) {
	fs := new(FlagSet)
	fs.New("foo", "bar").Func(&isOptionCaller{})
	testIsOption(t, fs, "foo", "-foo", "-bar", "-baz")
}
