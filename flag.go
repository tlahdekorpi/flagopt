// Package flagopt implements command-line flag parsing with long and short
// options.
package flagopt

import (
	"errors"
	"flag"
	"fmt"
	"sort"
	"strings"
	"unicode"
)

// A Flag represents a list of long and short options for the flag.Value interface.
type Flag struct {
	flag.Value
	Short []rune
	Long  []string
	Desc  string
}

// FlagSet is a set of options defined by Flag values.
// Its zero value is a usable empty flagset.
type FlagSet struct {
	// List of all Flag identifiers in this set
	ident []*Flag

	// Lookup maps for all short/long identifiers
	short map[rune]*Flag
	long  map[string]*Flag
	// Sorted long identifiers
	ll  []string
	lls bool

	cmds map[string]*FlagSet
	// Sorted subset identifiers
	cl  []string
	cls bool

	cmd  Caller
	done bool
	argc int

	// Set during parse to the top of the FlagSet list
	call *FlagSet
	prev *FlagSet

	name  string
	desc  string
	alias []string
	arg0  string
}

// New returns a new, empty FlagSet identified by name with a description desc.
// It panics if name or desc is an empty string.
func New(name, desc string) *FlagSet {
	fs := new(FlagSet)
	fs.Describe(desc)
	fs.Name(name)
	return fs
}

// Name sets the name of f to name.
// It panics if name is an empty string.
func (f *FlagSet) Name(name string) {
	if name == "" {
		panic("empty flagset name")
	}
	f.name = name
}

// Describe sets the description for f to desc.
// It panics if desc is an empty string.
func (f *FlagSet) Describe(desc string) {
	if desc == "" {
		panic("empty flagset description")
	}
	f.desc = desc
}

// New returns a new subset identified by name with a description desc.
// It panics if name or desc are empty strings.
func (f *FlagSet) New(name, desc string) *FlagSet {
	fs := new(FlagSet)
	fs.Describe(desc)
	f.Register(fs, name)
	return fs
}

// Func sets the command of f to fn.
// If fn does not implement the Caller interface, it is passed to NewFunc.
// Callers that do not implement the Setter interface are marked as done
// and take no arguments.
func (f *FlagSet) Func(fn interface{}) {
	if c, ok := fn.(Caller); ok {
		f.cmd = c
	} else if fn != nil {
		f.cmd = NewFunc(fn)
	}
	_, ok := f.cmd.(Setter)
	f.done = !ok
}

// next returns the first unused short value from name.
func (f *FlagSet) next(name string) (rune, error) {
	var (
		v  rune
		ok bool
	)
	for _, v = range name {
		if v == '-' {
			continue
		}
		if _, ok = f.short[v]; !ok {
			break
		}
		v = unicode.SimpleFold(v)
		if _, ok = f.short[v]; !ok {
			break
		}
	}
	if v == '-' {
		return -1, fmt.Errorf("invalid option identifier: %q", v)
	}
	if ok {
		return -1, fmt.Errorf("no undefined options found: %q", name)
	}
	return v, nil
}

// Add includes all short and long options from Flag to the set.
// This function will panic when there are no options defined
// or a option was previously defined.
func (f *FlagSet) Add(fl *Flag) {
	if err := f.add(fl); err != nil {
		panic(err)
	}
}

var errNoOptions = errors.New("no options defined for flag")

func (f *FlagSet) add(fl *Flag) error {
	if f.short == nil || f.long == nil {
		f.short, f.long = make(map[rune]*Flag), make(map[string]*Flag)
	}

	if len(fl.Short) == 0 && len(fl.Long) == 0 {
		return errNoOptions
	}
	for _, v := range fl.Short {
		if _, ok := f.short[v]; !ok {
			f.short[v] = fl
			continue
		}
		return fmt.Errorf("option -%s, flag already exists", string(v))
	}
	for _, v := range fl.Long {
		if _, ok := f.long[v]; !ok {
			f.long[v] = fl
			f.ll = append(f.ll, v)
			continue
		}
		return fmt.Errorf("option --%s, flag already exists", v)
	}
	f.ident = append(f.ident, fl)
	return nil
}

// Set long and short options for value v identified by name.
// The next undefined rune from name is used as the short option identifier.
// No long options are defined when name is only a single character.
// Value v is passed to NewValue.
func (f *FlagSet) Set(name, desc string, v interface{}) *Flag {
	fl, err := f.set(name, desc, NewValue(v))
	if err != nil {
		panic(err)
	}
	return fl
}

func (f *FlagSet) set(name, desc string, value flag.Value) (*Flag, error) {
	fl := &Flag{
		Desc:  desc,
		Value: value,
	}
	if len(name) > 1 {
		fl.Long = []string{name}
	} else if len(name) == 1 {
		fl.Short = []rune(name)[:1]
		return fl, f.add(fl)
	}
	r, err := f.next(name)
	if err != nil {
		return nil, err
	}
	fl.Short = []rune{r}
	return fl, f.add(fl)
}

// lookup searches a sorted slice of strings for a prefix.
// Returns a slice of matching prefixes and the starting slice index.
// When the prefix is an exact match only it is returned.
func lookup(a []string, prefix string) ([]string, int) {
	i := sort.SearchStrings(a, prefix)
	if i >= len(a) {
		return nil, i
	}
	if a[i] == prefix {
		return a[i : i+1], i
	}
	var j int
	for j = i; j < len(a); j++ {
		if !strings.HasPrefix(a[j], prefix) {
			break
		}
	}
	if i == j {
		return nil, i
	}
	return a[i:j], i
}

func (f *FlagSet) llookup(prefix string) []string {
	if !f.lls {
		sort.Strings(f.ll)
		f.lls = true
	}
	r, _ := lookup(f.ll, prefix)
	return r
}

func eqArg(arg string) (string, bool) {
	if len(arg) > 0 && arg[0] == '=' {
		return arg[1:], true
	}
	return arg, false
}

// boolFlag is similar to the flag.boolFlag interface, indicating when an option
// could be called without arguments or as a non-terminating short option.
type boolFlag interface {
	IsBoolFlag() bool
}

// String returns the name of f when called before Parse.
// If Parse is called before String, it returns a space separated list of all callers.
func (f *FlagSet) String() string {
	if f.call != nil && f.call != f {
		return f.call.String()
	}
	if f.name == "" {
		return "<unnamed FlagSet>"
	}
	var fn []string
	for p := f; p != nil; p = p.prev {
		if p.name == "" || p.prev == nil {
			break
		}
		fn = append(fn, p.name)
	}
	if fn == nil {
		return f.name
	}
	for i, j := 0, len(fn)-1; i <= j; i++ {
		fn[i], fn[j] = fn[j], fn[i]
		j--
	}
	return strings.Join(fn, " ")
}

// err is similar to String except uses arg0 over name and does not use f.call.
func (f *FlagSet) err(err error) error {
	if err == nil {
		return nil
	}
	if f.name == "" {
		return err
	}
	var fn []string
	for p := f; p != nil; p = p.prev {
		if p.arg0 == "" {
			break
		}
		fn = append(fn, p.arg0)
	}
	if fn == nil {
		return err
	}
	for i, j := 0, len(fn)-1; i <= j; i++ {
		fn[i], fn[j] = fn[j], fn[i]
		j--
	}
	return fmt.Errorf("%s: %w", strings.Join(fn, " "), err)
}

func (f *FlagSet) parseShort(arg string, next []string) (err error) {
	var (
		i int
		v rune
	)
	for i, v = range arg {
		var (
			fv *Flag
			ok bool
		)
		for p := f; p != nil; p = p.prev {
			if fv, ok = p.short[v]; ok {
				break
			}
		}
		if !ok {
			return fmt.Errorf("undefined option -%s", string(v))
		}

		argv, eq := eqArg(arg[i+1:])
		if b, ok := fv.Value.(boolFlag); ok && b.IsBoolFlag() {
			if eq {
				err = fv.Set(argv)
				break
			} else {
				err = fv.Set("true")
			}
		} else {
			eq = i != len(arg)-1
			if !eq && len(next) > 0 {
				argv = next[0]
			}
			if argv == "" {
				return fmt.Errorf("option requires an argument -%s", string(v))
			}
			if err = fv.Set(argv); err == nil {
				if eq {
					return nil
				}
				return errContinue
			}
			break
		}
		if err != nil {
			break
		}
	}
	if err != nil {
		return fmt.Errorf("-%s, %w", string(v), err)
	}
	return nil
}

func uniq(in []string) []string {
	var j, n int = -1, 0
	for i := range in {
		if j != -1 && in[i] == in[j] {
			continue
		}
		in[n], j = in[i], i
		n++
	}
	return in[:n]
}

func (f *FlagSet) parseLong(arg string, next []string) (err error) {
	var (
		argv string
		eq   bool
	)
	if i := strings.IndexByte(arg, '='); i != -1 {
		arg, argv = arg[:i], arg[i+1:]
		eq = true
	}

	var fs []string
	// TODO: Long flag lookup prefixes for a more useful ambiguity match.
	for p := f; p != nil; p = p.prev {
		n := p.llookup(arg)
		if len(n) == 0 {
			continue
		}
		if n[0] == arg {
			fs = n[:1]
			break
		}
		fs = append(fs, n...)
	}
	if fs == nil {
		return fmt.Errorf("undefined option --%s", arg)
	}
	for i := 0; i < 2; i++ {
		if len(fs) == 1 || fs[0] == arg {
			break
		}
		if i == 0 {
			sort.Strings(fs)
			fs = uniq(fs)
			continue
		}
		return fmt.Errorf(
			"option --%s is ambiguous; possibilities: %s", arg,
			strings.Join(fs, ", "),
		)
	}

	var (
		fv *Flag
		ok bool
	)
	for p := f; p != nil; p = p.prev {
		if fv, ok = p.long[fs[0]]; ok {
			break
		}
	}
	if fv == nil {
		panic(fmt.Errorf("option --%s, missing flag", fs[0]))
	}

	if b, ok := fv.Value.(boolFlag); ok && b.IsBoolFlag() {
		if argv != "" {
			err = fv.Set(argv)
		} else {
			err = fv.Set("true")
		}
		if err != nil {
			return fmt.Errorf("--%s, %w", fs[0], err)
		}
		return nil
	}

	if !eq && len(next) > 0 {
		argv = next[0]
	}
	if argv == "" {
		return fmt.Errorf("option requires an argument --%s", fs[0])
	}
	if err = fv.Set(argv); err == nil {
		if eq {
			return nil
		}
		return errContinue
	}
	return fmt.Errorf("--%s, %w", fs[0], err)
}

func (f *FlagSet) register(fs *FlagSet, name ...string) error {
	if f.cmds == nil {
		f.cmds = make(map[string]*FlagSet)
	}
	if fs == f {
		// TODO: Handle flagset loops.
		return errors.New("flagset loop")
	}
	if fs == nil {
		return errors.New("register called with nil flagset")
	}
	if fs.name == "" && len(name) == 0 {
		return errors.New("flagset name required")
	}
	var i int
	if fs.name == "" {
		fs.name, name = name[0], name[1:]
		i--
	} else if f.cmds[fs.name] == nil {
		i--
	}
	for ; i < len(name); i++ {
		var v string
		if i == -1 {
			v = fs.name
		} else {
			v = name[i]
		}
		if v == "" {
			return errors.New("flagset name is empty")
		}
		// Would result in a collision with options.
		if v[0] == '-' {
			return fmt.Errorf("invalid flagset name: %q", v)
		}
		if _, ok := f.cmds[v]; ok {
			return fmt.Errorf("flagset name is registered: %q", v)
		}
		if i != -1 {
			fs.alias = append(fs.alias, v)
		}
		f.cmds[v] = fs
		f.cl = append(f.cl, v)
	}
	return nil
}

// Register adds fs as a command to f.
// A name is required when fs is an unnamed set.
// When multiple names are provided, they are registered as aliases.
func (f *FlagSet) Register(fs *FlagSet, name ...string) {
	if err := f.register(fs, name...); err != nil {
		panic(err)
	}
}

func (f *FlagSet) clookup(prefix string) ([]string, int) {
	if !f.cls {
		sort.Strings(f.cl)
		f.cls = true
	}
	return lookup(f.cl, prefix)
}

var (
	// ErrBreak can be used as an error in either options or commands
	// to break the parse loop and return rest of the arguments to the
	// caller of Parse.
	ErrBreak = errors.New("flagopt: break")

	// errBreak is the same as Break but not returned to the caller.
	errBreak = errors.New("break")

	// errContinue indicates that the next argument should be skipped.
	errContinue = errors.New("continue")

	// errNoCommand indicates that all non-option arguments should not
	// be looked up as commands.
	errNoCommand = errors.New("no such command")
)

func (f *FlagSet) parseArg(arg string) (_ *FlagSet, err error) {
	var (
		fs []string
		// i int
	)

	// TODO: Ambigous command threshold
	// When below threshold, this is a map lookup of the exact match.
	// Configurable per-command threshold.
	if f.argc == 0 {
		fs, _ = f.clookup(arg)
		// fs, i
	}
	if len(fs) > 1 {
		return nil, fmt.Errorf(
			"command %q is ambiguous; possibilities: %s", arg,
			strings.Join(fs, ", "),
		)
	}
	if fs != nil {
		nc := f.cmds[fs[0]]
		nc.arg0 = fs[0]
		// TODO: FlagSet loops
		// Remove commands on shifting to the next FlagSet.
		// Configurable.
		// f.cl = append(f.cl[:i], f.cl[i+1:]...)
		if nc.cmd == nil {
			return nc, nil
		}
		if fi, ok := nc.cmd.(From); ok {
			nc.done, err = fi.From(nc.arg0)
		}
		return nc, err
	}
	if !f.done && f.cmd != nil {
		// If cmd returns false using the From interface and does
		// not implement the Setter interface this will panic.
		f.done, err = f.cmd.(Setter).Set(arg)
		f.argc++
		return
	}
	return nil, errNoCommand
}

func (f *FlagSet) parse(nc bool, arg string, next []string) (*FlagSet, error) {
	if arg == "--" {
		return nil, errBreak
	}
	var i int
	for ; i < 2; i++ {
		if i >= len(arg) || arg[i] != '-' {
			break
		}
	}
	// A single - won't be treated as a short option.
	// This can be a argument to a command, usually meaning stdin.
	if i == 0 || arg == "-" {
		if nc {
			return nil, errNoCommand
		}
		return f.parseArg(arg)
	}
	if i == 1 {
		return nil, f.parseShort(arg[1:], next)
	}
	return nil, f.parseLong(arg[2:], next)
}

// Parse reads arguments from the list and returns all unparsed arguments
// to the caller. Should be called after all options are defined.
func (f *FlagSet) Parse(args []string) (rest []string, err error) {
	var (
		i    int
		next bool
	)
	fs := f
loop:
	for i = range args {
		if next {
			next = !next
			continue
		}
		if err != nil {
			return rest, fs.err(err)
		}

		var fn *FlagSet
		fn, err = fs.parse(len(rest) != 0, args[i], args[i+1:])
		if fn != nil {
			fn.prev = fs
			fs = fn
		}

		switch err {
		case errBreak:
			// Unlike Break this is not returned
			err = nil
			fallthrough
		case ErrBreak:
			// Returned to the caller
			break loop
		case errContinue:
			// Skip the next argument
			err, next = nil, true
			continue
		case errNoCommand:
			// Stop all command matching
			rest, err = append(rest, args[i]), nil
			continue
		case nil:
			continue
		}
		// Exported break error might be wrapped
		if errors.Is(err, ErrBreak) {
			break
		}
		return rest, fs.err(err)
	}

	f.call = fs
	if i != len(args) {
		rest = append(rest, args[i+1:]...)
	}
	return rest, fs.err(err)
}

// Caller returns the current parsed caller.
func (f *FlagSet) Caller() *FlagSet { return f.call }

// Call runs the current command for the parsed flagset and advances
// the list to the next caller. Returns false when there are no more callers.
func (f *FlagSet) Call() (ok bool, err error) {
	if f.call != nil && f.call.cmd != nil {
		ok, err = true, f.call.err(f.call.cmd.Call())
		f.call = f.call.prev
	}
	return
}

// Exec runs all the commands in the parsed list and returns on error.
// Sets without commands are skipped.
func (f *FlagSet) Exec() (err error) {
	var p *FlagSet
	for p = f.call; p != nil; p = p.prev {
		if p.cmd == nil {
			continue
		}
		if err = p.err(p.cmd.Call()); err != nil {
			break
		}
	}
	return
}
