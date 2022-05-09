// Package flagopt implements command-line flag parsing with long and short
// options.
package flagopt

import (
	"errors"
	"flag"
	"fmt"
	"os"
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
	gid   int
}

type subset struct {
	name string
	id   int
	gid  int
	fs   *FlagSet
}

// FlagSet is a set of options defined by Flag values.
// Its zero value is a usable empty flagset.
type FlagSet struct {
	// List of all Flag identifiers in this set
	ident  []*Flag
	igroup []string

	// Lookup maps for all short/long identifiers
	short map[rune]*Flag
	long  map[string]*Flag
	// Sorted long identifiers
	ll  []string
	lls bool
	rv  *Flag

	cmds map[string]struct{}
	// Sorted subset identifiers
	cl     []subset
	cgroup []string
	cls    bool
	ct     int

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
	flags FlagSetFlag
}

// New returns a new, empty FlagSet identified by name with a description desc.
// It panics if name or desc is an empty string.
func New(name, desc string) *FlagSet {
	fs := new(FlagSet)
	fs.Describe(desc)
	fs.Name(name)
	fs.SetFlags(FlagDefault)
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

// FlagSetFlag is a set of configuration bits for FlagSets.
type FlagSetFlag int

func (f FlagSetFlag) has(bits FlagSetFlag) bool { return f&bits != 0 }

const (
	// Include a help flag when adding a command or flag to a FlagSet.
	FlagHelp FlagSetFlag = 1 << iota

	FlagDefault = FlagHelp
)

// SetFlags sets the configuration flags for this set.
// Inherited by all subsets created using New.
func (f *FlagSet) SetFlags(flags FlagSetFlag) {
	f.flags = flags
}

// New returns a new subset identified by name with a description desc.
// It panics if name or desc are empty strings.
func (f *FlagSet) New(name, desc string) *FlagSet {
	fs := &FlagSet{ct: f.ct, flags: f.flags}
	fs.Describe(desc)
	f.Register(fs, name)
	return fs
}

// Len sets the minimum length of the matching remaining prefix for this set.
// A negative length will always match a non-ambigous command.
// Inherited by all subsets created using New.
func (f *FlagSet) Len(i int) {
	f.ct = i
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

func (f *FlagSet) find(name string) (v rune, ok bool) {
	for _, v = range name {
		if v == '-' {
			continue
		}
		if _, ok = f.short[v]; !ok {
			return
		}
	}
	for _, v = range name {
		if v == '-' {
			continue
		}
		if n := unicode.ToUpper(v); n == v {
			v = unicode.ToLower(v)
		} else {
			v = n
		}
		if _, ok = f.short[v]; !ok {
			return
		}
	}
	return
}

var (
	errInvalidOption   = errors.New("invalid option identifier")
	errNoUndefinedOpts = errors.New("no undefined options")
)

// next returns the first unused short value from name.
func (f *FlagSet) next(name string) (rune, error) {
	v, ok := f.find(name)
	if v == '-' {
		return -1, fmt.Errorf("%w: %q", errInvalidOption, v)
	}
	if ok {
		return -1, fmt.Errorf("%w: %q", errNoUndefinedOpts, name)
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

func (f *FlagSet) autoHelp() (err error) {
	if !f.flags.has(FlagHelp) {
		return
	}
	if len(f.ident) > 0 {
		return
	}
	fl := &Flag{
		Value: breakFlag(func() error {
			return f.Usage(os.Stdout)
		}),
		Short: []rune{'h'},
		Long:  []string{"help"},
		Desc:  "Show this help",
	}
	return f.add1(fl)
}

var errNoOptions = errors.New("no options defined for flag")

func (f *FlagSet) add(fl *Flag) error {
	if err := f.autoHelp(); err != nil {
		return err
	}
	return f.add1(fl)
}

func (f *FlagSet) add1(fl *Flag) error {
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
	fl.gid = len(f.igroup)
	f.ident = append(f.ident, fl)
	return nil
}

// SetFlagGroup sets the group for new flags in Usage to name.
// It panics when name is an empty string.
func (f *FlagSet) SetFlagGroup(name string) {
	if name == "" {
		panic("empty group name")
	}
	f.igroup = append(f.igroup, name)
}

// SetSubsetGroup sets the group for new FlagSets in Usage to name.
// It panics when name is an empty string.
func (f *FlagSet) SetSubsetGroup(name string) {
	if name == "" {
		panic("empty group name")
	}
	f.cgroup = append(f.cgroup, name)
}

// Set long and short options for value v identified by ident.
// Short option identifiers are single rune length strings.
// Value v is passed to NewValue.
// It panics on zero length identifiers and NewValue errors.
func (f *FlagSet) Set(v interface{}, desc string, ident ...string) *Flag {
	fl, err := f.set(NewValue(v), desc, ident...)
	if err != nil {
		panic(err)
	}
	return fl
}

func (f *FlagSet) set(value Value, desc string, ident ...string) (*Flag, error) {
	fl := &Flag{
		Desc:  desc,
		Value: value,
	}
	for _, v := range ident {
		rv := []rune(v)
		if len(rv) > 1 {
			fl.Long = append(fl.Long, v)
		} else if len(rv) == 1 {
			fl.Short = append(fl.Short, rv[0])
		} else {
			return nil, errors.New("zero length identifier")
		}
	}
	return fl, f.add(fl)
}

// SetRange sets the range value as v with a description desc and optional
// long options identified by ident.
// Short range value is identified by a sequence of numbers in short options.
// Value v is passed to NewValue.
func (f *FlagSet) SetRange(v interface{}, desc string, ident ...string) *Flag {
	fl, err := f.setRange(NewValue(v), desc, ident...)
	if err != nil {
		panic(err)
	}
	return fl
}

func (f *FlagSet) setRange(value Value, desc string, ident ...string) (*Flag, error) {
	if f.rv != nil {
		return nil, errors.New("range flag already exists")
	}
	if err := f.autoHelp(); err != nil {
		return nil, err
	}
	fl := &Flag{
		Desc:  desc,
		Value: value,
		gid:   len(f.igroup),
	}
	f.rv = fl
	if len(ident) > 0 {
		fl.Long = ident
		return fl, f.add1(fl)
	}
	f.ident = append(f.ident, fl)
	return fl, nil
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

func eqArg(arg []rune) (string, bool) {
	if len(arg) > 0 && arg[0] == '=' {
		return string(arg[1:]), true
	}
	return string(arg), false
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

func isNum(r rune) bool { return '0' <= r && r <= '9' }

func (f *FlagSet) parseShort(arg string, next []string) (err error) {
	var (
		v  rune
		rv *Flag
		ri int
	)
loop:
	for i, ra := 0, []rune(arg); i < len(ra); i++ {
		v = ra[i]
		var (
			fv *Flag
			ok bool
		)
		if rv != nil {
			n := i
			if in := isNum(v); in && i < len(ra)-1 {
				continue
			} else if in {
				n++
			}
			err = rv.Set(arg[ri:n])
			if err != nil {
				v = '#'
				break
			}
			rv = nil
			if n >= len(ra) {
				break
			}
		}
		for p := f; p != nil; p = p.prev {
			if p.rv != nil && isNum(v) {
				rv, ri, ok = p.rv, i, true
				i--
				continue loop
			}
			if fv, ok = p.short[v]; ok {
				break
			}
		}
		if !ok {
			return fmt.Errorf("undefined option -%s",
				string(v),
			)
		}

		argv, eq := eqArg(ra[i+1:])
		if b, ok := fv.Value.(boolFlag); ok && b.IsBoolFlag() {
			if eq {
				err = fv.Set(argv)
				break
			} else {
				err = fv.Set("true")
			}
		} else {
			eq = i != len(ra)-1
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
	if len(in) == 0 {
		return in
	}
	var n int
	for i := 1; i < len(in); i++ {
		if in[i] != in[i-1] {
			n++
			in[n] = in[i]
		}
	}
	return in[:n+1]
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
	if err := f.autoHelp(); err != nil {
		return err
	}
	if f.cmds == nil {
		f.cmds = make(map[string]struct{})
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
	} else if _, ok := f.cmds[fs.name]; !ok {
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
		f.cmds[v] = struct{}{}
		f.cl = append(f.cl, subset{
			name: v, fs: fs, id: len(f.cl), gid: len(f.cgroup),
		})
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

func (f *FlagSet) skip(prefix string) bool {
	return f.ct > -1 && len(f.name)-len(prefix) > f.ct
}

func sublookup(a []subset, prefix string) (set []subset) {
	i := sort.Search(len(a), func(i int) bool {
		return a[i].name >= prefix
	})
	if i >= len(a) {
		return
	}
	if a[i].name == prefix {
		return a[i : i+1]
	}
	for j := i; j < len(a); j++ {
		if !strings.HasPrefix(a[j].name, prefix) {
			break
		}
		if a[j].fs.skip(prefix) {
			continue
		}
		set = append(set, a[j])
	}
	return
}

func (f *FlagSet) sublookup(prefix string) (set []subset) {
	if !f.cls {
		sort.Slice(f.cl, func(i, j int) bool {
			return f.cl[i].name < f.cl[j].name
		})
		f.cls = true
	}
	return sublookup(f.cl, prefix)
}

// BreakError can be used to wrap an error in either options or commands
// to conditionally stop the parse loop and return rest of the arguments to
// the caller of Parse.
type BreakError struct{ Err error }

func (e BreakError) Error() string {
	if e.Err != nil {
		return e.Err.Error()
	}
	return "break error"
}

func (e BreakError) Unwrap() error {
	if e.Err != nil {
		return e.Err
	}
	return nil
}

var (
	// errBreak stops the parse loop.
	errBreak = errors.New("break")

	// errContinue indicates that the next argument should be skipped.
	errContinue = errors.New("continue")

	// errNoCommand indicates that all non-option arguments should not
	// be looked up as commands.
	errNoCommand = errors.New("no such command")
)

func (f *FlagSet) setArg(arg string) (err error) {
	if !f.done && f.cmd != nil {
		// If cmd returns false using the From interface and
		// does not implement the Setter interface this will panic.
		f.done, err = f.cmd.(Setter).Set(arg)
		f.argc++
		return
	}
	return errNoCommand
}

func (f *FlagSet) setArgs(args []string) (i int, err error) {
	for ; i < len(args); i++ {
		err = f.setArg(args[i])
		if err == errNoCommand {
			return i - 1, nil
		} else if err != nil {
			break
		}
	}
	return
}

func sjoin(s []subset, sep string) string {
	b := new(strings.Builder)
	for i, v := range s {
		b.WriteString(v.name)
		if i == len(s)-1 {
			break
		}
		b.WriteString(sep)
	}
	return b.String()
}

func (f *FlagSet) parseArg(arg string) (_ *FlagSet, err error) {
	var fs []subset
	if f.argc == 0 && arg != "" {
		fs = f.sublookup(arg)
	}
	if len(fs) > 1 {
		return nil, fmt.Errorf(
			"command %q is ambiguous; possibilities: %s", arg,
			sjoin(fs, ", "),
		)
	}
	if len(fs) == 0 {
		return nil, f.setArg(arg)
	}

	nc := fs[0].fs
	nc.arg0 = fs[0].name
	if nc.cmd == nil {
		return nc, nil
	}
	if fi, ok := nc.cmd.(From); ok {
		nc.done, err = fi.From(nc.arg0)
	}
	return nc, err
}

func (f *FlagSet) isOption(arg string) bool {
	if fi, ok := f.cmd.(IsOption); ok {
		return fi.IsOption(arg)
	}
	return true
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
	if len(arg) > 1 && i > 0 && !f.isOption(arg) {
		i = 0
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
// Done is set when the returning error is a zero value BreakError.
func (f *FlagSet) Parse(args []string) (rest []string, done bool, err error) {
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
			return rest, done, fs.err(err)
		}

		var fn *FlagSet
		fn, err = fs.parse(len(rest) != 0, args[i], args[i+1:])
		if fn != nil {
			fn.prev = fs
			fs = fn
		}

		switch err {
		case errBreak:
			var j int
			j, err = fs.setArgs(args[i+1:])
			if err == nil {
				i += j + 1
				break loop
			}
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

		if done = errors.Is(err, BreakError{}); done {
			break
		}
		return rest, done, fs.err(err)
	}

	f.call = fs
	if i != len(args) {
		rest = append(rest, args[i+1:]...)
	}
	return rest, done, fs.err(err)
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

type breakFlag func() error

func (f breakFlag) String() string   { return "false" }
func (f breakFlag) IsBoolFlag() bool { return true }
func (f breakFlag) Set(arg string) error {
	v, err := parseBool(arg)
	if err == nil && v {
		return BreakError{f()}
	}
	return err
}
