package flagopt

import (
	"fmt"
	"io"
	"sort"
	"strings"
	"text/tabwriter"
)

func (f *Flag) usage(w io.Writer, l int) {
	io.WriteString(w, "  ")
	for i, v := range f.Short {
		fmt.Fprintf(w, "-%s", string(v))
		if i != len(f.Short)-1 {
			io.WriteString(w, " ")
		}
	}
	for i, v := range f.Long {
		if i == 0 {
			if len(f.Short) > 0 {
				io.WriteString(w, " ")
			}
			io.WriteString(w, strings.Repeat(
				"   ", l-len(f.Short),
			))
		}
		fmt.Fprintf(w, "--%s", v)
		if i != len(f.Long)-1 {
			io.WriteString(w, " ")
		}
	}
	if v, ok := f.Value.(boolFlag); ok && !v.IsBoolFlag() || !ok {
		io.WriteString(w, "=")
		if v, ok := f.Value.(Value); ok {
			io.WriteString(w, v.Type())
		}
	}
	if v, ok := f.Value.(funcFlag); ok && v.IsBoolFlag() && v.first != nil {
		io.WriteString(w, v.Type())
	}
	if f.Desc == "" {
		io.WriteString(w, "\t\n")
		return
	}
	fmt.Fprintf(w, "\t %s\n", strings.ReplaceAll(f.Desc, "\n", "\n\t\t"))
}

func (f *FlagSet) usagesig(w io.Writer) {
	fmt.Fprintf(w, "%s ", f.name)
	if len(f.ident) > 0 {
		io.WriteString(w, "[options...] ")
	}
	if len(f.cmds) > 0 {
		io.WriteString(w, "[command] ")
	}
	if fi, ok := f.cmd.(Signature); ok {
		io.WriteString(w, fi.Signature())
	}
	if f.desc != "" {
		fmt.Fprintf(w, "\n\n%s\n", f.desc)
	} else {
		fmt.Fprintln(w)
	}
	if len(f.ident) > 0 || len(f.cmds) > 0 {
		fmt.Fprintln(w)
	}
}

func (f *FlagSet) signature(w io.Writer) {
	fmt.Fprintf(w, "  %s", f.name)
	if len(f.alias) > 0 {
		io.WriteString(w, ", ")
		io.WriteString(w, strings.Join(f.alias, ", "))
	}
	io.WriteString(w, "\t")
	if len(f.ident) > 0 {
		io.WriteString(w, "[options...] ")
	}
	fi, ok := f.cmd.(Signature)
	if !ok {
		fmt.Fprintf(w, "\t %s\n", f.desc)
	} else {
		fmt.Fprintf(w, "%s\t %s\n", fi.Signature(), f.desc)
	}
}

func (f *FlagSet) usage(w io.Writer) {
	sort.Slice(f.cl, func(i, j int) bool {
		return f.cl[i].id < f.cl[j].id
	})
	f.cls = false

	for i, v := range f.cl {
		if v.name != v.fs.name {
			// alias
			continue
		}
		if i == 0 && v.gid == 0 {
			fmt.Fprintln(w, "Commands:")
		} else if i == 0 {
			fmt.Fprintf(w, "%s Commands:\n", f.cgroup[v.gid-1])
		}
		if i > 0 && v.gid > 0 && v.gid != f.cl[i-1].gid {
			fmt.Fprintf(w, "\n%s Commands:\n", f.cgroup[v.gid-1])
		}
		v.fs.signature(w)
		if i == len(f.cl)-1 && len(f.ident) > 0 {
			fmt.Fprintln(w)
		}
	}
	var i int
	for _, v := range f.ident {
		if j := len(v.Short); i < j {
			i = j
		}
	}
	for j, v := range f.ident {
		if j == 0 && v.gid == 0 {
			fmt.Fprintln(w, "Options:")
		} else if j == 0 {
			fmt.Fprintf(w, "%s Options:\n", f.igroup[v.gid-1])
		}
		if j > 0 && v.gid > 0 && v.gid != f.ident[j-1].gid {
			fmt.Fprintf(w, "\n%s Options:\n", f.igroup[v.gid-1])
		}
		v.usage(w, i)
	}
}

// Usage writes a message documenting all defined commands and options to w.
func (f *FlagSet) Usage(w io.Writer) error {
	f.usagesig(w)
	tw := tabwriter.NewWriter(w, 1, 1, 1, ' ', 0)
	f.usage(tw)
	return tw.Flush()
}
