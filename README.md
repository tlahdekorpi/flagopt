Package `flagopt` implements command-line flag and command parsing with long and short options.

Flags and commands can either be described using the provided interfaces or reflection.

## Example
```go
f := flagopt.New("prog", "description")
var opts struct {
	Foo bool  `Description`
	Bar *byte `,i;Byte pointer`
	Baz map[byte]map[uint]map[bool][]*****string
	i   uint
}
f.LoadRaw(&opts)
f.New("baz", "desc").Func(func(v struct {
	Index              uint
	FirstFloat, Second float64
}) {
	opts.i = v.Index
	if v.FirstFloat-v.Second != -3.2 {
		panic("!=")
	}
})
f.Func(func() error {
	a, b := *****opts.Baz[*opts.Bar][opts.i][opts.Foo][0], "baz"
	if a != b {
		return fmt.Errorf("%s != %s", a, b)
	}
	return nil
})
if _, _, err := f.Parse(
	[]string{"baz", "-fi0x1", "255", "1",
		"-b1=0xff=true=foo",
		"--baz=0b1=255=1=bar",
		"--baz", "0x1=0o377=false=baz",
		"--f=0", "4.2",
	},
); err != nil {
	log.Fatal(err)
}
if err := f.Exec(); err != nil {
	log.Fatal(err)
}
```
