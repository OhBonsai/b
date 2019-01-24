package b

import (
	"runtime"
	"fmt"
	"path"
	"strings"
	"bytes"
	"github.com/cznic/strutil"
)

var caller = func(s string, va ...interface{}) {

	_, fn, fl, _ := runtime.Caller(2)
	fmt.Printf("%s:%d: ", path.Base(fn), fl)
	fmt.Printf(s, va...)
	fmt.Println()
}

var dbg = func(s string ,va ...interface{}) {
	if s == "" {
		s = strings.Repeat("%v ", len(va))
	}

	_, fn, fl, _ := runtime.Caller(1)
	fmt.Printf("%s:%d: ", path.Base(fn), fl)
	fmt.Printf(s, va...)
	fmt.Println()
}

func isNil(p interface{}) bool {
	switch vl := p.(type) {
	case *X:
		if vl == nil {
			return true
		}
	case *DataPage:
		if vl == nil {
			return true
		}
	}

	return false
}

func (t *Tree) dump() string {
	var buf bytes.Buffer
	f := strutil.IndentFormatter(&buf, "\t")

	num := map[interface{}]int{}
	visited := map[interface{}]bool{}

	handle := func(p interface{}) int {
		if isNil(p) {
			return 0
		}

		if n, ok := num[p]; ok {
			return n
		}

		n := len(num) + 1
		num[p] = n
		return n
	}

	var pagedump func(interface{}, string)
	pagedump = func(p interface{}, pref string) {
		if isNil(p) || visited[p] {
			return
		}

		visited[p] = true
		switch vl := p.(type) {
		case *X:
			h := handle(p)
			n := 0
			for i, v := range vl.x {
				if v.ch != nil || v.k != nil {
					n = i + 1
				}
			}
			f.Format("%sX#%d(%p) n %d:%d {", pref, h, vl, vl.c, n)
			a := []interface{}{}
			for i,v := range vl.x[:n] {
				a = append(a, v.ch)
				if i != 0 {
					f.Format(" ")
				}
				f.Format("(C#%d K %v", handle(v.ch), v.k)
			}
			f.Format("}\n")
			for _, p := range a {
				pagedump(p, pref+". ")
			}
		case *DataPage:
			h := handle(p)
			n := 0
			for i, v := range vl.d {
				if v.k != nil || v.v != nil {
					n = i+1
				}
			}
			f.Format("%sD#%d(%p) P#%d N#%d n %d:%d {", pref, h, vl, handle(vl.pre), handle(vl.next), vl.c, n)
			for i, v := range vl.d[:n] {
				if i != 0 {
					f.Format(" ")
				}
				f.Format("%v:%v", v.k, v.v)
			}
			f.Format("}\n")
		}
	}
	pagedump(t.r, "")
	s := buf.String()
	if s != "" {
		s = s[:len(s) - 1]
	}
	return s
}