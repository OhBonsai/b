package b

import (
	"sync"
)

const (
	kx = 32
	kd = 32
)

type (
	Cmp func(a, b interface{}) int

	DataPage struct {
		c int
		d [2 * kd + 1]DataElement
		next *DataPage
		pre *DataPage
	}

	DataElement struct {
		k interface{}
		v interface{}
	}

	Tree struct {
		c int
		cmp Cmp
		first *DataPage
		last *DataPage
		r interface{}
		ver int64
	}

	Enumerator struct {
		err error
		hit bool
		i int
		k interface{}
		q *DataPage
		t *Tree
		ver int64
	}

	XElement struct {
		ch interface{}
		k interface{}
	}

	X struct {
		c int
		x [2*kx + 2]XElement
	}
)

type btTpool struct { sync.Pool }
func (p *btTpool) get(cmp Cmp) *Tree {
	x := p.Get().(*Tree)
	x.cmp = cmp
	return x
}

type btEpool struct { sync.Pool }
func (p *btEpool) get(err error, hit bool, i int, k interface{}, q *DataPage, t *Tree, ver int64) *Enumerator {
	x := p.Get().(*Enumerator)
	x.err, x.hit, x.i, x.k, x.q, x.t, x.ver = err, hit, i, k, q, t, ver
	return x
}

var (
	btDPool = sync.Pool{New: func() interface{} {return &DataPage{} }}
	btEPool = btEpool{sync.Pool{New: func() interface{} { return &Enumerator{} }}}
	btTPool = btTpool{sync.Pool{New: func() interface{} { return &Tree{} }}}
	btXPool = sync.Pool{New: func() interface{} { return &X{} }}
)

var (
	zeroDataPage    DataPage
	zeroDataElement DataElement
	zeroEnumerator  Enumerator
	zeroK           interface{}
	zeroTree        Tree
	zeroX           X
	zeroElement     XElement
)

func clr(q interface{}) {
	switch t := q.(type) {
	case *X:
		for i:=0; i <= t.c; i++ {
			clr(t.x[i].ch)
		}
		*t = zeroX
		btXPool.Put(t)
	case *DataPage:
		*t = zeroDataPage
		btDPool.Put(t)
	}
}


func newNonLeaf(ch0 interface{}) *X {
	r := btXPool.Get().(*X)
	r.x[0].ch = ch0
	return r
}

func (q *X) extract(i int) {
	q.c--
	if i < q.c {
		copy(q.x[i:], q.x[i+1:q.c+1])
		q.x[q.c].ch = q.x[q.c+1].ch
		q.x[q.c].k = zeroK
		q.x[q.c+1] = zeroElement
	}
}
