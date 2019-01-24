package b

import (
	"sync"
	"io"
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
	zeroXElement    XElement
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


func newX(ch0 interface{}) *X {
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
		q.x[q.c+1] = zeroXElement
	}
}


func (q *X) insert(i int, k interface{}, ch interface{}) *X {
	c := q.c
	if i < c {
		q.x[c+1].ch = q.x[c].ch
		copy(q.x[i+2:], q.x[i+1:c])
		q.x[i+1].k = q.x[i].k
	}
	c ++
	q.c = c
	q.x[i].k = k
	q.x[i+1].ch = ch
	return q
}

func (q *X) siblings(i int) (l, r *DataPage) {
	if i >= 0 {
		if i > 0 {
			l = q.x[i-1].ch.(*DataPage)
		}
		if i < q.c {
			r = q.x[i+1].ch.(*DataPage)
		}
	}
	return
}

func (l *DataPage) mvL(r *DataPage, c int) {
	copy(l.d[l.c:], r.d[:c])
	copy(r.d[:], r.d[c:r.c])
	l.c += c
	r.c -= c
}


func (l *DataPage) mvR(r *DataPage, c int) {
	copy(r.d[c:], r.d[:r.c])
	copy(r.d[:c], l.d[l.c-c:])
	r.c += c
	l.c -= c
}

// ------------
func TreeNew(cmp Cmp) *Tree {
	return btTPool.get(cmp)
}

func (t *Tree) Clear() {
	if t.r == nil {
		return
	}

	clr(t.r)
	t.c, t.first, t.last, t.r = 0, nil, nil, nil
	t.ver ++
}


func (t *Tree) Close() {
	t.Clear()
	*t = zeroTree
	btTPool.Put(t)
}


func (t *Tree) cat(p *X, q, r *DataPage, pi int) {
	t.ver ++
	q.mvL(r, r.c)

	if r.next != nil {
		r.next.pre = q
	} else {
		t.last = q
	}

	q.next = r.next
	*r = zeroDataPage
	btDPool.Put(r)
	if p.c > 1 {
		p.extract(pi)
		p.x[pi].ch = q
		return
	}

	switch v:=t.r.(type) {
	case *X:
		*v = zeroX
		btXPool.Put(v)
	case *DataPage:
		*v = zeroDataPage
		btDPool.Put(v)
	}
	t.r = q

}

func (t *Tree) catX(p, q, r *X, pi int) {
	t.ver ++
	q.x[q.c].k = p.x[pi].k
	copy(q.x[q.c+1:], r.x[:r.c])
	q.c += r.c +1
	q.x[q.c].ch = r.x[r.c].ch
	*r = zeroX
	btXPool.Put(r)

	if p.c > 1 {
		p.c --
		pc := p.c
		if pi < pc {
			p.x[pi].k = p.x[pi+1].k
			copy(p.x[pi+1:], p.x[pi+2:pc+1])
			p.x[pc].ch = p.x[pc+1].ch
			p.x[pc].k = zeroK
			p.x[pc + 1].ch = nil
		}

		return
	}

	switch v := t.r.(type) {
	case *X:
		*v = zeroX
		btXPool.Put(v)
	case *DataPage:
		*v = zeroDataPage
		btDPool.Put(v)
	}
	t.r = q
}


func (t *Tree) Delete(k interface{}) (ok bool) {
	pi := -1
	var p *X
	q := t.r
	if q == nil {
		return false
	}

	for {
		var i int
		i, ok = t.find(q, k)
		if ok {
			switch vl := q.(type) {
			case *X:
				if vl.c < kx && q != t.r {
					vl, i = t.underflowX(p, vl, pi, i)
				}
				pi = i + 1
				p = vl
				q = vl.x[pi].ch
				continue
			case *DataPage:
				t.extract(vl, i)
				if vl.c >= kd {
					return true
				}

				if q != t.r {
					t.underflow(p, vl, pi)
				}else if t.c == 0 {
					t.Clear()
				}
				return true
			}
		}

		switch vl := q.(type) {
		case *X:
			if vl.c < kx && q != t.r {
				vl, i = t.underflowX(p, vl, pi, i)
			}
			pi = i
			p = vl
			q = vl.x[i].ch
		case *DataPage:
			return false
		}
	}
}

func (t *Tree) extract(q *DataPage, i int) {
	t.ver ++
	q.c --
	if i<q.c {
		copy(q.d[i:], q.d[i+1:q.c+1])
		q.d[q.c] = zeroDataElement
		t.c --
	}
}

func (t *Tree) find (q interface{}, k interface{}) (i int, ok bool ) {
	var mk interface{}
	l := 0
	switch  v := q.(type) {
	case *X:
		h:= v.c -1
		for l <=h {
			m := (l+h) >> 1
			mk = v.x[m].k
			switch compareResult := t.cmp(k, mk); {
			case compareResult > 0:
				l = m +1
			case compareResult == 0:
				return m , true
			default:
				h = m -1
			}
		}
	case *DataPage:
		h := v.c - 1
		for l <=h {
			m := (l+h) >> 1
			mk = v.d[m].k
			switch compareResult := t.cmp(k, mk); {
			case compareResult > 0:
				l = m +1
			case compareResult == 0:
				return m , true
			default:
				h = m -1
			}
		}
	}
	return l, false
}

func (t *Tree) First() (k interface{}, v interface{}) {
	if q:=t.first; q != nil {
		q := &q.d[0]
		k,v =q.k , q.v
	}
	return
}


func (t *Tree) Get(k interface{}) (v interface{}, ok bool) {
	q := t.r
	if q == nil {
		return
	}

	for {
		var i int
		if i,ok = t.find(q, k); ok {
			switch vl := q.(type) {
			case *X:
				q= vl.x[i+1].ch
				continue
			case *DataPage:
				return vl.d[i].v , true
			}
		}
		switch vl := q.(type) {
		case *X:
			q = vl.x[i].ch
		default:
			return

		}

	}
}


func (t *Tree) insert(q *DataPage, i int, k interface{}, v interface{}) *DataPage {
	t.ver ++
	c := q.c
	if i < c {
		copy(q.d[i+1:], q.d[i:c])
	}
	c ++
	q.c = c
	q.d[i].k, q.d[i].v = k, v
	t.c ++
	return q
}


func (t *Tree) Last() (k interface{}, v interface{}) {
	if q:= t.last; q != nil {
		q := &q.d[q.c-1]
		k,v = q.k , q.v
	}
	return
}

func (t *Tree) Len() int {
	return t.c
}


func (t *Tree) overflow(p *X, q *DataPage, pi, i int, k, v interface{}) {
	t.ver ++
	l, r := p.siblings(pi)

	if l != nil && l.c < 2 *kd && i != 0 {
		l.mvL(q, 1)
		t.insert(q, i-1, k, v)
		p.x[pi-1].k = q.d[0].k
		return
	}

	if r != nil && r.c < 2*kd {
		if i < 2*kd {
			q.mvR(r, 1)
			t.insert(q, i , k, v)
			p.x[pi].k = r.d[0].k
			return
		}

		t.insert(r, 0, k, v)
		p.x[pi].k = k
		return
	}

	t.split(p, q, pi, i , k, v)
}


func (t *Tree) Seek (k interface{}) (e *Enumerator, ok bool) {
	q := t.r
	if q == nil {
		e = btEPool.get(nil, false, 0, k ,nil, t, t.ver)
		return
	}

	for {
		var i int
		if i, ok = t.find(q, k); ok {
			switch v := q.(type) {
			case *X:
				q = v.x[i+1].ch
				continue
			case *DataPage:
				return btEPool.get(nil, ok, i, k, v, t, t.ver), true

			}
		}
		switch v := q.(type) {
		case *X:
			q = v.x[i].ch
		case *DataPage:
			return btEPool.get(nil, ok, i, k, v, t, t.ver), false
		}
	}
}


func (t *Tree) SeekFirst() (e *Enumerator, err error) {
	q := t.first
	if q == nil {
		return nil, io.EOF
	}

	return btEPool.get(nil, true, 0, q.d[0].k, q, t, t.ver), nil
}

func (t *Tree) SeekLast() (e *Enumerator, err error) {
	q := t.last
	if q==nil {
		return nil, io.EOF
	}

	return btEPool.get(nil, true, q.c-1, q.d[q.c-1].k, q, t, t.ver), nil
}




func (t *Tree) Set(k, v interface{}) {
	pi := -1
	var p *X
	q := t.r
	if q == nil {
		z := t.insert(btDPool.Get().(*DataPage), 0, k, v)
		t.r, t.first, t.last = z, z, z
		return
	}

	for {
		i, ok := t.find(q, k)
		if ok {
			switch vl := q.(type) {
			case *X:
				i ++
				if vl.c > 2 *kx {
					vl, i = t.splitX(p, vl, pi, i)
				}
				pi = i
				p = vl
				q = vl.x[i].ch
				continue
			case *DataPage:
				vl.d[i].v = v
			}
			return
		}

		switch vl := q.(type) {
		case *X:
			if vl.c > 2*kx {
				vl, i = t.splitX(p, vl, pi, i)
			}
			pi = i
			p = vl
			q = vl.x[i].ch
		case *DataPage:
			switch  {
			case vl.c < 2*kd:
				t.insert(vl, i, k, v)
			default:
				t.overflow(p, vl, pi, i, k, v)
			}

		}
	}
}


func (t *Tree) Put(k interface{} /*K*/, upd func(oldV interface{} /*V*/, exists bool) (newV interface{} /*V*/, write bool)) (oldV interface{} /*V*/, written bool) {
	pi := -1
	var p *X
	q := t.r

	var newV interface{}
	if q == nil {
		newV, written = upd(newV, false)
		if !written {
			return
		}

		z := t.insert(btDPool.Get().(*DataPage), 0, k, newV)
		t.r, t.first, t.last = z, z, z
		return
	}

	for {
		i, ok := t.find(q, k)
		if ok {
			switch vl := q.(type) {
			case *X:
				i++
				if vl.c > 2*kx {
					vl, i = t.splitX(p, vl, pi, i)
				}
				pi = i
				p = vl
				q = vl.x[i].ch
				continue
			case *DataPage:
				oldV = vl.d[i].v
				newV, written = upd(oldV, true)
				if !written {
					return
				}

				vl.d[i].v = newV
			}
			return
		}

		switch vl := q.(type) {
		case *X:
			if vl.c > 2*kx {
				vl, i = t.splitX(p, vl, pi, i)
			}
			pi = i
			p = vl
			q = vl.x[i].ch
		case *DataPage:
			newV, written = upd(newV, false)
			if !written {
				return
			}

			switch  {
			case vl.c < 2 *kd:
				t.insert(vl, i, k, newV)
			default:
				t.overflow(p, vl, pi, i, k, newV)
			}
			return
		}
	}
}

func (t *Tree) split(p *X, q *DataPage, pi, i int, k, v interface{}) {
	t.ver ++
	r := btDPool.Get().(*DataPage)
	if q.next != nil {
		r.next = q.next
		r.next.pre = r
	} else {
		t.last = r
	}

	q.next = r
	r.pre = q

	copy(r.d[:], q.d[kd:2*kd])
	for i:= range q.d[kd:] {
		q.d[kd+i] = zeroDataElement
	}
	q.c = kd
	r.c = kd
	var done bool
	if i > kd {
		done = true
		t.insert(r, i-kd, k, v)
	}

	if pi >= 0 {
		p.insert(pi, r.d[0].k, r)
	} else {
		t.r = newX(q).insert(0, r.d[0].k, r)
	}
	if done {
		return
	}

	t. insert(q, i, k, v)
}


func (t *Tree) splitX(p *X, q *X, pi int, i int) (*X, int) {
	t.ver ++
	r := btXPool.Get().(*X)

	copy(r.x[:], q.x[kx+1:])
	q.c = kx
	r.c = kx
	if pi >= 0 {
		p.insert(pi, q.x[kx].k, r)
	} else {
		t.r = newX(q).insert(0, q.x[kx].k, r)
	}

	q.x[kx].k = zeroK
	for i := range q.x[kx+1:] {
		q.x[kx+i+1] = zeroXElement
	}

	if i > kx {
		q = r
		i -= kx +1
	}

	return q,i

}


func (t *Tree) underflow(p *X, q *DataPage, pi int) {
	t.ver ++
	l, r := p.siblings(pi)

	if l != nil && l.c + q.c >= 2 *kd {
		l.mvR(q, 1)
		p.x[pi-1].k = q.d[0].k

		return
	}

	if r != nil && q.c + r.c >= 2*kd {
		q.mvL(r, 1)
		p.x[pi].k = r.d[0].k
		r.d[r.c] = zeroDataElement
		return
	}

	if l != nil {
		t.cat(p, l, q, pi-1)
		return
	}

	t.cat(p, q, r, pi)

}

func (t *Tree) underflowX(p *X, q *X, pi int, i int) (*X, int) {
	t.ver++
	var l, r *X

	if pi >=0 {
		if pi > 0 {
			l = p.x[pi-1].ch.(*X)
		}
		if pi < p.c {
			r = p.x[pi+1].ch.(*X)
		}
	}

	if l != nil && l.c > kx {
		q.x[q.c + 1].ch = q.x[q.c].ch
		copy(q.x[1:], q.x[:q.c])
		q.x[0].ch = l.x[l.c].ch
		q.x[0].k = p.x[pi-1].k
		q.c++

		i++
		l.c--
		p.x[pi-1].k = l.x[l.c].k
		return q, i
	}

	if r != nil && r.c > kx{
		q.x[q.c].k = p.x[pi].k
		q.c++
		q.x[q.c].ch = r.x[0].ch
		p.x[pi].k = r.x[0].k
		copy(r.x[:], r.x[1:r.c])
		r.c --
		rc := r.c
		r.x[rc].ch = r.x[rc+1].ch
		r.x[rc].k = zeroK
		r.x[rc+1].ch = nil
		return q, i
	}

	if l != nil {
		i += l.c + 1
		t.catX(p, l, q, pi-1)
		q =l
		return q, i
	}


	t.catX(p, q, r, pi)
	return q, i
}

func (e *Enumerator) Close() {
	*e = zeroEnumerator
	btEPool.Put(e)
}

func (e *Enumerator) Next() (k, v interface{}, err error ) {
	if err = e.err; err != nil {
		return
	}

	if e.ver != e.t.ver {
		f, _ := e.t.Seek(e.k)
		*e = *f
		f.Close()
	}

	if e.q == nil {
		e.err, err = io.EOF, io.EOF
		return
	}

	if e.i >= e.q.c {
		if err = e.next(); err != nil {
			return
		}
	}

	i := e.q.d[e.i]
	k,v = i.k, i.v
	e.k, e.hit = k, true
	e.next()
	return
}

func (e *Enumerator) next() error {
	if e.q == nil {
		e.err = io.EOF
		return io.EOF
	}

	switch  {
	case e.i < e.q.c - 1:
		e.i++
	default:
		if e.q, e.i = e.q.next, 0; e.q == nil {
			e.err = io.EOF
		}
	}
	return e.err
}



func (e *Enumerator) Prev() (k,v interface{}, err error) {
	if err = e.err; err != nil {
		return
	}

	if e.ver != e.t.ver {
		f, _:= e.t.Seek(e.k)
		*e = *f
		f.Close()
	}

	if e.q == nil {
		e.err, err = io.EOF, io.EOF
		return
	}

	if !e.hit {
		if err = e.prev(); err != nil {
			return
		}
	}

	if e.i >= e.q.c {
		if err = e.prev(); err != nil {
			return
		}
	}

	i := e.q.d[e.i]
	k,v = i.k, i.v
	e.k, e.hit = k, true
	e.prev()
	return
}


func (e *Enumerator) prev() error {
	if e.q == nil {
		e.err = io.EOF
		return io.EOF
	}

	switch  {
	case e.i >0:
		e.i --
	default:
		if e.q = e.q.pre; e.q == nil {
			e.err = io.EOF
			break
		}
		e.i = e.q.c - 1
	}
	return e.err
}