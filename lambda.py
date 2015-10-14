"""
Type inference/checking for simply-typed lambda calculus.

V x             means the variable named x
L x e           means (lambda (x) e)
C f e           means (f e)

Fn domain range means the type: domain -> range
"""

# import sys; sys.setrecursionlimit(5000)
from parser import parse
from pythological import fresh, run, both, eq

# XXX LookUp needs disunify to avoid shadowed bindings

example = """

Type (V x)   r type              <- LookUp r x type.
Type (L x e) r (Fn domain range) <- Type e (Bind x domain r) range.
Type (C f e) r range             <- Type f r (Fn domain range),
                                    Type e r domain.

LookUp (Bind key val _) key val.
LookUp (Bind _ _ r)     key val  <- LookUp r key val.
"""
program = parse(example)
Type = program['Type']

Nil = ('Nil',)
def Bind(x, v, r): return 'Bind', x, v, r

def Fn(dom, ran):  return 'Fn', dom, ran

def V(x):          return 'V', x
def L(x, e):       return 'L', x, e
def C(f, e):       return 'C', f, e

q, a, b = fresh('q a b')

f, g, x, y = 'fgxy'
A, B = 'AB'

## run(q, Type(L(x, V(x)), Nil, q))
#. [('Fn', _.0, _.0)]

## run(q, Type(q, Bind(x, a, Nil), a), n=1)
#. [('V', 'x')]

## run(q, Type(q, Nil, Fn(a, a)), n=1)
#. [('L', _.0, ('V', _.0))]


## run(q, Type(L(x, L(y, C(V(y), V(x)))), Nil, q), n=1)
#. [('Fn', _.0, ('Fn', ('Fn', _.0, _.1), _.1))]

## run(q, Type(L(f, L(g, L(x, C(V(f), C(V(g), V(x)))))), Nil, q), n=1)
#. [('Fn', ('Fn', _.0, _.1), ('Fn', ('Fn', _.2, _.0), ('Fn', _.2, _.1)))]
