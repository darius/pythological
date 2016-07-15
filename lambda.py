"""
Type inference/checking for simply-typed lambda calculus.

V x             means the variable named x
L x e           means (lambda (x) e)
C f e           means (f e)

Fn domain range means the type: domain -> range
"""

# import sys; sys.setrecursionlimit(5000)
from parser import parse

# XXX LookUp needs disunify to avoid shadowed bindings
example = open('examples/lambda.pytho').read()
program = parse(example)

## program.q('Type (L x (V x)) [] t', vars='t')
#. t: (Fn _.0 _.0)

## program.q('Type e (Bind X t []) t', vars='e', n=1)
#. e: (V X)

## program.q('Type e [] (Fn t t)', vars='e', n=1)
#. e: (L _.0 (V _.0))

## program.q('Type (L X (L Y (C (V Y) (V X)))) [] t', n=1)
#. t: (Fn _.0 (Fn (Fn _.0 _.1) _.1))

## program.q('Type (L F (L G (L X (C (V F) (C (V G) (V X)))))) [] t', n=1)
#. t: (Fn (Fn _.0 _.1) (Fn (Fn _.2 _.0) (Fn _.2 _.1)))
