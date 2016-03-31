"""
Well-typed expressions in the simply-typed lambda calculus.
# XXX LookUp needs disunify to avoid shadowed bindings
"""

from parser import parse, unparse
from pythological import fresh, run, both, eq

example = """

Type (V x)   r type              <- LookUp r x type.
Type (L x e) r (Fn domain range) <- Type e (Bind x domain r) range.
Type (C f e) r range             <- Type f r (Fn domain range),
                                    Type e r domain.

LookUp (Bind key val _) key val.
LookUp (Bind _ _ r)     key val  <- LookUp r key val.
"""
program = parse(example)

# import sys; sys.setrecursionlimit(5000)

## program.q('Type (L x (V x)) [] t', vars='t')
#. t: (Fn _.0 _.0)

## program.q('Type e (Bind X t []) t', vars='e', n=1)
#. e: (V X)

## program.q('Type e [] (Fn t t)', vars='e', n=1)
#. e: (L _.0 (V _.0))
