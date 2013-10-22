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

q, a, b = fresh('q a b')

I = ('L', 'x', ('V', 'x'))
I_type = ('Fn', a, a)

## run(q, program['Type'](I, ('Nil',), q))
#. [('Fn', _.0, _.0)]

## run(q, program['Type'](q, ('Bind', 'x', a, ('Nil',)), a), n=1)
#. [('V', 'x')]

## run(q, program['Type'](q, ('Nil',), I_type), n=1)
#. [('L', _.0, ('V', _.0))]
# import sys; sys.setrecursionlimit(5000)
