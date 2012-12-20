"""
Sketch of a friendly syntax frontend.
"""

## grammar.program(append)
#. ('Append(Nil(ys, ys)) :- true', 'Append(Cons(x, xs), ys, Cons(x, zs)) :- Append(xs, ys, zs)', 'Member(x, Cons(x, _)) :- true', 'Member(x, Cons(_, xs)) :- Member(x, xs)')

append = """
Append Nil ys ys.
Append (Cons x xs) ys (Cons x zs) <- Append xs ys zs.

Member x (Cons x _).
Member x (Cons _ xs) <- Member x xs.
"""

from parson import Grammar, hug, join
from pythological import run, eq, either, both, delay, Var

grammar = Grammar(r"""
program = _ rule* ~/./.

rule = call '<-'_ predicates '.'_   :mk_rule
     | call                  '.'_   :mk_fact.

predicates = predicate (','_ predicate)*   :hug.

predicate = call.

call = symbol term*   :mk_call.

term = '('_ term ')'_
     | variable
     | symbol term*   :mk_call  # XXX
     | number
     | string.

variable = /([a-z_]\w*)/_.
symbol = /([A-Z]\w*)/_.

number = /(\d+)/_   :int.   # TODO more
string = '"' qchar* '"'_  :join :mk_string.
qchar = /[^"]/.  # TODO more

_ = /\s*/.
""")(mk_fact = lambda predicate: '%s :- true' % predicate,
     mk_rule = lambda predicate, body: '%s :- %s' % (predicate, ', '.join(body)),
     mk_call = lambda symbol, *terms: '%s(%s)' % (symbol, ', '.join(terms)),
     mk_string = repr,
     int = int,
     join = join,
     hug = hug)
