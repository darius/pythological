"""
Sketch of a friendly syntax frontend.
"""

## from pythological import fresh, run
## program = collect_rules(parser.program(example))
## program.keys()
#. ['Next_to', 'Left_of', 'Member', 'Zebra', 'Main', 'Left_and_middle', 'Append']
## program.query('Member q Nil')
#. []
## program.query('Member x (Cons 5 Nil)')
#. [{'x': 5}]
## program.query('Member x (Cons a Nil)')
#. [{'a': _.0, 'x': _.0}]
## program.query('Member x (Cons 22 (Cons 137 Nil))')
#. [{'x': 22}, {'x': 137}]
## program.query('Member x a', n=3)
#. [{'a': ('Cons', _.0, _.1), 'x': _.0}, {'a': ('Cons', _.0, ('Cons', _.1, _.2)), 'x': _.1}, {'a': ('Cons', _.0, ('Cons', _.1, ('Cons', _.2, _.3))), 'x': _.2}]
### run(q, both(eq(q, (a, b)), program['Zebra'](a, b)))

example = """
Append Nil ys ys.
Append (Cons x xs) ys (Cons x zs) <- Append xs ys zs.

Member x (Cons x _).
Member x (Cons _ xs) <- Member x xs.

Main owns hs <- Zebra owns hs.

Zebra owns hs <-
    Left_and_middle hs,
    Left_of (H Green _ _ Coffee _)    (H White _ _ _ _)  hs,
    Next_to (H _ _ _ _ Blend)         (H _ _ Cats  _ _)  hs,
    Next_to (H _ _ _ _ Dunhill)       (H _ _ Horse _ _)  hs,
    Next_to (H _ Norwegian _ _ _)     (H Blue _ _ _ _)   hs,
    Next_to (H _ _ _ _ Blend)         (H _ _ _ Water _)  hs,
    Member  (H Red English _ _ _)     hs,
    Member  (H _ Swede Dog _ _)       hs,
    Member  (H _ Dane _ Tea _)        hs,
    Member  (H _ _ Birds _ Pallmall)  hs,
    Member  (H Yellow _ _ _ Dunhill)  hs,
    Member  (H _ _ _ Beer Bluemaster) hs,
    Member  (H _ German _ _ Prince)   hs,
    Member  (H _ owns Zebra _ _)      hs.

Left_and_middle (Cons (H _ Norwegian _ _ _)
                 (Cons _
                  (Cons (H _ _ _ Milk _)
                   (Cons _
                    (Cons _ Nil))))).

Next_to a b c <- Left_of a b c.
Next_to a b c <- Left_of b a c.

Left_of a b c <- Append _ (Cons a (Cons b _)) c.
"""

import collections
from parson import Grammar, hug, join
from pythological import run, Var, fail, succeed, eq, either, both, delay

grammar = r"""
program = _ rule* ~/./.
query = _ call ~/./.

rule = predicate '<-'_ calls '.'_   :mk_rule
     | predicate             '.'_   :mk_fact.

predicate = symbol term*   :mk_predicate.

calls = call (','_ call)*   :hug.

call = symbol term*   :mk_call.

term = '('_ symbol term* ')'_  :mk_compound
     | symbol         :mk_compound
     | variable       :mk_variable
     | anonvar        :mk_anon
     | number         :mk_literal
     | string         :mk_literal.

symbol   = /([A-Z]\w*)/_.
variable = /([a-z]\w*)/_.
anonvar  = /(_\w*)/_.

number = /(\d+)/_   :int.   # TODO more

string = '"' qchar* '"'_  :join.
qchar = /[^"]/.  # TODO more

_ = /\s*/.   # TODO comments
"""

class Program(dict):
    def query(self, string, n=None):
        (fvs, ev), = parser.query(string)
        variables = tuple(map(Var, fvs))
        q = Var('q')
        results = run(q, both(eq(q, variables),
                              ev(self, (), dict(zip(fvs, variables)))),
                      n=n)
        return [dict(zip(fvs, result)) for result in results]

def parse(string):
    return collect_rules(parser.program(string))

def mk_program(rules):
    program = collect_rules(rules)
    return program['Main']

def collect_rules(rules_tuple):
    rules = collections.defaultdict(list)
    for symbol, fvs, ev in rules_tuple:
        rules[symbol].append((fvs, ev))
    def make_function(symbol, pairs):
        fvs, ev = collect(pairs)
        def fn(*args):
            variables = dict((name, Var(name)) for name in fvs)
            return foldr(either, fail, ev(program, args, variables))
        return fn
    program = Program((symbol, make_function(symbol, pairs))
                      for symbol, pairs in rules.items())
    return program

def collect(pairs):
    fvs = set().union(*[fvs for fvs, _ in pairs])
    evs = [ev for _, ev in pairs]
    return fvs, (lambda program, args, variables:
                     tuple(ev(program, args, variables) for ev in evs))
    
def mk_rule(predicate, calls):
    symbol, head_fvs, head_ev = predicate
    call_fvs, ev_calls = collect(calls)
    fvs = head_fvs | call_fvs
    return symbol, fvs, (lambda program, args, variables:
                          both(eq(args, head_ev(program, args, variables)),
                               foldr(both, succeed, ev_calls(program,
                                                             args,
                                                             variables))))

def mk_predicate(symbol, *terms):
    fvs, ev_terms = collect(terms)
    return symbol, fvs, ev_terms

def mk_call(symbol, *terms):
    fvs, ev_terms = collect(terms)
    return fvs, (lambda program, args, variables:
                     delay(lambda: program[symbol](*ev_terms(program,
                                                             args,
                                                             variables))))

def mk_compound(symbol, *terms):
    fvs, ev_terms = collect(terms)
    return fvs, (lambda program, args, variables:
                     (symbol,) + ev_terms(program, args, variables))

def mk_literal(value):
    return set(), lambda program, args, variables: value

def mk_anon(name):
    return set(), lambda program, args, variables: Var(name)

def mk_variable(name):
    return set([name]), lambda program, args, variables: variables[name]

parser = Grammar(grammar)(mk_fact      = lambda predicate: mk_rule(predicate, []),
                          mk_rule      = mk_rule,
                          mk_predicate = mk_predicate,
                          mk_call      = mk_call,
                          mk_compound  = mk_compound,
                          mk_literal   = mk_literal,
                          mk_variable  = mk_variable,
                          mk_anon      = mk_anon,
                          int = int,
                          join = join,
                          hug = hug)

def foldr(f, z, xs):
    for x in reversed(xs):
        z = f(x, z)
    return z
