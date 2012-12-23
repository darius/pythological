"""
Sketch of a friendly syntax frontend.
"""

## for name, fvs, _ in parser.program(example): print name, ' '.join(sorted(fvs))
#. Append ys
#. Append x xs ys zs
#. Member x
#. Member x xs
#. Main hs owns
#. Zebra hs owns
#. Left_and_middle 
#. Next_to a b c
#. Next_to a b c
#. Left_of a b c
#. 

## from pythological import fresh, run
## q, a, b = fresh('q a b')
## def test(name, *args): return run(q, program[name](*args))
## program = mk_program(parser.program(example))
## program = collect_rules(parser.program(example))
## program.keys()
#. ['Next_to', 'Left_of', 'Member', 'Zebra', 'Main', 'Left_and_middle', 'Append']
## test('Member', q, ())
#. []
## test('Member', q, ('Cons', 5, ()))
#. [5]
## test('Member', q, ('Cons', a, ()))
#. [_.0]
## test('Member', q, ('Cons', 22, ('Cons', 137, ())))
#. [22, 137]
## run(q, both(eq(q, (a, b)), program['Zebra'](a, b)))
#. []

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

rule = predicate '<-'_ calls '.'_   :mk_rule
     | predicate             '.'_   :mk_fact.

predicate = symbol term*   :mk_predicate.

calls = call (','_ call)*   :hug.

call = symbol term*   :mk_call.

term = '('_ term ')'_
     | symbol term*   :mk_compound
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

_ = /\s*/.
"""

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
    program = dict((symbol, make_function(symbol, pairs))
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
