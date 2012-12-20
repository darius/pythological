"""
Sketch of a friendly syntax frontend.
"""

## grammar.program(append)
#. ('Append(Nil(ys, ys)) :- true', 'Append(Cons(x, xs), ys, Cons(x, zs)) :- Append(xs, ys, zs)', 'Member(x, Cons(x, _)) :- true', 'Member(x, Cons(_, xs)) :- Member(x, xs)')

## for x in grammar.program(zebra): print x
#. Zebra(owns, hs) :- Left_and_middle(hs), Left_of(H(Green(_, _, Coffee(_))), H(White(_, _, _, _)), hs), Next_to(H(_, _, _, _, Blend()), H(_, _, Cats(_, _)), hs), Next_to(H(_, _, _, _, Dunhill()), H(_, _, Horse(_, _)), hs), Next_to(H(_, Norwegian(_, _, _)), H(Blue(_, _, _, _)), hs), Next_to(H(_, _, _, _, Blend()), H(_, _, _, Water(_)), hs), Member(H(Red(English(_, _, _))), hs), Member(H(_, Swede(Dog(_, _))), hs), Member(H(_, Dane(_, Tea(_))), hs), Member(H(_, _, Birds(_, Pallmall())), hs), Member(H(Yellow(_, _, _, Dunhill())), hs), Member(H(_, _, _, Beer(Bluemaster())), hs), Member(H(_, German(_, _, Prince())), hs), Member(H(_, owns, Zebra(_, _)), hs)
#. Left_and_middle(Cons(H(_, Norwegian(_, _, _)), Cons(_, Cons(H(_, _, _, Milk(_)), Cons(_, Cons(_, Nil())))))) :- true
#. Next_to(a, b, c) :- Left_of(a, b, c)
#. Next_to(a, b, c) :- Left_of(b, a, c)
#. Left_of(a, b, c) :- Append(_, Cons(a, Cons(b, _)), c)
#. 

append = """
Append Nil ys ys.
Append (Cons x xs) ys (Cons x zs) <- Append xs ys zs.

Member x (Cons x _).
Member x (Cons _ xs) <- Member x xs.
"""

zebra = """
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

from parson import Grammar, hug, join
from pythological import run, eq, either, both, delay, Var

grammar = Grammar(r"""
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
""")(mk_fact      = lambda predicate: '%s :- true' % predicate,
     mk_rule      = lambda predicate, body: '%s :- %s' % (predicate, ', '.join(body)),
     mk_predicate = lambda symbol, *terms: '%s(%s)' % (symbol, ', '.join(terms)),
     mk_call      = lambda symbol, *terms: '%s(%s)' % (symbol, ', '.join(terms)),
     mk_compound  = lambda symbol, *terms: '%s(%s)' % (symbol, ', '.join(terms)),
     mk_literal   = lambda s: s,
     mk_variable  = lambda s: s,
     mk_anon      = lambda s: s,
     int = int,
     join = join,
     hug = hug)

