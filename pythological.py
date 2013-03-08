"""
A port of core miniKanren to Python from William Byrd's dissertation chapter 3.
https://scholarworks.iu.edu/dspace/bitstream/handle/2022/8777/Byrd_indiana_0093A_10344.pdf
The goal part doesn't try to follow him in any detail, using Python generators
instead.
"""

from itertools import islice

# Top level

def run(var, goal, n=None):
    """Return a list of reifications of var from the solutions of goal
    (only the first n solutions, if n given)."""
    solns = gen_solutions(var, goal)
    return list(solns if n is None else islice(solns, 0, n))

def gen_solutions(var, goal):
    "Generate the reifications of var from the solutions of goal."
    return (reify(var, opt_s) for opt_s in goal(empty_s) if opt_s is not None)


# Goals

# A goal is a function from substitution to generator. Each value we
# generate is an optional substitution -- that is, a substitution or
# None. The option of None gives a way to "yield your timeslice" from
# an unproductive subcomputation. (So to feed a result opt_s from one
# generator to another goal, you must first check it and skip it if
# None.)

def fail(s):
    return iter(())

def succeed(s):
    yield s

def eq(val1, val2):
    "Succeed when val1 and val2 unify."
    def goal(s): yield unify(val1, val2, s)
    return goal

def either(goal1, goal2):
    """Succeed when goal1 succeeds or goal2 succeeds (not sharing any
    new substitutions between the two)."""
    return lambda s: interleave((goal1(s), goal2(s)))

def interleave(iters):
    """Given a tuple of iterators, generate one value from each, in
    order, cyclically until all are exhausted."""
    while iters:
        try:                  yield next(iters[0])
        except StopIteration: iters = iters[1:]
        else:                 iters = iters[1:] + (iters[0],)

def both(goal1, goal2):
    "Succeed when goal1 and goal2 both succeed (sharing new substitutions)."
    return lambda s: (opt_s2 
                      for opt_s1 in goal1(s) if opt_s1 is not None
                      for opt_s2 in goal2(opt_s1))

def delay(thunk):
    "A goal equivalent to thunk() but less prone to hanging up the computation."
    def goal(s):
        # Keep from hogging the scheduler if recursion never yields anything:
        yield None
        for opt_s in thunk()(s):
            yield opt_s
    return goal


# Variables and values (var and val by convention)
# Val = Var | tuple(Val*) | Atom [any other type, treated as an atom]

def is_var(x):   return isinstance(x, Var)
def is_tuple(x): return isinstance(x, tuple)
def is_atom(x):  return not (is_var(x) or is_tuple(x))

class Var(object):
    "A variable."
    def __init__(self, name):
        self.name = name
    def __repr__(self):
        return self.name


# Substitutions (s by convention)
# data S = () | (Var, Val, S)
# Invariant: no transitive cycles in the val for any var. (i.e. take a
# var in s, and fully expand out its val, substituting for vars: in
# doing so you won't ever run into the same var.)

def is_subst(x): return is_tuple(x) and len(x) in (0, 3)

empty_s = ()

def extend_unchecked(var, val, s):
    return (var, val, s)

def extend(var, val, s):
    """Return s plus (var: val) if possible, else None.
    Pre: var is unbound in s."""
    return None if occurs(var, val, s) else (var, val, s)

def occurs(var, val, s):
    """Would adding (var: val) to s introduce a cycle?
    Pre: var is unbound in s."""
    # Note the top-level substitute in the call from unify is redundant
    val = substitute(val, s)
    return (var is val
            or (is_tuple(val) and any(occurs(var, item, s) for item in val)))

def substitute(val, s):
    """Return val with substitution s applied enough that the result
    is not a bound variable; it's either a non-variable or unbound."""
    while is_var(val):
        s1 = s
        while s1 is not ():
            var1, val1, s1 = s1
            if var1 is val:
                val = val1
                break
        else:
            break
    return val

def unify(u, v, s):
    """Return s plus minimal extensions to make the vals u and v equal
    mod substitution, if possible; else None."""
    u = substitute(u, s)
    v = substitute(v, s)
    if u is v:
        return s
    elif is_var(u):
        return (extend_unchecked if is_var(v) else extend)(u, v, s)
    elif is_var(v):
        return extend(v, u, s)
    elif is_tuple(u) and is_tuple(v) and len(u) == len(v):
        for ui, vi in zip(u, v):
            s = unify(ui, vi, s)
            if s is None: break
        return s
    else:
        return s if u == v else None

def reify(val, s):
    "Return val with substitutions applied and free variables renamed."
    free_vars = {}
    def reifying(val):
        val = substitute(val, s)
        if is_var(val):
            if val not in free_vars:
                free_vars[val] = Var('_.%d' % len(free_vars))
            return free_vars[val]
        elif is_tuple(val):
            return tuple(map(reifying, val))
        else:
            return val
    return reifying(val)


# Convenience syntax

def fresh(names_str):
    "Return fresh new variables."
    names = names_str.split()
    return Var(names[0]) if len(names) == 1 else map(Var, names)

def prologly(names_str, make_clauses):
    return lambda *args: case(args, *make_clauses(*map(Var, names_str.split())))

def case(subject, *clauses):
    return cond(*[[eq(subject, clause[0])] + clause[1:]
                  for clause in clauses])

def cond(conjunction, *conjunctions):
    goal = conjoin(*conjunction)
    return either(goal, cond(*conjunctions)) if conjunctions else goal

def conjoin(goal, *goals):
    return both(goal, conjoin(*goals)) if goals else goal


# Debugging

def show_s(opt_s):
    "Return a more human-readable repr of a substitution."
    if opt_s is None: return 'None'
    s = opt_s
    bindings = []
    while s is not ():
        var, val, s = s
        bindings.append('%s: %s' % (var, val))
    return '  '.join(bindings)


# Examples

def old_appendo(x, y, z):
    xh, xt, zt = fresh('xh xt zt')
    return cond([eq((x, y), ((), z))],
                [eq(x, (xh, xt)),
                 eq(z, (xh, zt)),
                 delay(lambda: appendo(xt, y, zt))])
    # Or better without the sugar?
    return either(eq((x, y),
                     ((), z)),
                  both(eq((x, z),
                          ((xh, xt), (xh, zt))),
                       delay(lambda: appendo(xt, y, zt))))

def appendo(*args):
    y, z, h, xt, zt = fresh('y z h xt zt')
    return cond([eq(args, ((), z, z))],
                [eq(args, ((h, xt), y, (h, zt))),
                 delay(lambda: appendo(xt, y, zt))])

def appendo(*args):
    y, h, xt, zt = fresh('y h xt zt')
    return case(args,
                [((), y, y)],
                [((h, xt), y, (h, zt)),
                 delay(lambda: appendo(xt, y, zt))])

appendo = prologly('y h xt zt',
                   lambda y, h, xt, zt:
                       ([((), y, y)],
                        [((h, xt), y, (h, zt)),
                         delay(lambda: appendo(xt, y, zt))]))

membero = prologly('x t _',
                   lambda x, t, _:
                       ([(x, (x, _))],
                        [(x, (_, t)),
                         delay(lambda: membero(x, t))]))

## q = fresh('q')
## a, b = fresh('a b')

## run(q, membero(q, (b, (a, ()))))
#. [_.0, _.0]

## unify((), (), empty_s)
#. ()
## run(q, eq((), ()))
#. [_.0]
## run(q, appendo((), (), ()))
#. [_.0]
## run(q, appendo((), (), q))
#. [()]
## run(q, appendo((1,()), (), (1,())))
#. [_.0]
## run(q, appendo((1,()), (), q))
#. [(1, ())]
## run(q, appendo(a, b, q), n=5)
#. [_.0, (_.0, _.1), (_.0, (_.1, _.2)), (_.0, (_.1, (_.2, _.3))), (_.0, (_.1, (_.2, (_.3, _.4))))]
## for r in run(q, both(eq(q, (a, b)), appendo(a, b, (4, (3, (2, (1, ()))))))): print r
#. ((), (4, (3, (2, (1, ())))))
#. ((4, ()), (3, (2, (1, ()))))
#. ((4, (3, ())), (2, (1, ())))
#. ((4, (3, (2, ()))), (1, ()))
#. ((4, (3, (2, (1, ())))), ())
#. 

## for r in run(q, both(eq(q, (a, b)), appendo(a, b, (1, ())))): print r
#. ((), (1, ()))
#. ((1, ()), ())
#. 

def nevero(): return delay(lambda: nevero())

## run(q, either(nevero(), eq(q, "tea")), n=1)
#. ['tea']

## list(islice(nevero()(empty_s), 0, 5))
#. [None, None, None, None, None]

## q, x = Var('q'), Var('x')
## substitute(x, (q, 5, (x, q, ())))
#. 5

## x, y = fresh('x y')
## reify((x, y, x, x, (42,)), empty_s)
#. (_.0, _.1, _.0, _.0, (42,))
