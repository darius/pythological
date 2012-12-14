"""
A port of core miniKanren to Python from William Byrd's dissertation chapter 3.
The goal part doesn't try to follow him in any detail, using Python generators
instead.
"""

from itertools import count, islice

# Top level

def run(var, goal, n=None):
    """Return a list of reifications of var from the solutions of goal
    (only the first n solutions, if n given)."""
    solns = gen_solutions(var, goal)
    if n is not None:
        solns = islice(solns, 0, n)
    return list(solns)

def gen_solutions(var, goal):
    "Generate the reifications of var from the solutions of goal."
    for opt_s in goal(empty_s):
        if opt_s is not None:
            yield reify(var, opt_s)


# Goals

# A goal is a function from substitution to generator. Each value we
# generate is an optional substitution, that is: a substitution or
# None. The option of None gives a way to "yield your timeslice" from
# an unproductive subcomputation. (So to feed a result opt_s from one
# generator to another goal, you must first check it and skip it if
# None.)

def eq(val1, val2):
    "Succeed when val1 and val2 unify."
    def goal(s):
        yield unify(val1, val2, s)
    return goal

def either(goal1, goal2):
    """Succeed when goal1 succeeds or goal2 succeeds (not sharing any
    new substitutions between the two)."""
    return lambda s: interleave((goal1(s), goal2(s)))

def interleave(iters):
    """Given a tuple of iterators, generate one value from each, in
    order, cyclically until all are exhausted."""
    while iters:
        try:
            yield next(iters[0])
        except StopIteration:
            iters = iters[1:]
        else:
            iters = iters[1:] + (iters[0],)

def both(goal1, goal2):
    """Succeed when goal1 succeeds and goal2 does too (sharing new
    substitutions)."""
    def goal(s):
        for opt_s1 in goal1(s):
            if opt_s1 is not None:
                for opt_s2 in goal2(opt_s1):
                    yield opt_s2
    return goal

def delay(thunk):
    """A goal equivalent to thunk() but not quite as prone to hanging
    up the larger computation."""
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

def fresh(names_string):
    "Return fresh new variables."
    names = names_string.split()
    return Var(names[0]) if len(names) == 1 else map(Var, names)


# Substitutions (s by convention)
# data S = () | (Var, Val, S)
# Invariant: no transitive cycles in the val for any var. (i.e. take a
# var in s, and fully expand out its val, substituting for vars: in
# doing so you won't ever run into the same var.)

def is_subst(x): return is_tuple(x) and len(x) in (0, 3)

empty_s = ()

def ext_s_no_check(var, val, s):
    assert is_subst(s)
    return (var, val, s)

def ext_s(var, val, s):
    """Return s plus (var: val) if possible, else None.
    Pre: var is unbound in s."""
    assert is_subst(s)
    return None if occurs(var, val, s) else (var, val, s)

def occurs(var, val, s):
    """Would adding (var: val) to s introduce a cycle?
    Pre: var is unbound in s."""
    # Note the top-level walk in the call from unify is redundant
    val = walk(val, s)
    if is_var(val):
        return var is val
    elif is_tuple(val):
        return any(occurs(var, item, s) for item in val)
    else:
        return False

def walk(val, s):
    """Return val with substitution s applied enough that the result
    is not a bound variable; it's either a non-variable or unbound."""
    assert is_subst(s)
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
    assert is_subst(s)
    u = walk(u, s)
    v = walk(v, s)
    if u is v:
        return s
    elif is_var(u):
        if is_var(v):
            return ext_s_no_check(u, v, s)
        else:
            return ext_s(u, v, s)
    elif is_var(v):
        return ext_s(v, u, s)
    elif is_tuple(u) and is_tuple(v) and len(u) == len(v):
        for x, y in zip(u, v):
            s = unify(x, y, s)
            if s is None: break
        return s
    else:
        return s if u == v else None


# Reifying
## x, y = fresh('x y')
## reify((x, y, x, (42,)), empty_s)
#. (_.2, _.1, _.2, (42,))

def reify(val, s):
    """Return val with substitutions applied and any unbound variables
    renamed."""
    val = walk_full(val, s)
    return walk_full(val, name_vars(val))

def walk_full(val, s):
    """Return val with substitution s fully applied: any variables
    left are unbound."""
    val = walk(val, s)
    if is_var(val):
        return val
    elif is_tuple(val):
        return tuple(walk_full(item, s) for item in val)
    else:
        return val

def name_vars(val):
    """Return a substitution renaming all the vars in val to distinct
    ReifiedVars."""
    k = count()
    def renaming(val, s):
        val = walk(val, s)
        if is_var(val):
            s = ext_s_no_check(val, ReifiedVar(next(k)), s)
        elif is_tuple(val):
            for item in val:
                s = renaming(item, s)
        else:
            pass
        return s
    return renaming(val, empty_s)

def ReifiedVar(k):
    return Var('_.%d' % k)


# Convenience syntax

def prologly(fresh_names, make_clauses):
    return lambda *args: case(args, *make_clauses(*fresh(fresh_names)))

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

## a, b = fresh('a b')

## q = fresh('q')
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
## walk(x, (q, 5, (x, q, ())))
#. 5
