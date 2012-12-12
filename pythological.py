from itertools import count

# Variables, values, and substitutions

class Var(object):
    def __init__(self, name):
        self.name = name
    def __repr__(self):
        return self.name

def is_var(x):   return isinstance(x, Var)
def is_tuple(x): return isinstance(x, tuple)

# data S = () | (Var, Val, S)
# where Val = Var | tuple(Val*) | Datum [treated as an atom]
# Invariant: no transitive cycles in the val for any var
# i.e. expand out a val in s, substituting vars, and you
# won't ever run into the val's var.

empty_s = ()

def ext_s_no_check(var, val, s):
    assert s is not None
    return (var, val, s)

def ext_s(var, val, s):
    """Return s plus (var,val) if possible, else None.
    Pre: var is unbound in s."""
    assert s is not None
    return None if occurs(var, val, s) else (var, val, s)

def occurs(var, val, s):
    """Return true if adding (var, val) to s would introduce a cycle.
    Pre: var is unbound in s."""
    # Note the top-level walk in the call from unify is redundant
    assert s is not None
    val = walk(val, s)
    if is_var(val):
        return var is val
    elif is_tuple(val):
        return any(occurs(var, item, s) for item in val)
    else:
        return False

def walk(val, s):
    assert s is not None
    """Return val with substitution s applied enough that the result
    is not a bound variable; it's either a datum or unbound."""
    if is_var(val):
        while s is not ():
            var1, val1, s = s
            if var1 is val: return walk(val1, s)
            assert s is not None
    return val

def unify(u, v, s):
    """Return s plus minimal extensions to make u and v equal mod
    substitution, if possible; else None."""
    assert s is not None
    u = walk(u, s)
    v = walk(v, s)
    if u is v:
        return s
    if is_var(u):
        if is_var(v):
            return ext_s_no_check(u, v, s) # order doesn't matter, right?
        else:
            return ext_s(u, v, s)
    elif is_var(v):
        return ext_s(v, u, s)
    elif (is_tuple(u) and is_tuple(v) and len(u) == len(v)):
        for x, y in zip(u, v):
            s = unify(x, y, s)
            if s is None: return None
        return s
    else:
        return s if u == v else None


# Reifying
## reify(Var('x'), empty_s)
#. _.0

def reify(val, s):
    """Return val with substitutions applied and any unbound variables
    renamed."""
    assert s is not None
    val = walk_full(val, s)
    return walk_full(val, name_vars(val))

def walk_full(val, s):
    """Return val with substitution s fully applied: any variables
    left are unbound."""
    assert s is not None
    val = walk(val, s)
    if is_var(val):
        return val
    elif is_tuple(val):
        return tuple(walk_full(item, s) for item in val)
    else:
        return val

def name_vars(val):
    k, s = count(), [empty_s]
    def recur(val):
        val = walk(val, s[0])
        if is_var(val):
            s[0] = ext_s_no_check(val, ReifiedVar(next(k)), s[0])
        elif is_tuple(val):
            for item in val:
                recur(item)
        else:
            pass
    recur(val)
    return s[0]

def ReifiedVar(k):
    return Var('_.%d' % k)


# Goals
# Let's try making the streams generators.

def eq(u, v):
    def goal(s):
        assert s is not None
        s1 = unify(u, v, s)
        if s1 is not None: yield s1
    return goal

def either(goal1, goal2):
    return lambda s: interleave((goal1(s), goal2(s)))

def interleave(its):
    while its:
        try:
            yield next(its[0])
        except StopIteration:
            its = its[1:]
        else:
            its = its[1:] + (its[0],)

def both(goal1, goal2):
    def goal(s):
        assert s is not None
        for s1 in goal1(s):
            for s2 in goal2(s1):
                yield s2
    return goal

def fresh(names_string, receiver):
    return receiver(*map(Var, names_string.split()))

def delay(thunk):
    return lambda s: thunk()(s)

def run(var, goal, n=None):
    it = goal(empty_s)
    for s, _ in zip(it, count() if n is None else xrange(n)):
        yield reify(var, s)


# Examples

def appendo(x, y, z):
    return either(both(eq(x, ()), eq(y, z)),
                  fresh('xh xt', lambda xh, xt:
                            both(eq(x, (xh, xt)),
                                 fresh('zh zt', lambda zh, zt:
                                           both(eq(z, (zh, zt)),
                                                delay(lambda: appendo(xt, y, zt)))))))

## q = Var('q')
## unify((), (), empty_s)
#. ()
## list(run(q, eq((), ())))
#. [_.0]
## list(run(q, appendo((), (), ())))
#. [_.0]
## list(run(q, appendo((), (), q)))
#. [()]
## list(run(q, appendo((1,()), (), (1,()))))
#. [_.0]
## list(run(q, appendo((1,()), (), q)))
#. [(_.0, ())]
## list(run(q, fresh('a b', lambda a, b: appendo(a, b, q)), n=5))
#. [_.0, (_.0, _.1), (_.0, (_.1, _.2)), (_.0, (_.1, (_.2, _.3))), (_.0, (_.1, (_.2, (_.3, _.4))))]


def nevero(): return delay(lambda: nevero())

### list(run(q, either(nevero(), eq(q, "tea")), n=1))
