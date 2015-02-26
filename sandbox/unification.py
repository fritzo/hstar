from functools import partial
from collections import deque

alphabet = 'abcdefghijklmnopqrstuvwxyz'


def VAR(name):
    assert isinstance(name, basestring)
    assert ' ' not in name
    return ('VAR', name)


def EXP(dom, cod):
    return ('EXP', dom, cod)


def APP(lhs, rhs):
    return ('APP', lhs, rhs)


def LAMBDA(name, expr):
    assert ' ' not in name
    assert isinstance(name, basestring)
    return ('LAMBDA', name, expr)


def OF_TYPE(expr, tp):
    return ('OF_TYPE', expr, tp)


def pretty(expr):
    if isinstance(expr, basestring):
        return expr
    else:
        return ' '.join(map(pretty, expr))


def tuple_map(fun, tup):
    return tuple(fun(x) for x in tup)


def inplace_map(fun, mutable_list):
    for i, item in enumerate(mutable_list):
        mutable_list[i] = fun(item)


def sub(name, defn, expr):
    if expr[0] == 'VAR':
        if expr[1] == name:
            return defn
        else:
            return expr
    elif expr[0] == 'EXP':
        return ('EXP', sub(name, defn, expr[1]), sub(name, defn, expr[2]))


def occurs(name, expr):
    if expr[0] == 'VAR':
        return name == expr[1]
    elif expr[0] == 'EXP':
        return occurs(name, expr[1]) or occurs(name, expr[2])


class UnificationFailure(Exception):
    pass


def unify(equation_queue):
    assert isinstance(equation_queue, deque)
    subs = deque()

    def unify_one(name, expr):
        if occurs(lhs[1], rhs):
            raise UnificationFailure
        else:
            s = partial(tuple_map, partial(sub, lhs[1], rhs))
            inplace_map(s, equation_queue)
            inplace_map(s, subs)
            subs.appendleft(VAR(name), expr)

    while equation_queue:
        lhs, rhs = equation_queue.pop()
        if lhs[1] == rhs[1]:
            continue
        if lhs[0] == 'VAR':
            unify_one(lhs[1], rhs)
        elif rhs[0] == 'VAR':
            unify_one(rhs[1], lhs)
        else:
            equation_queue.appendleft(lhs[1], rhs[1])
            equation_queue.appendleft(lhs[2], rhs[2])

    return subs
