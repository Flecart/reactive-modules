"""Finite collection layouts expanded into ordinary RM expressions."""
from . import Int, Bool, LIA
from .expr import Expr, expr, ite as _ite
from .protocol import Field


def ite(condition, yes, no):
    """LIA scalar conditional, including two literal branches."""
    if not isinstance(yes, Expr) and not isinstance(no, Expr):
        yes = expr(yes, theory=LIA, sort=(Bool if type(yes) is bool else Int)([1,1]))
    return _ite(condition, yes, no)


def select(values, index, default=0):
    result = default
    for i, value in reversed(list(enumerate(values))):
        result = ite(index == i, value, result)
    return result


def any_of(values):
    values = list(values)
    if not values: raise ValueError("empty symbolic disjunction")
    result = values[0]
    for value in values[1:]: result = result | value
    return result


def all_of(values):
    values = list(values)
    if not values: raise ValueError("empty symbolic conjunction")
    result = values[0]
    for value in values[1:]: result = result & value
    return result


class FiniteMap:
    def __init__(self, prefix, keys, default=0):
        self.prefix, self.keys, self.default = prefix, tuple(keys), default

    def schema(self):
        return {name: Field(value) for key in self.keys
                for name,value in ((f"{self.prefix}_has_{key}",0),(f"{self.prefix}_{key}",self.default))}

    def put(self, state, key, value, guard):
        for k in self.keys:
            condition = guard & (key == k)
            for name, v in ((f"{self.prefix}_has_{k}",1),(f"{self.prefix}_{k}",value)):
                state[name] = ite(condition,v,state[name])


class MembershipSet:
    def __init__(self, prefix, members): self.prefix, self.members = prefix, tuple(members)

    def schema(self): return {f"{self.prefix}_{m}":Field() for m in self.members}

    def add(self, state, member, guard):
        for m in self.members:
            name = f"{self.prefix}_{m}"
            state[name] = ite(guard & (member == m),1,state[name])

    def size(self,state): return sum(state[f"{self.prefix}_{m}"] for m in self.members)


class OrderedCounter:
    def __init__(self,prefix,keys): self.prefix,self.keys=prefix,tuple(keys)

    def schema(self):
        return {f"{self.prefix}_next":Field(), **{f"{self.prefix}_{kind}_{k}":Field()
                for kind in ("count","rank") for k in self.keys}}

    def increment(self,state,key,guard):
        for k in self.keys:
            count,rank,nxt = (f"{self.prefix}_count_{k}",f"{self.prefix}_rank_{k}",f"{self.prefix}_next")
            active=guard & (key == k)
            first=active & (state[count] == 0)
            state[rank]=ite(first,state[nxt],state[rank])
            state[nxt]=ite(first,state[nxt]+1,state[nxt])
            state[count]=ite(active,state[count]+1,state[count])

    def most_common(self,state,default):
        best,rank,choice=0,len(self.keys),default
        for k in self.keys:
            count,r=state[f"{self.prefix}_count_{k}"],state[f"{self.prefix}_rank_{k}"]
            win=(count>best)|((count==best)&(count!=0)&(r<rank))
            choice,rank,best=ite(win,k,choice),ite(win,r,rank),ite(win,count,best)
        return choice,best
