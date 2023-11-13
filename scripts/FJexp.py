from functools import reduce

from sage.functions.log import exp
from sage.rings.big_oh import O
from sage.rings.infinity import infinity
from sage.rings.integer import Integer
from sage.rings.function_field.element import FunctionFieldElement_rational
from sage.rings.laurent_series_ring import LaurentSeriesRing
from sage.rings.laurent_series_ring_element import LaurentSeries
from sage.rings.multi_power_series_ring_element import MPowerSeries
from sage.rings.polynomial.polydict import ETuple
from sage.rings.power_series_ring import PowerSeriesRing
from sage.rings.rational import Rational
from sage.rings.rational_field import QQ
from sage.sets.set import Set
from sage.structure.sage_object import SageObject

def exponential(prec):
    Rs = PowerSeriesRing(QQ, "s", default_prec=prec)
    s = Rs.gen()
    return exp(s)

class FJexp(SageObject):
    r"""
    This class represents (scalar-valued) Fourier Jacobi expansions of
    (not necessarily holomorphic)
    Siegel modular forms as power series in q_1,q_2 over a Laurent ring in s.
    Unlike sage, it keeps track of the precision of the coefficients.
    """

    def _init_from_power_series(self, qexp):
#        print("qexp = ", qexp)
#        print("type(qexp) = ", type(qexp))
        self.coeffs = qexp.dict()
        self.prec = qexp.prec()
        self.exps = sorted(self.coeffs.keys())
        if len(self.exps) == 0:
            self.min_val = -infinity
        else:
            self.min_val = self.exps[0][0] + self.exps[0][1]
        # self.min_val = min([e[0] + e[1] for e in self.exps])

    def __init__(self, qexp):
        pow_ser_types = [MPowerSeries]
        if (type(qexp) == FJexp):
            self.coeffs = {k : qexp.coeffs[k] for k in qexp.coeffs.keys()}
            self.prec = qexp.prec
            self.exps = qexp.exps[:]
            self.min_val = qexp.min_val
        elif (type(qexp) == LaurentSeries):
            self.coeffs = {ETuple([0,0]) : qexp}
            self.prec = infinity
            self.exps = [ETuple([0,0])]
            self.min_val = 0
        elif (type(qexp) in [int,Integer,Rational]):
            if (qexp == 0):
                self.coeffs = {}
                self.prec = infinity
                self.exps = []
                self.min_val = -infinity
            else:
                self.coeffs = {ETuple([0,0]) : qexp}
                self.prec = infinity
                self.exps = [ETuple([0,0])]
                self.min_val = 0
        elif (type(qexp) in pow_ser_types):
            self._init_from_power_series(qexp)
        else: # Right now there are power series that we don't know how to check
            self._init_from_power_series(qexp)

    def __str__(self):
        s = ""
        for term_idx,e in enumerate(self.exps):
            q_strs = []
            for idx in range(len(e)):
                q_str = ""
                if (e[idx] == 0):
                    q_strs.append(q_str)
                else:
                    q_str += "*q" + str(idx+1)
                    if (e[idx] >= 2):
                        q_str += "^" + str(e[idx])
                q_strs.append(q_str)
            q_str = reduce(lambda x,y: x+y, q_strs)
            if (term_idx > 0):
                s += " + "
            s += "("  + str(self.coeffs[e]) + ")" +  q_str
        return s + " + O(q1, q2)^" + str(self.prec)

    def __repr__(self):
        return self.__str__()

    def __add__(self, other):
        if (type(other) != FJexp):
            return self.__add__(FJexp(other))
        ret = FJexp(self)
        ret.prec = min(self.prec, other.prec)
        ret.exps = sorted([e for e in list(Set(self.exps).union(Set(other.exps)))
                           if e[0] + e[1] < ret.prec])
        # For now we don't kill off zeros, to not harm precision
        for e in ret.exps:
            ret.coeffs[e] = self.coeffs.get(e,0) + other.coeffs.get(e,0)

        if len(ret.exps) == 0:
            ret.min_val = -infinity
        else:
            ret.min_val = ret.exps[0][0] + ret.exps[0][1]
        return ret

    def __mul__(self, other):
        def add_exps(e1, e2):
            return ETuple([e1[j] + e2[j] for j in range(2)])
        def val_add(v1,v2):
            if (((v1 == infinity) and (v2 == -infinity)) or
                ((v1 == -infinity) and (v2 == infinity))):
                return -infinity
            return v1+v2
        ret = FJexp(self)
        ret.prec = min(val_add(self.min_val,other.prec), val_add(self.prec,other.min_val))
        coeffs = {}
        for e1 in self.exps:
            for e2 in other.exps:
                e = add_exps(e1, e2)
                if (e[0] + e[1] < ret.prec):
                    coeffs[e] = coeffs.get(e,0) + self.coeffs[e1]*other.coeffs[e2]
        ret.coeffs = coeffs
        ret.exps = sorted(list(coeffs.keys()))
        return ret

    def __pow__(self, n):
        ret = FJexp(1)
        for i in range(n):
            ret *= self
        return ret

    def __rmul__(self, r):
        if (r == 0):
            return FJexp(0)
        else:
            ret = FJexp(self)
            ret.coeffs = {k : r*self.coeffs[k] for k in self.exps}
            return ret

    def __radd__(self, r):
        if (self.coeffs == {}):
            ret = FJexp(r)
            ret.prec = self.prec
            return ret
        ret = FJexp(self)
        R = list(self.coeffs.values())[0].parent()
        ret.coeffs[ETuple([0,0])] = ret.coeffs.get(ETuple([0,0]), R(0)) + r
        ret.exps = sorted(ret.coeffs.keys())
        ret.min_val = 0
        return ret

    def __neg__(self):
        return (-1)*self

    def __sub__(self, other):
        return self.__add__(-other)

    def is_weakly_zero(self):
        return all([val == 0 for val in self.coeffs.values()])

    def __eq__(self, other):
        if (type(other) != FJexp):
            return self.__eq__(FJexp(other))
        return (self-other).is_weakly_zero()

class VectorFJexp(SageObject):
    r"""
    This class represents vector-valued Fourier Jacobi expansions of
    (not necessarily holomorphic)
    Siegel modular forms as polynomials in two-variables x, yin
    power series in q_1,q_2 over a Laurent ring in s.
    """

    def _init_from_laurent(self, chi):
        self.coeffs = {}
        for e in chi.dict().keys():
            self.coeffs[e] = FJexp(chi.dict()[e])
            self.exps = sorted(list(self.coeffs.keys()))

    def _init_from_func_field(self, chi, prec):
        assert prec >= 2
        self.coeffs = {}
        exps = list(chi.dict().keys())
        Rs = LaurentSeriesRing(QQ, "s")
        s = Rs.gen()
        Rsq = PowerSeriesRing(Rs, ["q1", "q2"])
        q1, q2 = Rsq.gens()
        exp_s = Rs(exponential(prec))
        for e in chi.dict().keys():
            mon = chi.dict()[e]
            mon_exps = list(mon.dict().keys())
            res_mon = FJexp(0)
            for mon_exp in mon_exps:
                f = mon.dict()[mon_exp]
                f_pow = FJexp(f.numerator().subs(exp_s) / f.denominator().subs(exp_s))
                res_mon += f_pow * FJexp(q1**mon_exp[0] * q2**mon_exp[1])
            self.coeffs[e] = res_mon
            if (mon.prec() < infinity):
                self.coeffs[e] += FJexp(O(q1**mon.prec()))
        self.exps = sorted(list(self.coeffs.keys()))

    def _init_from_list(self, exps, coeffs):
        assert len(exps) == len(coeffs)
        self.exps = sorted(exps)
        self.coeffs = { exps[i] : coeffs[i] for i in range(len(exps))}

    def _init_from_int(self, a):
        self.exps = [ETuple([0,0])]
        self.coeffs = { ETuple([0,0]) : FJexp(a) }

    def __init__(self, chi, prec=0):
        func_field_elt = FunctionFieldElement_rational
        laurent_elt = LaurentSeries
        if (type(chi) == VectorFJexp):
            self.coeffs = {k : FJexp(chi.coeffs[k]) for k in chi.coeffs.keys()}
            self.exps = chi.exps
        elif (type(chi) in [int, Integer]):
            self._init_from_int(chi)
        elif (type(chi) == list):
            self._init_from_list(chi[0], chi[1])
        elif (type(chi.parent().base().base().gen()) == laurent_elt):
            self._init_from_laurent(chi)
        elif (type(chi.parent().base().base().gen()) == func_field_elt):
            self._init_from_func_field(chi, prec)

    def __str__(self):
        s = ""
        xy_names = ["x", "y"]
        for term_idx,e in enumerate(self.exps):
            xy_strs = []
            for idx in range(len(e)):
                xy_str = ""
                if (e[idx] == 0):
                    xy_strs.append(xy_str)
                else:
                    xy_str += "*" + xy_names[idx]
                    if (e[idx] >= 2):
                        xy_str += "^" + str(e[idx])
                xy_strs.append(xy_str)
            xy_str = reduce(lambda x,y: x+y, xy_strs)
            if (term_idx > 0):
                s += " + "
            s += "("  + str(self.coeffs[e]) + ")" +  xy_str
        return s

    def __repr__(self):
        return self.__str__()

    def __add__(self, other):
        ret = VectorFJexp(self)
        ret.exps = sorted([e for e in list(Set(self.exps).union(Set(other.exps)))])
        # For now we don't kill off zeros, to not harm precision
        for e in ret.exps:
            ret.coeffs[e] = self.coeffs.get(e,0) + other.coeffs.get(e,0)
        return ret

    def __mul__(self, other):
        def add_exps(e1, e2):
            return ETuple([e1[j] + e2[j] for j in range(2)])
        ret = VectorFJexp(self)
        coeffs = {}
        for e1 in self.exps:
            for e2 in other.exps:
                e = add_exps(e1, e2)
                coeffs[e] = coeffs.get(e,0) + self.coeffs[e1]*other.coeffs[e2]
        ret.coeffs = coeffs
        ret.exps = sorted(list(coeffs.keys()))
        return ret

    def __pow__(self, n):
        ret = VectorFJexp(1)
        for i in range(n):
            ret *= self
        return ret

    def __rmul__(self, r):
        if (r == 0):
            return  VectorFJexp(0)
        else:
            ret = VectorFJexp(self)
            ret.coeffs = {k : r*ret.coeffs[k] for k in ret.exps}
            return ret

    def __radd__(self, r):
        ret = VectorFJexp(self)
        ret.coeffs[ETuple([0,0])] = ret.coeffs.get(ETuple([0,0]), 0) + r
        ret.exps = sorted(ret.coeffs.keys())
        return self

    def __neg__(self):
        return (-1)*self

    def __sub__(self, other):
        return self.__add__(-other)

    def is_weakly_zero(self):
        return all([val == 0 for val in self.coeffs.values()])

    def __eq__(self, other):
        if (type(other) != VectorFJexp):
            return self.__eq__(VectorFJexp(other))
        return (self-other).is_weakly_zero()
