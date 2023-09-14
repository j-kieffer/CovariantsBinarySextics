
from sage.rings.infinity import infinity
from sage.rings.polynomial.polydict import ETuple
from sage.structure.sage_object import SageObject

class FJexp(SageObject):
    r"""
    This class represents (scalar-valued) Fourier Jacobi expansions of 
    (not necessarily holomorphic)
    Siegel modular forms as power series in q_1,q_2 over a Laurent ring in s.
    Unlike sage, it keeps track of the precision of the coefficients.
    """

    def _init_from_power_series(self, qexp):
        self.coeffs = qexp.dict()
        self.prec = qexp.prec()
        self.exps = sorted(self.coeffs.keys())
        self.min_val = self.exps[0][0] + self.exps[0][1]
        # self.min_val = min([e[0] + e[1] for e in self.exps])
    
    def __init__(self, qexp):
        if (type(qexp) == sage.rings.multi_power_series_ring_element.MPowerSeries):
            self._init_from_power_series(qexp)
        elif (type(qexp) == sage.rings.laurent_series_ring_element.LaurentSeries):
            self.coeffs = {ETuple([0,0]) : qexp}
            self.prec = infinity
            self.exps = [ETuple([0,0])]
            self.min_val = 0

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
        self.prec = min(self.prec, other.prec)
        self.exps = sorted([e for e in list(Set(self.exps).union(Set(other.exps)))
                           if e[0] + e[1] < self.prec])
        for e in self.exps:
            self.coeffs[e] = self.coeffs.get(e,0) + other.coeffs.get(e,0)
        return self

    def __mul__(self, other):
        def add_exps(e1, e2):
            return ETuple([e1[j] + e2[j] for j in range(2)])
        self.prec = min(self.min_val + other.prec, self.prec + other.min_val)
        coeffs = {}
        for e1 in self.exps:
            for e2 in other.exps:
                e = add_exps(e1, e2)
                coeffs[e] = coeffs.get(e,0) + self.coeffs[e1]*other.coeffs[e2]
        self.coeffs = coeffs
        self.exps = sorted(list(coeffs.keys()))
        return self

class VectorFJexp(SageObject):
    r"""
    This class represents vector-valued Fourier Jacobi expansions of 
    (not necessarily holomorphic)
    Siegel modular forms as polynomials in two-variables x, yin 
    power series in q_1,q_2 over a Laurent ring in s.
    """
    def __init__(self, t_chi):
        self.coeffs = t_chi.coefficients()

    def __str__(self):
        s = ""
        for i, coeff in enumerate(self.coeffs):
            mon_str = "*x^"
            s += "(" + str(coeff) + ")" + mon_str 
        return s
        
    def foo():
        exps = list(chi.dict().keys())
        Rs = LaurentSeriesRing(QQ, "s")
        s = Rs.gen()
        Rsq = PowerSeriesRing(Rs, ["q1", "q2"])
        q1, q2 = Rsq.gens()        
        Rsqxy = PolynomialRing(Rsq, ["x", "y"])
        x, y = Rsqxy.gens()
        res = Rsqxy(0)
        exp_s = Rs(exponential(prec))
        for e in exps:
            mon = chi.dict()[e]
            mon_exps = list(mon.dict().keys())
            res_mon = Rsq(0)
            for mon_exp in mon_exps:
                f = mon.dict()[mon_exp]    
                f_pow = FJExp(f.numerator().subs(exp_s) / f.denominator().subs(exp_s))
                res_mon += f_pow * FJExp(q1**mon_exp[0] * q2**mon_exp[1])
                res += res_mon * x**e[0] * y**e[1]
        return res
