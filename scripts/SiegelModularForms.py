from functools import reduce
from sage.structure.sage_object import SageObject
from sage.matrix.constructor import Matrix
from sage.modules.free_module import VectorSpace
from sage.rings.big_oh import O
from sage.rings.infinity import infinity
from sage.rings.rational_field import QQ
from sage.sets.set import Set

from BinarySexticsCovariants import BinarySexticsCovariants as BSC
from FJexp import VectorFJexp, FJexp
from ThetaFourier import get_chi6m2

class SMF(SageObject):
    r"""
    Constructs Siegel modular forms of weight (k,j) (degree 2)

    sage: SMF(4,0).GetBasis()
    [-Co20^2 + 3*Co40]

    sage: SMF(6,0).GetBasis()
    [-28*Co20^3 + 57*Co20*Co40 + 3*Co60]

    sage: SMF(8,0).GetBasis()
    [Co20^4 - 6*Co20^2*Co40 + 9*Co40^2]

    sage: len(SMF(12,0).GetBasis())
    3
    """
    prec = 0
    chi = 0
    t_chi = 0
    
    def __init__(self, k, j, prec=3, taylor_prec=20):
        self.prec = prec
        print("Creating basis of covariants...")
        bsc = BSC(k+j//2,j)
        basis = bsc.GetBasis()
        print("Done!")
        if (len(basis) == 0):
            self.basis = []
            return
        if (SMF.prec < self.prec):
            print("Computing expansion of chi_6_m_2...")
            SMF.chi = get_chi6m2(4*self.prec)
            SMF.prec = self.prec
            print("Done!")
            
        q = SMF.chi.parent().base().gens()
        chi = sum([(SMF.chi.monomial_coefficient(m) + O(q[0]**prec))*m for m in SMF.chi.monomials()])
        t_chi = VectorFJexp(chi, taylor_prec)
        print("Substituting chi_6_m_2...")
        basis_expanded = [b.subs(bsc.DCov) for b in basis]
        exps = list(chi.dict().keys())
        t_chi_vals = list(t_chi.coeffs.values())
        R = t_chi_vals[0].parent()
        t_chi_comps = [t_chi.coeffs.get(exp, R(0)) for exp in exps]
        assert len(t_chi_comps) == 7
        gens = list(reduce(lambda x,y:x.union(y), [Set(b.variables()) for b in basis]))
        gens_exp = [g.subs(bsc.DCov) for g in gens]
        g_exps = [list(g_exp.dict().keys()) for g_exp in gens_exp]
        b_exps = list(basis_expanded[0].dict().keys())
        vals = list(basis_expanded[0].dict().values())
        U = vals[0].parent()
        a = U.gens()
        g_comps = [[g.dict().get(exp,U(0)) for exp in g_exps[i]] for i,g in enumerate(gens_exp)]
        b_comps = [[b.dict().get(exp,U(0)) for exp in b_exps] for b in basis_expanded]
        sub_dict = {a[i] : t_chi_comps[i] for i in range(7)}
        b_comps_expanded = [[R(b_c.subs(sub_dict)) for b_c in b_comps_s] for b_comps_s in b_comps]
        g_comps_expanded = [[R(g_c.subs(sub_dict)) for g_c in g_comps_s] for g_comps_s in g_comps]
        g_c_e = [VectorFJexp([g_exps[l], g_comps_expanded[l]]) for l in range(len(g_exps))]
        g_sub_dict = {gens[i] : g_c_e[i] for i in range(len(gens))}
        b_comps_exp = [b.subs(g_sub_dict) for b in basis]
        b_comps_exp2 = [VectorFJexp([b_exps, b_comps_s]) for b_comps_s in b_comps_expanded]
        # assert all([b_comps_exp[i].__eq__(b_comps_exp2[i]) for i in range(len(b_comps_exp))])
        assert b_comps_exp == b_comps_exp2
        print("Done!")
        print("Solving linear system...")
        qexps = reduce(lambda x,y: x.union(y), [reduce(lambda x,y: x.union(y), [Set(list(b_c.coeffs.keys())) for b_c in b_c_e]) for b_c_e in b_comps_expanded])
        ker = VectorSpace(QQ, len(basis))
        for qexp in qexps:
            for i in range(len(b_exps)):
                all_vals = []
                all_coeffs = []
                for j, b_c_e in enumerate(b_comps_expanded):
                    b_c = b_c_e[i]
                    mon = b_c.coeffs.get(qexp, FJexp(0))
                    v = mon.valuation()
                    coeffs = list(mon)
                    all_vals.append(v)
                    if (v >= 0):
                        all_coeffs.append([])
                    else:
                        all_coeffs.append(coeffs[:-v])
                min_val = min(all_vals)
                if (min_val < 0):
                    max_len = max([len(all_coeffs[j]) + all_vals[j] for j in range(len(all_vals)) if all_vals[j] < 0])
                    for j in range(len(all_vals)):
                        v = all_vals[j]
                        if (v >= 0):
                            v = max_len
                        all_coeffs[j] = [0 for l in range(v-min_val)] + all_coeffs[j]
                max_len = max([len(a) for a in all_coeffs])
                all_coeffs = [a + [0 for j in range(max_len-len(a))] for a in all_coeffs]
                mat_coeffs = Matrix(all_coeffs)
                ker_mat = mat_coeffs.kernel()
                ker = ker.intersection(ker_mat)
        print("Done!")
        # Take only highest valuations
        self.basis = [sum([b.denominator()*b[i]*basis[i] for i in range(len(basis))]) for b in ker.basis()]

    def GetBasis(self):
        return self.basis
