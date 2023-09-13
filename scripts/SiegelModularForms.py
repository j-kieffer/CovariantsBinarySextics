from functools import reduce
from sage.matrix.constructor import Matrix
from sage.modules.free_module import VectorSpace
from sage.rings.infinity import infinity
from sage.rings.rational_field import QQ
from sage.sets.set import Set

from BinarySexticsCovariants import BinarySexticsCovariants as BSC
from ThetaFourier import get_chi6m2, get_taylor_exp

def get_smf_cov_basis(k, j, prec=10):
    print("Computing expansion of chi_6_m_2...")
    chi = get_chi6m2(prec)
    print("Done!")
    print("Producing Taylor expansion around s = 0...")
    t_chi = get_taylor_exp(chi)
    print("Done!")
    print("Creating basis of covariants...")
    bsc = BSC(k,j)
    basis = bsc.GetBasis()
    print("Done!")
    print("Substituting chi_6_m_2...")
    basis_expanded = [b.subs(bsc.DCov) for b in basis]
    exps = list(t_chi.dict().keys())
    t_chi_comps = [t_chi.dict()[exp] for exp in exps]
    t_chi_vals = list(t_chi.dict().values())
    R = t_chi_vals[0].parent()
    vals = list(basis_expanded[0].dict().values())
    U = vals[0].parent()
    a = U.gens()
    b_comps = [[b.dict().get(exp,U(0)) for exp in exps] for b in basis_expanded]
    sub_dict = {a[i] : t_chi_comps[i] for i in range(7)}
    b_comps_expanded = [[R(b_c.subs(sub_dict)) for b_c in b_comps_s] for b_comps_s in b_comps]
    print("Done!")
    print("Solving linear system...")
    qexps = reduce(lambda x,y: x.union(y), [reduce(lambda x,y: x.union(y), [Set(list(b_c.dict().keys())) for b_c in b_c_e]) for b_c_e in b_comps_expanded])
    ker = VectorSpace(QQ, len(basis))
    for qexp in qexps:
        for i in range(7):
            all_vals = []
            all_coeffs = []
            for j, b_c_e in enumerate(b_comps_expanded):
                b_c = b_c_e[i]
                mon = b_c.dict().get(qexp, R.base()(0))
                v = mon.valuation()
                coeffs = list(mon)
                all_vals.append(v)
                if (v > 0):
                    all_coeffs.append([])
                else:
                    all_coeffs.append(coeffs[:-v])
            min_val = min(all_vals)
            if (min_val <= 0):
                max_len = max([len(all_coeffs[j]) + all_vals[j] for j in range(len(all_vals)) if all_vals[j] <= 0])
                for j in range(len(all_vals)):
                    v = all_vals[j]
                    if (v == infinity):
                        v = max_len
                    all_coeffs[j] = [0 for l in range(v-min_val)] + all_coeffs[j]
                mat_coeffs = Matrix(all_coeffs)
                ker_mat = mat_coeffs.kernel()
                ker = ker.intersection(ker_mat)
    print("Done!")
    return [sum([b.denominator()*b[i]*basis[i] for i in range(len(basis))]) for b in ker.basis()]
