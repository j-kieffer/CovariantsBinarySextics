"""
This file contains functions to compute a basis for the space of covariants of binary sextics C_{a,b} of degree a and order b.
"""

## imports
from functools import reduce
from sage.all import Matrix, ZZ, prod, Set
from sage.combinat.integer_vector_weighted import WeightedIntegerVectors
from Generators_Ring_Covariants_Sextic import GetRingGeneratorsCov

# we use a class in order to perform initialization only once

class BinarySexticsCovariants:

    LW, LCo, LCov = GetRingGeneratorsCov()
    
    def __init__(self, a, b):
        self.a = a
        self.b = b
        self.weight = (a,b)

    def MakeCov(L):
        S = [[BinarySexticsCovariants.LCo[k]**L[k],BinarySexticsCovariants.LCov[k]**L[k]] for k in range(len(L))]
        S1 = prod(S[k][0] for k in range(len(S)))
        S2 = prod(S[k][1] for k in range(len(S)))
        return [S1,S2]

    # Somehow this is slow if one runs it line by line, but quite fast in practice ?!
    def GetGeneratorsCovSlow(weight_list, wt):
        has_zero = [ any([x[i] == 0 for x in weight_list]) for i in range(2)]
        assert not all(has_zero)
        if (has_zero[1]) or ((not has_zero[0]) and (wt[0] < wt[1])):
            return BinarySexticsCovariants.GetGeneratorsCov([[x[1],x[0]] for x in weight_list], [wt[1], wt[0]])
        exps = list(WeightedIntegerVectors(wt[1],[x[1] for x in weight_list]))
        return [exp for exp in exps if sum([exp[i]*weight_list[i][0] for i in range(len(exp))]) == wt[0]]

    def GetGeneratorsCov(weight_list, wt):
        if (len(weight_list) == 0):
            if (wt == (0,0)):
                return [[]]
            else:
                return []
        wt0 = weight_list[0]
        assert not ((wt0[0] == 0) and (wt0[1] == 0))
        max_w0 = min([wt[i] // wt0[i] for i in range(2) if wt0[i] != 0])
        all_ws = []
        for w0 in range(max_w0+1):
            ws = BinarySexticsCovariants.GetGeneratorsCov(weight_list[1:], (wt[0]-w0*wt0[0], wt[1]-w0*wt0[1]))
            all_ws += [[w0] + w for w in ws]
        return all_ws
        
    def GetBasisAndRelationsCov(self):
        W = BinarySexticsCovariants.GetGeneratorsCov(BinarySexticsCovariants.LW, self.weight)
        covs = [BinarySexticsCovariants.MakeCov(wt) for wt in W]
        poly_ring_bivariate = BinarySexticsCovariants.LCov[0].parent()
        coeff_ring = poly_ring_bivariate.base_ring()
        # Here we are using the theorem by Roberts, stating it is enough to consider the coefficient of x^b
        # lcs = [coeff_ring(c[1].coefficient([0,self.b])) for c in covs]
        lcs = [[coeff_ring(c[1].coefficient([i,j])) for c in covs] for i in range(7) for j in range(7)]
        # exps = reduce(lambda x,y: x.union(y), [Set(lc.exponents()) for lc in lcs])
        exps = [reduce(lambda x,y: x.union(y), [Set(lc.exponents()) for lc in lcss], Set([])) for lcss in lcs]
        # !! TODO - It might be faster to work over QQ here and then normalize
        # coeffs_mat = Matrix([[ZZ(lc.coefficient(e)) for e in exps] for lc in lcs])
        coeffs_mats = [Matrix([[ZZ(lc.coefficient(e)) for e in exps[j]] for lc in lcs[j]]) for j in range(len(exps))]
        coeffs_mat = reduce(lambda x,y : x.augment(y), coeffs_mats)
        kers = [coeffs_mat.kernel() for coeffs_mat in coeffs_mats]
        ker = reduce(lambda x,y: x.intersection(y), kers)
        assert ker == coeffs_mat.kernel()
        # rels = coeffs_mat.kernel().basis()
        rels = ker.basis()
        rels_symb = [sum([rel[i]*covs[i][0] for i in range(len(covs))]) for rel in rels]
        C_basis = [covs[i][0] for i in coeffs_mat.pivot_rows()]
        return C_basis, rels_symb
