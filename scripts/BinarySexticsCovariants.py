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
        self.weight = [a,b]

    def MakeCov(L):
        S = [[BinarySexticsCovariants.LCo[k]**L[k],BinarySexticsCovariants.LCov[k]**L[k]] for k in range(len(L))]
        S1 = prod(S[k][0] for k in range(len(S)))
        S2 = prod(S[k][1] for k in range(len(S)))
        return [S1,S2]
        
    def GetGeneratorsCov(weight_list, wt):
        has_zero = [ any([x[i] == 0 for x in weight_list]) for i in range(2)]
        assert not all(has_zero)
        if (has_zero[1]) or ((not has_zero[0]) and (wt[0] < wt[1])):
            return BinarySexticsCovariants.GetGeneratorsCov([[x[1],x[0]] for x in weight_list], [wt[1], wt[0]])
        exps = list(WeightedIntegerVectors(wt[1],[x[1] for x in weight_list]))
        return [exp for exp in exps if sum([exp[i]*weight_list[i][0] for i in range(len(exp))]) == wt[0]]
        
    def GetBasisAndRelationsCov(self):
        W = BinarySexticsCovariants.GetGeneratorsCov(BinarySexticsCovariants.LW, self.weight)
        covs = [BinarySexticsCovariants.MakeCov(wt) for wt in W]
        poly_ring_bivariate = BinarySexticsCovariants.LCov[0].parent()
        coeff_ring = poly_ring_bivariate.base_ring()
        # Here we are using the theorem by Roberts, stating it is enough to consider the coefficient of x^b
        lcs = [coeff_ring(c[1].coefficient([0,self.b])) for c in covs]
        exps = reduce(lambda x,y: x.union(y), [Set(lc.exponents()) for lc in lcs])
        # !! TODO - It might be faster to work over QQ here and then normalize
        coeffs_mat = Matrix([[ZZ(lc.coefficient(e)) for e in exps] for lc in lcs])
        rels = coeffs_mat.kernel().basis()
        rels_symb = [sum([rel[i]*covs[i][0] for i in range(len(covs))]) for rel in rels]
        C_basis = [covs[i][0] for i in coeffs_mat.pivot_rows()]
        return C_basis, rels_symb
