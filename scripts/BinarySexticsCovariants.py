"""
This file contains functions to compute a basis for the space of covariants of binary sextics C_{a,b} of degree a and order b.
"""

## imports
from functools import reduce
from sage.structure.sage_object import SageObject
from sage.all import Matrix, Partitions, ZZ, QQ, prod, Set, PolynomialRing, random_prime
from sage.combinat.q_analogues import q_multinomial
from sage.combinat.q_analogues import q_binomial
from sage.combinat.integer_vector_weighted import WeightedIntegerVectors
from Generators_Ring_Covariants_Sextic import GetRingGeneratorsCov
from sage.misc.prandom import randint
from sage.rings.invariants.invariant_theory import AlgebraicForm, transvectant
from sage.arith.misc import next_prime
from sage.rings.finite_rings.finite_field_constructor import GF

def ListOfWeights():
    return [(1, 6), (2, 0), (2, 4), (2, 8), (3, 2), (3, 6), (3, 8), (3, 12),
            (4, 0), (4, 4), (4, 6), (4, 10), (5, 2), (5, 4), (5, 8), (6, 0),
            (6, 6), (6, 6), (7, 2), (7, 4), (8, 2), (9, 4), (10, 0), (10, 2),
            (12, 2), (15, 0)]

# Only leading coefficients by default, otherwise all coefficients
def EvaluateBasicCovariants(sextic, leading_coefficient = True):
    LW = ListOfWeights()
    R = sextic.base_ring()
    C = {}
    f = AlgebraicForm(2, 6, sextic)
    cofactors = [1, 60, 75, 90, 2250, 2250, 450, 540, 11250, 67500, 13500,
                 13500, 168750, 67500, 405000, 10125000, 2025000, 2700000, 151875000,
                 60750000, 15187500, 9112500000, 227812500000, 13668750000,
                 8201250000000, 384433593750];

    C[(1,6)] = f
    C[(2,0)] = transvectant(f, f, 6)
    C[(2,4)] = transvectant(f, f, 4)
    C[(2,8)] = transvectant(f, f, 2)
    C[(3,2)] = transvectant(f, C[(2,4)], 4)
    C[(3,6)] = transvectant(f, C[(2,4)], 2)
    C[(3,8)] = transvectant(f, C[(2,4)], 1)
    C[(3,12)] = transvectant(f, C[(2,8)], 1)
    C[(4,0)] = transvectant(C[(2,4)], C[(2,4)], 4)
    C[(4,4)] = transvectant(f, C[(3,2)], 2)
    C[(4,6)] = transvectant(f, C[(3,2)], 1)
    C[(4,10)] = transvectant(C[(2,8)], C[(2,4)], 1)
    C[(5,2)] = transvectant(C[(2,4)], C[(3,2)], 2)
    C[(5,4)] = transvectant(C[(2,4)], C[(3,2)], 1)
    C[(5,8)] = transvectant(C[(2,8)], C[(3,2)], 1)
    C[(6,0)] = transvectant(C[(3,2)], C[(3,2)], 2)
    C[(6,6)] = transvectant(C[(3,6)], C[(3,2)], 1)
    C[(6,6,2)] = transvectant(C[(3,8)], C[(3,2)], 2)
    C32_2 = transvectant(C[(3,2)],C[(3,2)],0)
    C[(7,2)] = transvectant(f, C32_2, 4)
    C[(7,4)] = transvectant(f, C32_2, 3)
    C[(8,2)] = transvectant(C[(2,4)], C32_2, 3)
    C[(9,4)] = transvectant(C[(3,8)], C32_2, 4)
    C32_3 = transvectant(C[(3,2)],C32_2,0)
    C[(10,0)] = transvectant(f, C32_3, 6)
    C[(10,2)] = transvectant(f, C32_3, 5)
    C[(12,2)] = transvectant(C[(3,8)], C32_3, 6)
    C32_4 = transvectant(C32_2,C32_2,0)
    C[(15,0)] = transvectant(C[(3,8)], C32_4, 8)

    #could be more efficient if we only want leading coefficient
    if leading_coefficient:
        for k in C.keys():
            C[k] = R(C[k].polynomial().coefficient([k[1], 0]))
    else:
        Rx = PolynomialRing(R, "x")
        for k in C.keys():
            pol = C[k].polynomial()
            coeffs = [pol.coefficient([i, k[1] - i]) for i in range(k[1] + 1)]
            C[k] = Rx(coeffs)

    res = [C[wt] for wt in LW]
    res[17] = C[(6,6,2)]
    for k in range(26):
        res[k] *= cofactors[k]
    return res

def EvaluateMonomialInCovariants(wt, basic):
    R = basic[0].parent()
    res = R(1)
    for i in range(26):
        res *= basic[i] ** wt[i]
    return res

#this is just for testing.
def EvaluatePolynomialInCovariants(pol, basic):
    res = 0
    w = pol.exponents()
    c = pol.coefficients()
    for i in range(len(c)):
        res += c[i] * EvaluateMonomialInCovariants(w[i], basic)
    return res

def RandomSextic(R, bound, zeroa5a6 = False):
    x = R.gens()[0]
    y = R.gens()[1]
    f = R(0)
    start = 0
    if zeroa5a6:
        start = 2
    for i in range(start, 7):
        f += randint(1, bound) * x ** i * y ** (6-i)
    return f

def RandomSL2(bound):
    g = 2
    while not g == 1:
        a = randint(-bound, bound)
        b = randint(-bound, bound)
        g, u, v = ZZ(a).xgcd(b)
    return Matrix([[a, b],[-v, u]])

def QuarticTransform(f, mat):
    R = f.parent()
    a = mat[0,0]
    b = mat[0,1]
    c = mat[1,0]
    d = mat[1,1]
    x = R.gen(0)
    y = R.gen(1)
    q = f // x**2
    q = q.subs({x: a*x + c*y, y: b*x + d*y})
    return x**2 * q

# we use a class in order to perform initialization only once

class BinarySexticsCovariants(SageObject):

    r"""
     Constructs spaces of covariants of binary sextics

     EXAMPLES:

     This example is Example 2.1 in the overleaf. :

        sage: bsc = BinarySexticsCovariants(6,0)
        sage: bsc.GetBasisAndRelationsCov()
        ([Co60, Co20*Co40, Co20^3], [])

    """

    LW, LCo, LCov, DCov = GetRingGeneratorsCov()

    # Verifying the expression for C_{2,0}
    assert LCo[1].parent().variable_names()[1] == 'Co20'
    a = LCov[1].base_ring().gens()
    assert LCov[1] == -3*a[3]**2 + 8*a[2]*a[4] - 20*a[1]*a[5] + 120*a[0]*a[6]

    def __init__(self, a, b):
        self.a = a
        self.b = b
        self.weight = (a,b)

    def __str__(self):
        return "Space of covariants of binary sextics of degree " + str(self.a) + " and order " + str(self.b)

    def __repr__(self):
        return str(self)

    def GetCov(cov_name):
        idx = BinarySexticsCovariants.LCo[0].parent().variable_names().index(cov_name)
        return BinarySexticsCovariants.LCov[idx]

    def MakeCov(L):
        r"""
        Returns a list with two elements, the first is the polynomial in the covariants defined by the exponents in L, and the second is
        its evaluation at the covariants (polynomial in the a_i, x and y)

        INPUT:

        - ``L`` - a list of exponents for the different covariants.

        OUTPUT: [Cov, polynomial in a_i and x,y]

        EXAMPLES:

        This example is Example 2.3 in the overleaf. ::

           sage: bsc = BSC(6,0)
           sage: W = BSC.GetGeneratorsCov(BSC.LW, bsc.weight)
           sage: covs = [BSC.MakeCov(wt) for wt in W]
           sage: covs[1]
           [Co20*Co40,
            -9*a3^6 + 72*a2*a3^4*a4...

        """
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

    def MakeMonomial(self, wt):
        res = 1
        for i in range(26):
            res *= BinarySexticsCovariants.LCo[i] ** wt[i]
        return res

    def Dimension2(self):
        # using the Cayley-Sylvester formula
        a = self.a
        b = self.b
        n = 3 * a - b // 2
        def p(k,n):
            return Partitions(n,max_length=k, max_part=6).cardinality()
        return p(a,n) - p(a,n-1)

    def Dimension(self):
        a = self.a
        b = self.b
        if ((b % 2) == 1):
            return 0
        else:
            R = PolynomialRing(ZZ, ['p'])
            p = R.gen()
            n = 3*a-b//2
            if (n < 0):
                return 0
            f = (1-p)*q_binomial(6+a,a,p)
            d = f.list()[n]
            return d

    # This is slowish (Gauss pivot on a possibly huge matrix over QQ...)
    def _ComputeBasisAndRelationsCov(self):
        r"""
        Computes the basis and relations for both of the following functions
        """
        LW = ListOfWeights()
        W = BinarySexticsCovariants.GetGeneratorsCov(LW, self.weight)
        dim = self.Dimension()
        if (dim == 0):
            return [], [], []
        eval_data = []
        R = PolynomialRing(QQ, ["x", "y"])

        for i in range(dim):
            f = RandomSextic(R, 10)
            basic = EvaluateBasicCovariants(f)
            new_eval = [EvaluateMonomialInCovariants(wt, basic) for wt in W]
            eval_data.append(new_eval)

        eval_mat = Matrix(eval_data).transpose()
        print("Computing rank (size {} * {})...".format(len(W), dim))
        rk = eval_mat.rank()
        print("done")
        while (rk < dim):
            print("One more evaluation point (current rank {})".format(rk))
            f = RandomSextic(R, 100)
            basic = EvaluateBasicCovariants(f)
            new_eval = [EvaluateMonomialInCovariants(wt, basic) for wt in W]
            eval_data.append(new_eval)
            eval_mat = Matrix(eval_data).transpose()
            rk = eval_mat.rank()

        rels = eval_mat.kernel().basis()
        rels = [rel.denominator() * rel for rel in rels]
        C_basis = [self.MakeMonomial(W[i]) for i in eval_mat.pivot_rows()]
        covs = [self.MakeMonomial(wt) for wt in W]
        assert len(C_basis) == dim
        return C_basis, rels, covs

    # Use a finite field instead
    def _ComputeBasisCov(self):
        LW = ListOfWeights()
        W = BinarySexticsCovariants.GetGeneratorsCov(LW, self.weight)
        print("ComputeBasisCov: starting dimension {}".format(len(W)))
        dim = self.Dimension()
        print("ComputeBasisCov: target dimension {}".format(dim))
        if (dim == 0):
            return []
        eval_data = []
        R = PolynomialRing(QQ, ["x", "y"])
        for i in range(dim):
            f = RandomSextic(R, 10)
            basic = EvaluateBasicCovariants(f)
            new_eval = [EvaluateMonomialInCovariants(wt, basic) for wt in W]
            eval_data.append(new_eval)

        exp = 10
        bound = 10
        p = next_prime(2**exp)
        reduced_mat = Matrix(eval_data).change_ring(GF(p))
        basis = reduced_mat.pivot_rows()
        rk = len(basis)
        print("ComputeBasisCov: dimension {}".format(rk))
        while rk < dim:
            exp += 10
            bound += 10
            f = RandomSextic(R, bound)
            basic = EvaluateBasicCovariants(f)
            new_eval = [EvaluateMonomialInCovariants(wt, basic) for wt in W]
            eval_data.append(new_eval)
            p = next_prime(2**exp)
            reduced_mat = Matrix(eval_data).change_ring(GF(p))
            basis = reduced_mat.pivot_rows()
            print("ComputeBasisCov: dimension {}".format(rk))

        return [self.MakeMonomial(W[i]) for i in basis]

    def _ComputeBasisAndRelationsCovOld(self):
        print("    Getting generators of covariants...")
        W = BinarySexticsCovariants.GetGeneratorsCov(BinarySexticsCovariants.LW, self.weight)
        print("    Half done! MakeCov on {} vectors of exponents...".format(len(W)))
        covs = [BinarySexticsCovariants.MakeCov(wt) for wt in W]
        print("    Done!")
        poly_ring_bivariate = BinarySexticsCovariants.LCov[0].parent()
        coeff_ring = poly_ring_bivariate.base_ring()
        # Here we are using the theorem by Roberts, stating it is enough to consider the coefficient of x^b
        lcs = [coeff_ring(c[1].coefficient([0,self.b])) for c in covs]
        exps = reduce(lambda x,y: x.union(y), [Set(lc.exponents()) for lc in lcs], Set([]))
        # We try to make this more efficient as exps is very long
        dim = self.Dimension()
        if (dim == 0):
            return [], [], []
        rk = 0
        maybe_enough_coeffs = 0
        coeff_data = []
        while (rk != dim):
            more_coeffs = len(lcs)
            coeff_data += [[QQ(lc.coefficient(e)) for lc in lcs] for e in exps[maybe_enough_coeffs:maybe_enough_coeffs+more_coeffs]]
            maybe_enough_coeffs += more_coeffs
            coeffs_mat = Matrix(coeff_data).transpose()
            rk = coeffs_mat.rank()
        rels = coeffs_mat.kernel().basis()
        rels = [rel.denominator() * rel for rel in rels]
        C_basis = [covs[i][0] for i in coeffs_mat.pivot_rows()]
        assert len(C_basis) == dim
        return C_basis, rels, covs

    def GetBasisAndRelationsCov(self):
        r"""
        Return the generators and relations for the covariants in the space of covariants of binary sextics

        OUTPUT: a list of polynomials in the covariants that generate the space, and a list of polynomial relations that they satisfy

        EXAMPLES:

        This example is Example 2.1 in the overleaf. ::

            sage: bsc = BinarySexticsCovariants(6,0)
            sage: bsc.GetBasisAndRelationsCov()
            ([Co60, Co20*Co40, Co20^3], [])

        This example is the Example commeneted out after Example 2.4 in the overleaf. ::

            sage: bsc = BinarySexticsCovariants(6,8)
            sage: bsc.GetBasisAndRelationsCov()
            ([Co32*Co36, Co28*Co40, Co24*Co44, Co20*Co24^2, Co20^2*Co28, Co16*Co20*Co32],
             [5*Co20*Co24^2 + 4*Co32*Co36 - 10*Co28*Co40 + Co24*Co44 - 60*Co16*Co52])

        This example is Igusa's relation for the Siegel three-fold. ::

            sage: bsc = BinarySexticsCovariants(30,0)
            sage: basis, rels = bsc.GetBasisAndRelationsCov()
            sage: rels
            [1953125*Co20^9*Co40^3 - 15000000*Co20^7*Co40^4 - 1171875*Co20^8*Co40^2*Co60 + 43200000*Co20^5*Co40^5 + 4125000*Co20^6*Co40^3*Co60 + 234375*Co20^7*Co40*Co60^2 - 55296000*Co20^3*Co40^6 + 2160000*Co20^4*Co40^4*Co60 + 900000*Co20^5*Co40^2*Co60^2 - 15625*Co20^6*Co60^3 + 1687500*Co20^6*Co40^2*Co100 + 26542080*Co20*Co40^7 - 20736000*Co20^2*Co40^5*Co60 - 6048000*Co20^3*Co40^3*Co60^2 - 375000*Co20^4*Co40*Co60^3 - 9720000*Co20^4*Co40^3*Co100 - 675000*Co20^5*Co40*Co60*Co100 + 18579456*Co40^6*Co60 + 6635520*Co20*Co40^4*Co60^2 + 806400*Co20^2*Co40^2*Co60^3 + 30000*Co20^3*Co60^4 + 18662400*Co20^2*Co40^4*Co100 + 2592000*Co20^3*Co40^2*Co60*Co100 + 67500*Co20^4*Co60^2*Co100 - 55296*Co40^3*Co60^3 - 11520*Co20*Co40*Co60^4 - 11943936*Co40^5*Co100 - 2488320*Co20*Co40^3*Co60*Co100 + 486000*Co20^3*Co40*Co100^2 + 1152*Co60^5 - 248832*Co40^2*Co60^2*Co100 - 25920*Co20*Co60^3*Co100 - 933120*Co20*Co40^2*Co100^2 - 97200*Co20^2*Co60*Co100^2 + 93312*Co40*Co60*Co100^2 + 46656*Co100^3 + 14929920000000000*Co150^2]

        """
        C_basis, rels, covs = self._ComputeBasisAndRelationsCov()
        rels_symb = [sum([rel[i]*covs[i] for i in range(len(covs))]) for rel in rels]
        return C_basis, rels_symb

    def GetBasis(self):
        r"""
        Return the generators for the covariants in the space of covariants of binary sextics

        OUTPUT: a list of polynomials in the covariants that generate the space

        EXAMPLES:

        This example is Example 2.1 in the overleaf. :

            sage: bsc = BinarySexticsCovariants(6,0)
            sage: bsc.GetBasis()
            [Co60, Co20*Co40, Co20^3]

        This example is the Example commeneted out after Example 2.4 in the overleaf. ::

            sage: bsc = BinarySexticsCovariants(6,8)
            sage: bsc.GetBasis()
            [Co32*Co36, Co28*Co40, Co24*Co44, Co20*Co24^2, Co20^2*Co28, Co16*Co20*Co32]

        """
        return self._ComputeBasisCov()

    def GetBasisWithConditions(self, bound = 6):
        r"""
        Return a set of linearly independent elements in the space of covariants that is
        sufficient to generate the space of holomorphic Siegel modular forms of the
        corresponding weight

        OUTPUT: a list of polynomial in the basic covariants

        EXAMPLES: todo
        """

        B = self.GetBasis()
        W = [b.exponents()[0] for b in B]
        R = PolynomialRing(QQ, ["x", "y"])
        x = R.gen(0)
        y = R.gen(1)
        eval_data = []
        nonincrease = 0
        dim = len(B)
        n = self.a - (self.b)/2
        cusp = (n % 2 == 1)

        #stop if done or unlucky four times
        while nonincrease < bound:
            f = RandomSextic(R, 10, zeroa5a6 = True)
            mat = RandomSL2(10)
            fp = QuarticTransform(f, mat)
            basic = EvaluateBasicCovariants(f, leading_coefficient = False)
            basicp = EvaluateBasicCovariants(fp, leading_coefficient = False)
            a4 = f.coefficient(x**2 * y**4)
            a4p = fp.coefficient(x**2 * y**4)

            #evaluate basis elements
            new_eval = [EvaluateMonomialInCovariants(wt, basic).coefficients(sparse = False)
                        for wt in W]
            new_evalp = [EvaluateMonomialInCovariants(wt, basicp).coefficients(sparse = False)
                         for wt in W]
            #padding in case the evaluation has smaller degree
            for v in new_eval:
                v += [0 for i in range(self.b + 1 - len(v))]
            for v in new_evalp:
                v += [0 for i in range(self.b + 1 - len(v))]
            #these are polynomials in QQ[x] of degree self.b, all coefficients
            #except leading term must vanish
            for i in range(self.b):
                eval_data.append([v[i] for v in new_eval])
                eval_data.append([v[i] for v in new_evalp])
            #additionally, leading coefficient divided by a4^n must be an invariant of quadrics
            #if cusp, must be zero
            if cusp:
                eval_data.append([v[self.b] for v in new_eval])
                eval_data.append([v[self.b] for v in new_evalp])
            else:
                line = [a4p ** (n//2) * new_eval[i][self.b]
                        - a4 ** (n//2) * new_evalp[i][self.b] #no det since SL
                        for i in range(len(B))]
                eval_data.append(line)

            #do linear algebra
            next_dim = dim + 1
            while next_dim > dim:
                p = random_prime(10000)
                mat = Matrix(GF(p), eval_data)
                next_dim = len(B) - mat.rank()

            if next_dim < dim:
                nonincrease = 0
            else:
                nonincrease += 1
            dim = next_dim
            print("GetBasisWithConditions: dimension {}".format(dim))
            eval_data = [eval_data[i] for i in mat.pivot_rows()]

        LCs = mat.right_kernel().basis()
        res = []
        for LC in LCs:
            cov = 0
            for i in range(len(LC)):
                cov += LC[i] * B[i]
            res.append(cov / cov.content())
        return res
