"""
This file contains a function returning a dictionary with the keys being the weights and the items the list of generators in that weight.
"""

## imports
from functools import reduce
from sage.all import QQ, PolynomialRing, GF
from sage.rings.invariants.invariant_theory import AlgebraicForm, transvectant

def ListOfWeights(new_ordering = False):
    if new_ordering:
        return [(1, 6), (2, 8), (3, 12), (3, 8), (4, 10), (2, 4), (3, 6), (5, 8),
                (4, 6), (4, 4), (6, 6), (6, 6), (5, 4), (3, 2), (7, 4), (9, 4),
                (5, 2), (7, 2), (8, 2), (10, 2), (12, 2), (2, 0), (4, 0),
                (6, 0), (10, 0), (15, 0)]
    else:
        return [(1, 6), (2, 0), (2, 4), (2, 8), (3, 2), (3, 6), (3, 8), (3, 12),
                (4, 0), (4, 4), (4, 6), (4, 10), (5, 2), (5, 4), (5, 8), (6, 0),
                (6, 6), (6, 6), (7, 2), (7, 4), (8, 2), (9, 4), (10, 0), (10, 2),
                (12, 2), (15, 0)]

# packaging Fabien's initialization function neatly to be able to use it in what follows
def GetRingGeneratorsCov(new_ordering = False, p = 0):
    """
    Compute generators for the entire ring of covariants of binary sextics
    """
    if p == 0:
        A = PolynomialRing(QQ, 'a', 7)
    else:
        A = PolynomialRing(GF(p), 'a', 7)
    a = A.gens()
    R = PolynomialRing(A, ['x', 'y'])
    x, y = R.gens()
    f = AlgebraicForm(2, 6, sum([a[i]*x**(6-i)*y**i for i in range(7)]))
    C = {}

    C[(1,6)] = [f]

    C[(2,0)] = [transvectant(f, f, 6)]
    C[(2,4)] = [transvectant(f, f, 4)]
    C[(2,8)] = [transvectant(f, f, 2)]

    C[(3,2)] = [transvectant(f, C[(2,4)][0], 4)]
    C[(3,6)] = [transvectant(f, C[(2,4)][0], 2)]
    C[(3,8)] = [transvectant(f, C[(2,4)][0], 1)]
    C[(3,12)] = [transvectant(f, C[(2,8)][0], 1)]

    C[(4,0)] = [transvectant(C[(2,4)][0], C[(2,4)][0], 4)]
    C[(4,4)] = [transvectant(f, C[(3,2)][0], 2)]
    C[(4,6)] = [transvectant(f, C[(3,2)][0], 1)]
    C[(4,10)] = [transvectant(C[(2,8)][0], C[(2,4)][0], 1)]

    C[(5,2)] = [transvectant(C[(2,4)][0], C[(3,2)][0], 2)]
    C[(5,4)] = [transvectant(C[(2,4)][0], C[(3,2)][0], 1)]
    C[(5,8)] = [transvectant(C[(2,8)][0], C[(3,2)][0], 1)]

    C[(6,0)] = [transvectant(C[(3,2)][0], C[(3,2)][0], 2)]
    C[(6,6)] = [transvectant(C[(3,6)][0], C[(3,2)][0], 1), transvectant(C[(3,8)][0], C[(3,2)][0], 2)]

    C32_2 = transvectant(C[(3,2)][0],C[(3,2)][0],0)

    C[(7,2)] = [transvectant(f, C32_2, 4)]
    C[(7,4)] = [transvectant(f, C32_2, 3)]

    C[(8,2)] = [transvectant(C[(2,4)][0], C32_2, 3)]

    C[(9,4)] = [transvectant(C[(3,8)][0], C32_2, 4)]

    C32_3 = transvectant(C[(3,2)][0],C32_2,0)

    C[(10,0)] = [transvectant(f, C32_3, 6)]
    C[(10,2)] = [transvectant(f, C32_3, 5)]

    C[(12,2)] = [transvectant(C[(3,8)][0], C32_3, 6)]

    C32_4 = transvectant(C32_2,C32_2,0)

    C[(15,0)] = [transvectant(C[(3,8)][0], C32_4, 8)]

    LW = ListOfWeights(new_ordering = new_ordering)
    values = []
    cov_names = []
    i = 1
    for k in LW:
        name = "Co{}{}".format(k[0], k[1])
        if k == (6, 6):
            values.append(C[k][i - 1])
            name += str(i)
            i += 1
        else:
            values.append(C[k][0])
        cov_names.append(name)
    if p == 0:
        LCov = [c.form().numerator() for c in values]
        Co = PolynomialRing(QQ, cov_names)
        LCo = Co.gens()
    else:
        LCov = [c.form() for c in values]
        Co = PolynomialRing(GF(p), cov_names)
        LCo = Co.gens()

    # Sanity check
    assert (len(LW) == len(LCo)) and (len(LCo) == len(LCov))

    DCov = {LCo[i] : LCov[i] for i in range(len(LCo))}

    return LW, LCo, LCov, DCov

def RingOfCovariants(new_ordering = False, p = 0):
    LW, LCo, LCov, DCov = GetRingGeneratorsCov(new_ordering = new_ordering, p = p)
    return LCo[0].parent()

def LeadingMonomial(cov):
    assert cov != 0
    mon = x.monomials()
    lm = mon[0]
    ld = lm.degrees()
    for i in range(1, len(mon)):
        newd = mon[i].degrees()
        for j in range(26):
            if newd[j] > ld[j]:
                break
            elif newd[j] < ld[j]: #found bigger monomial
                lm = mon[i]
                ld = newd
                break
        assert j < 26
    return lm
