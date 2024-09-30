"""
This file contains a function returning a dictionary with the keys being the weights and the items the list of generators in that weight.
"""

## imports
from sage.all import QQ, PolynomialRing, GF, TermOrder
from sage.rings.invariants.invariant_theory import AlgebraicForm, transvectant

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
        base_ring = QQ
        LCov = [c.form().numerator() for c in values]
    else:
        base_ring = GF(p)
        LCov = [c.form() for c in values]
    Co = PolynomialRing(base_ring, cov_names, order = TermOrder('wdegrevlex', tuple([w[0] for w in LW])))
    LCo = Co.gens()

    # Sanity check
    assert (len(LW) == len(LCo)) and (len(LCo) == len(LCov))

    DCov = {LCo[i] : LCov[i] for i in range(len(LCo))}

    return LW, LCo, LCov, DCov

def RingOfCovariants(new_ordering = False, p = 0):
    LW, LCo, LCov, DCov = GetRingGeneratorsCov(new_ordering = new_ordering, p = p)
    return LCo[0].parent()

