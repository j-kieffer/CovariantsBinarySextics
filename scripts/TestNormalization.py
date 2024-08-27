"""
This file contains a function testing our normalization of the generators of the covariants.
"""

## imports
from functools import reduce
from sage.all import QQ, PolynomialRing
from sage.rings.invariants.invariant_theory import AlgebraicForm, transvectant

def testNormalization():
    A = PolynomialRing(QQ, 'a', 7)
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

    LW = [k for k in C.keys()]
    values = [C[k] for k in LW]
    LCov = [c.form().numerator() for c in reduce(lambda x,y : x + y, values)]

    # Manually inputing the cofficients Fabien calculated
    
    coeffs = {}
    coeffs[(1,6)] = 1
    coeffs[(2,0)] = 60
    coeffs[(2,4)] = 75
    coeffs[(2,8)] = 90
    coeffs[(3,2)] = 30*coeffs[(2,4)]
    coeffs[(3,6)] = 30*coeffs[(2,4)]
    coeffs[(3,8)] = 6*coeffs[(2,4)]
    coeffs[(3,12)] = 6*coeffs[(2,8)]
    coeffs[(4,0)] = 2*coeffs[(2,4)]**2
    coeffs[(4,4)] = 30*coeffs[(3,2)]
    coeffs[(4,6)] = 6*coeffs[(3,2)]
    coeffs[(4,10)] = 2*coeffs[(2,8)]*coeffs[(2,4)]
    coeffs[(5,2)] = coeffs[(2,4)]*coeffs[(3,2)]
    coeffs[(5,4)] = 2/5*coeffs[(2,4)]*coeffs[(3,2)]
    coeffs[(5,8)] = 2*coeffs[(2,8)]*coeffs[(3,2)]
    coeffs[(6,0)] = 2*coeffs[(3,2)]**2
    for k in coeffs.keys():
        coeffs[k] = [coeffs[k]] 
    coeffs[(6,6)] = [2*coeffs[(3,6)][0]*coeffs[(3,2)][0]/5, 8*coeffs[(3,8)][0]*coeffs[(3,2)][0] / 3]
    coeffs[(7,2)] = [30*coeffs[(3,2)][0]**2]
    coeffs[(7,4)] = [12*coeffs[(3,2)][0]**2]
    coeffs[(8,2)] = [coeffs[(2,4)][0]*coeffs[(3,2)][0]**2/25]
    coeffs[(9,4)] = [4*coeffs[(3,8)][0]*coeffs[(3,2)][0]**2]
    coeffs[(10,0)] = [20*coeffs[(3,2)][0]**3]
    coeffs[(10,2)] = [6*coeffs[(3,2)][0]**3/5]
    coeffs[(12,2)] = [8*coeffs[(3,8)][0]*coeffs[(3,2)][0]**3/5]
    coeffs[(15,0)] = [coeffs[(3,8)][0]*coeffs[(3,2)][0]**4/30000]
    all_coeffs = reduce(lambda x,y :x+y, [coeffs[k] for k in LW])

    denoms = [c.form().denominator() for c in reduce(lambda x,y : x + y, values)]
    return (all_coeffs == denoms)
