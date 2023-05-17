"""
This file contains a function returning a dictionary with the keys being the weights and the items the list of generators in that weight.
"""

## imports
from functools import reduce
from sage.all import QQ, PolynomialRing
from sage.rings.invariants.invariant_theory import AlgebraicForm, transvectant

# packaging Fabien's initialization function neatly to be able to use it in what follows
def GetRingGeneratorsCov():
    """
    Compute generators for the entire ring of covariants of binary sextics
    """
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

    LW = C.keys()
    key_list = [k for k in C.keys()]
    values = [C[k] for k in key_list]
    LCov = [c.form().numerator() for c in reduce(lambda x,y : x + y, values)]
    cov_names = [[''.join([str(j) for j in k]) for j in range(len(C[k]))] for k in key_list]
    wt_names = reduce(lambda x,y : x + y, [n if len(n) == 1 else [n[i] + str(i+1) for i in range(len(n))] for n in cov_names])
    names = ['Co' + n for n in wt_names]
    Co = PolynomialRing(QQ, names)
    LCo = Co.gens()

    return LW, LCo, LCov
