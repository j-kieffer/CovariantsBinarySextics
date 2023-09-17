"""
    
"""

A.<a0,a1,a2,a3,a4,a5,a6> = PolynomialRing(QQ)
R.<x,y> = A[]

from sage.rings.invariants.invariant_theory import AlgebraicForm, transvectant

f = AlgebraicForm(2, 6, a0*x^6+a1*x^5*y+a2*x^4*y^2+a3*x^3*y^3+a4*x^2*y^4+a5*x*y^5+a6*y^6)

C16 = f

C20 = transvectant(f, f, 6)   
C24 = transvectant(f, f, 4)
C28 = transvectant(f, f, 2)

C32 = transvectant(f, C24, 4)
C36 = transvectant(f, C24, 2)
C38 = transvectant(f, C24, 1)
C312 = transvectant(f, C28, 1)

C40 = transvectant(C24, C24, 4)
C44 = transvectant(f, C32, 2)
C46 = transvectant(f, C32, 1)
C410 = transvectant(C28, C24, 1)

C52 = transvectant(C24, C32, 2)
C54 = transvectant(C24, C32, 1)
C58 = transvectant(C28, C32, 1)

C60 = transvectant(C32, C32, 2)
C661 = transvectant(C36, C32, 1)
C662 = transvectant(C38, C32, 2)

C72 = transvectant(f, transvectant(C32,C32,0), 4)
C74 = transvectant(f, transvectant(C32,C32,0), 3)

C82 = transvectant(C24, transvectant(C32,C32,0), 3)

C94 = transvectant(C38, transvectant(C32,C32,0), 4)

C100 = transvectant(f, transvectant(C32,transvectant(C32,C32,0),0), 6)
C102 = transvectant(f, transvectant(C32,transvectant(C32,C32,0),0), 5)

C122 = transvectant(C38, transvectant(C32,transvectant(C32,C32,0),0), 6)

C150 = transvectant(C38, transvectant(transvectant(C32,C32,0),transvectant(C32,C32,0),0), 8)
 

LW = [[2, 0], [4, 0], [6, 0], [10, 0], [15, 0], [1, 6], [2, 4], [2, 8], [3, 2], [3, 6], [3, 8], [3, 12], 
[4, 4], [4, 6], [4, 10], [5, 2], [5, 4], [5, 8], 
[6, 6], [6,6], [7, 2], [7, 4], [8, 2], [9, 4], [10, 2], [12, 2]]


def ridiculous(LW, wt):
    has_zero = [ any([x[i] == 0 for x in LW]) for i in range(2)]
    assert not all(has_zero)
    if (has_zero[1]) or ((not has_zero[0]) and (wt[0] < wt[1])):
        return ridiculous([[x[1],x[0]] for x in LW], [wt[1], wt[0]])
    exps = list(WeightedIntegerVectors(wt[1],[x[1] for x in LW]))
    return [exp for exp in exps if sum([exp[i]*LW[i][0] for i in range(len(exp))]) == wt[0]]

LCov = [C20.form().numerator(),C40.form().numerator(),C60.form().numerator(),C100.form().numerator(),C150.form().numerator(),
C16.form().numerator(),
C24.form().numerator(),C28.form().numerator(),
C32.form().numerator(),C36.form().numerator(),C38.form().numerator(),C312.form().numerator(),
C44.form().numerator(),C46.form().numerator(),C410.form().numerator(),
C52.form().numerator(),C54.form().numerator(),C58.form().numerator(),
C661.form().numerator(),C662.form().numerator(),
C72.form().numerator(),C74.form().numerator(),
C82.form().numerator(),
C94.form().numerator(),
C102.form().numerator(),
C122.form().numerator()]

LCovNotNorm = [C20.form(),C40.form(),C60.form(),C100.form(),C150.form(),
C16.form(),
C24.form(),C28.form(),
C32.form(),C36.form(),C38.form(),C312.form(),
C44.form(),C46.form(),C410.form(),
C52.form(),C54.form(),C58.form(),
C661.form(),C662.form(),
C72.form(),C74.form(),
C82.form(),
C94.form(),
C102.form(),
C122.form()] 

Co.<Co20,Co40,Co60,Co100,Co150,Co16,Co24,C28,Co32,Co36,Co38,Co312,Co44,Co46,Co410,Co52,Co54,Co58,Co661,Co662,Co72,Co74,Co82,Co94,Co102,Co122> = PolynomialRing(QQ)

LCo = [Co20,Co40,Co60,Co100,Co150,
Co16,
Co24,C28,
Co32,Co36,Co38,Co312,
Co44,Co46,Co410,
Co52,Co54,Co58,
Co661,Co662,
Co72,Co74,
Co82,
Co94,
Co102,
Co122]

def MakeCov(LCov,L):
    S = [[LCo[k]^L[k],LCov[k]^L[k]] for k in range(len(L))]
    S1 = prod(S[k][0] for k in range(len(S)))
    S2 = prod(S[k][1] for k in range(len(S)))
    return [S1,S2]
       



