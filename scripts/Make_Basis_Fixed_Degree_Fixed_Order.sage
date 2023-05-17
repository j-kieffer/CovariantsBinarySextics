
load('Generators_Ring_Covariants_Sextic.sage')

LW = [
[2, 0], [4, 0], [6, 0], [10, 0], [15, 0], 
[1, 6], 
[2, 4], [2, 8], 
[3, 2], [3, 6], [3, 8], [3, 12], 
[4, 4], [4, 6], [4, 10], 
[5, 2], [5, 4], [5, 8], 
[6, 6], [6,6], 
[7, 2], [7, 4], 
[8, 2], 
[9, 4], 
[10, 2], 
[12, 2]]


def ridiculous(LW, wt):
    has_zero = [ any([x[i] == 0 for x in LW]) for i in range(2)]
    assert not all(has_zero)
    if (has_zero[1]) or ((not has_zero[0]) and (wt[0] < wt[1])):
        return ridiculous([[x[1],x[0]] for x in LW], [wt[1], wt[0]])
    exps = list(WeightedIntegerVectors(wt[1],[x[1] for x in LW]))
    return [exp for exp in exps if sum([exp[i]*LW[i][0] for i in range(len(exp))]) == wt[0]]

Co.<Co20,Co40,Co60,Co100,Co150,Co16,Co24,Co28,Co32,Co36,Co38,Co312,Co44,Co46,Co410,Co52,Co54,Co58,Co661,Co662,Co72,Co74,Co82,Co94,Co102,Co122> = PolynomialRing(QQ)

LCo = [
Co20,Co40,Co60,Co100,Co150,
Co16,
Co24,Co28,
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
       
def MakeLinComb(a,b):
    A = ridiculous(LW, [a,b])
    l = len(A)
    z = var(','.join('z%s'%i for i in range(l)))
    LinComb1 = sum(z[i]*MakeCov(LCov,A[i])[0] for i in range(l))
    LinComb2 = sum(z[i]*MakeCov(LCov,A[i])[1] for i in range(l))
    LinComb = [LinComb1,LinComb2]
    return LinComb



