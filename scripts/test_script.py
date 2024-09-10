from BinarySexticsCovariants import BinarySexticsCovariants as BSC
from FJexp import VectorFJexp, FJexp
from SiegelModularForms import SMF
from ThetaFourier import Chi

# a,b,val, dim
data_tuples = [(5,12,-2,2),(7,12,-2,4),(9,12,-2,5)]

#bsc = BSC(11,12)
#bsc = BSC(5,12)

prec = 3
s_prec = 2

chi = Chi(6,-2).GetFJexp(prec)
t_chi = VectorFJexp(chi, s_prec)

for dt in data_tuples:
    print ("checking dt = ", dt)
    a,b,v,d = dt
    bsc = BSC(a,b)
    basis = bsc.GetBasis()
    b_comps_exp, b_exps = SMF._subs_chi(bsc, basis, chi, t_chi)
    V = VectorSpace(QQ, len(basis))
    ker = SMF._solve_linear_system(V, b_comps_exp, b_exps, up_to_val=v)
    assert ker.dimension() >= d
