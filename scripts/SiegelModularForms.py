from functools import reduce
from sage.structure.sage_object import SageObject
from sage.matrix.constructor import Matrix
from sage.modules.free_module import VectorSpace
from sage.rings.big_oh import O
from sage.rings.infinity import infinity
from sage.rings.rational_field import QQ
from sage.rings.integer_ring import ZZ
from sage.all import NumberField
from sage.sets.set import Set

from BinarySexticsCovariants import BinarySexticsCovariants as BSC
from ThetaFourier import get_chi6m2, get_taylor_exp
import subprocess

class SMF(SageObject):
    r"""
    Constructs Siegel modular forms of weight (k,j) (degree 2)

    sage: SMF(4,0).GetBasis()
    [-Co20^2 + 3*Co40]

    sage: SMF(6,0).GetBasis()
    [-28*Co20^3 + 57*Co20*Co40 + 3*Co60]

    sage: SMF(8,0).GetBasis()
    [Co20^4 - 6*Co20^2*Co40 + 9*Co40^2]

    sage: len(SMF(12,0).GetBasis())
    3
    """
    prec = 0
    chi = 0
    t_chi = 0
    
    def __init__(self, k, j, prec=3, taylor_prec=20):
        self.prec = prec
        print("Creating basis of covariants...")
        bsc = BSC(k+j//2,j)
        basis = bsc.GetBasis()
        print("Done!")
        if (len(basis) == 0):
            self.basis = []
            return
        if (SMF.prec < self.prec):
            print("Computing expansion of chi_6_m_2...")
            SMF.chi = get_chi6m2(4*self.prec)
            SMF.prec = self.prec
            print("Done!")
            # print("Producing Taylor expansion around s = 0...")
            # SMF.t_chi = get_taylor_exp(SMF.chi, taylor_prec)
            # print("Done!")
        q = SMF.chi.parent().base().gens()
        chi = sum([(SMF.chi.monomial_coefficient(m) + O(q[0]**prec))*m for m in SMF.chi.monomials()])
        t_chi = get_taylor_exp(chi, taylor_prec)
        print("Substituting chi_6_m_2...")
        basis_expanded = [b.subs(bsc.DCov) for b in basis]
        exps = list(chi.dict().keys())
        t_chi_vals = list(t_chi.dict().values())
        R = t_chi_vals[0].parent()
        t_chi_comps = [t_chi.dict().get(exp, R(0)) for exp in exps]
        assert len(t_chi_comps) == 7
        gens = list(reduce(lambda x,y:x.union(y), [Set(b.variables()) for b in basis]))
        x,y = t_chi.parent().gens()
        b_exps = list(basis_expanded[0].dict().keys())
        vals = list(basis_expanded[0].dict().values())
        U = vals[0].parent()
        a = U.gens()
        b_comps = [[b.dict().get(exp,U(0)) for exp in b_exps] for b in basis_expanded]
        sub_dict = {a[i] : t_chi_comps[i] for i in range(7)}
        x,y = t_chi.parent().gens()
        qb = t_chi.parent().base().gens()
        b_comps_expanded = [[R(b_c.subs(sub_dict))+O(qb[0]**prec) for b_c in b_comps_s] for b_comps_s in b_comps]
        print("Done!")
        print("Solving linear system...")
        qexps = reduce(lambda x,y: x.union(y), [reduce(lambda x,y: x.union(y), [Set(list(b_c.dict().keys())) for b_c in b_c_e]) for b_c_e in b_comps_expanded])
        ker = VectorSpace(QQ, len(basis))
        for qexp in qexps:
            for i in range(len(b_exps)):
                all_vals = []
                all_coeffs = []
                for j, b_c_e in enumerate(b_comps_expanded):
                    b_c = b_c_e[i]
                    mon = b_c.dict().get(qexp, R.base()(0))
                    v = mon.valuation()
                    coeffs = list(mon)
                    all_vals.append(v)
                    if (v >= 0):
                        all_coeffs.append([])
                    else:
                        all_coeffs.append(coeffs[:-v])
                min_val = min(all_vals)
                if (min_val < 0):
                    max_len = max([len(all_coeffs[j]) + all_vals[j] for j in range(len(all_vals)) if all_vals[j] < 0])
                    for j in range(len(all_vals)):
                        v = all_vals[j]
                        if (v >= 0):
                            v = max_len
                        all_coeffs[j] = [0 for l in range(v-min_val)] + all_coeffs[j]
                max_len = max([len(a) for a in all_coeffs])
                all_coeffs = [a + [0 for j in range(max_len-len(a))] for a in all_coeffs]
                mat_coeffs = Matrix(all_coeffs)
                ker_mat = mat_coeffs.kernel()
                ker = ker.intersection(ker_mat)
        print("Done!")
        # Take only highest valuations
        self.basis = [sum([b.denominator()*b[i]*basis[i] for i in range(len(basis))]) for b in ker.basis()]
        # This is not computed yet.
        self.decomposition = None

    def GetBasis(self):
        return self.basis

    def Dimension(self):
        return len(self.basis)

    def WriteBasisToFile(self, filename):
        with open(filename, "w") as f:
            B = self.basis
            d = self.Dimension()
            for k in range(d):
                f.write(str(B[k]))
                if k < d - 1:
                    f.write("\n")

    def WriteDecompositionToFile(self, filename):
        with open(filename, "w") as f:
            D = self.HeckeDecomposition()
            d = len(D)
            for k in range(d):
                e = len(D[k])
                for l in range(e):
                    f.write(str(D[k][l]))
                    if l < e - 1:
                        f.write("\n")
                if k < d - 1:
                    f.write("\n\n")

    # This computes the Hecke action on full basis up to some cofactor
    def HeckeAction(self, q, filename="hecke", log=True):
        self.WriteBasisToFile(filename + ".in")
        call = ["./hecke.exe", "{}".format(q), filename + ".in", filename + ".out"]
        run = subprocess.run(call, capture_output=True, check=True)
        subprocess.run(["rm", filename + ".in"])
        if log:
            with open(filename + ".log", "w") as f:
                f.write(run.stdout.decode("ASCII"))

        d = self.Dimension()
        M = Matrix(ZZ, d, d)
        with open(filename + ".out", "r") as f:
            for k in range(d):
                line = f.readline().strip("[]\n").split(" ")
                assert len(line) == d, "Line is not of expected length {}".format(d)
                for j in range(d):
                    M[k,j] = ZZ(line[j])
        subprocess.run(["rm", filename + ".out"])
        return M

    def HeckeDecomposition(self):
        if not self.decomposition is None:
            return self.decomposition
        M = self.HeckeAction(2)
        print("Matrix of Hecke action at 2:\n{}".format(M))
        fac = M.characteristic_polynomial().factor()
        res = []
        for k in range(len(fac)):
            pol = fac[k][0]
            print("Found eigenvalue with minimal polynomial {}".format(pol))
            F = NumberField(pol, "a")
            B = F.integral_basis()
            N = Matrix(F, M) - F.gen()
            V = N.left_kernel().basis()
            assert len(V) == 1, "Should find exactly one eigenvector"
            v = V[0].denominator() * V[0]; #coordinates of v are integers in F.
            print("Found eigenvector {}".format(v))

            QQ_basis = []
            for l in range(pol.degree()):
                w = B[l] * v
                elt = 0
                for m in range(self.Dimension()):
                    elt += ZZ(w[m].trace()) * self.basis[m]
                elt = elt/elt.content()
                QQ_basis.append(elt)
            res.append(QQ_basis)
        self.decomposition = res
        return res

    def HeckeActionOnEigenvectors(self, q, filename="hecke", log=True):
        self.WriteDecompositionToFile(filename + ".in")
        call = ["./hecke.exe", "{}".format(q), filename + ".in", filename + ".out"]
        run = subprocess.run(call, capture_output=True, check=True)
        subprocess.run(["rm", filename + ".in"])
        if log:
            with open(filename + ".log", "w") as f:
                f.write(run.stdout.decode("ASCII"))

        res = []
        D = self.HeckeDecomposition()
        with open(filename + ".out", "r") as f:
            for i in range(len(D)):
                d = len(D[i])
                M = Matrix(ZZ, d, d)
                for k in range(d):
                    line = f.readline().strip("[]\n").split(" ")
                    assert len(line) == d, "Line is not of expected length {}".format(d)
                    for j in range(d):
                        M[k,j] = ZZ(line[j])
                res.append(M)
                f.readline()
                f.readline()
        subprocess.run(["rm", filename + ".out"])
        return res
