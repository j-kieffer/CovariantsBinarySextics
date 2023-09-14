from functools import reduce
from sage.structure.sage_object import SageObject
from sage.matrix.constructor import Matrix
from sage.modules.free_module import VectorSpace
from sage.rings.big_oh import O
from sage.rings.infinity import infinity
from sage.rings.rational_field import QQ
from sage.rings.integer_ring import ZZ
from sage.all import NumberField, pari
from sage.sets.set import Set

from BinarySexticsCovariants import BinarySexticsCovariants as BSC
from FJexp import VectorFJexp, FJexp
from ThetaFourier import get_chi6m2
from Generators_Ring_Covariants_Sextic import RingOfCovariants
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

    def __init__(self, k, j):
        self.k = k
        self.j = j
        self.prec = 0
        self.basis = None
        self.decomposition = None
        self.fields = None
        #if j == 0:
        #    B = SMFPrecomputedScalarBasis(k)
        #    if not B is None:
        #        self.SetBasis(B)

    def SetBasis(self, L):
        CRing = RingOfCovariants()
        self.basis = [CRing(x) for x in L]

    def GetBasis(self, prec=3, taylor_prec=20):
        if (not self.basis is None and prec <= self.prec):
            return self.basis

        k = self.k
        j = self.j
        self.prec = prec
        print("Creating basis of covariants...")
        bsc = BSC(k+j//2,j)
        basis = bsc.GetBasis()
        print("Done!")
        if (len(basis) == 0):
            self.basis = []
            return self.basis

        if (SMF.prec < self.prec):
            print("Recomputing expansion of chi_6_m_2 to precision {}...".format(prec))
            SMF.chi = get_chi6m2(4*self.prec)
            SMF.prec = self.prec
            print("Done!")

        # Compute Taylor expansion: this is cheap.
        q = SMF.chi.parent().base().gens()
        chi = sum([(SMF.chi.monomial_coefficient(m) + O(q[0]**prec))*m for m in SMF.chi.monomials()])
        t_chi = VectorFJexp(chi, taylor_prec)

        # Substitution
        print("Substituting chi_6_m_2...")
        basis_expanded = [b.subs(bsc.DCov) for b in basis]
        exps = list(chi.dict().keys())
        t_chi_vals = list(t_chi.coeffs.values())
        R = t_chi_vals[0].parent()
        t_chi_comps = [t_chi.coeffs.get(exp, R(0)) for exp in exps]
        assert len(t_chi_comps) == 7
        gens = list(reduce(lambda x,y:x.union(y), [Set(b.variables()) for b in basis]))
        gens_exp = [g.subs(bsc.DCov) for g in gens]
        g_exps = [list(g_exp.dict().keys()) for g_exp in gens_exp]
        b_exps = list(basis_expanded[0].dict().keys())
        vals = list(basis_expanded[0].dict().values())
        U = vals[0].parent()
        a = U.gens()
        g_comps = [[g.dict().get(exp,U(0)) for exp in g_exps[i]] for i,g in enumerate(gens_exp)]
        sub_dict = {a[i] : t_chi_comps[i] for i in range(7)}
        g_comps_expanded = [[R(g_c.subs(sub_dict)) for g_c in g_comps_s] for g_comps_s in g_comps]
        g_c_e = [VectorFJexp([g_exps[l], g_comps_expanded[l]]) for l in range(len(g_exps))]
        g_sub_dict = {gens[i] : g_c_e[i] for i in range(len(gens))}
        b_comps_exp = [b.subs(g_sub_dict) for b in basis]
        print("Done!")

        #Linear algebra
        print("Solving linear system...")
        qexps = reduce(lambda x,y: x.union(y), [reduce(lambda x,y: x.union(y), [Set(list(b_c.coeffs.keys())) for b_c in b_c_e.coeffs.values()]) for b_c_e in b_comps_exp])
        ker = VectorSpace(QQ, len(basis))
        for qexp in qexps:
            for i in range(len(b_exps)):
                all_vals = []
                all_coeffs = []
                for j, b_c_e in enumerate(b_comps_exp):
                    b_c = b_c_e.coeffs[b_exps[i]]
                    mon = b_c.coeffs.get(qexp, FJexp(0))
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
        return self.basis

    def Dimension(self):
        return len(self.GetBasis())

    def WriteBasisToFile(self, filename):
        with open(filename, "w") as f:
            B = self.GetBasis()
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
        #print("Matrix of Hecke action at 2:\n{}".format(M))
        fac = M.characteristic_polynomial().factor()
        res = []
        fields = []
        for k in range(len(fac)):
            pol = fac[k][0]
            #print("Found eigenvalue with minimal polynomial {}".format(pol))
            F = NumberField(pol, "a")
            B = F.integral_basis()
            N = Matrix(F, M) - F.gen()
            V = N.left_kernel().basis()
            assert len(V) == 1, "Should find exactly one eigenvector"
            v = V[0].denominator() * V[0]; #coordinates of v are integers in F.
            #print("Found eigenvector {}".format(v))

            QQ_basis = []
            for l in range(pol.degree()):
                w = B[l] * v
                elt = 0
                for m in range(self.Dimension()):
                    elt += ZZ(w[m].trace()) * self.basis[m]
                elt = elt/elt.content()
                QQ_basis.append(elt)
            res.append(QQ_basis)

            #Get polredabs
            if F.degree() == 1:
                fields.append(QQ)
            else:
                R = pol.parent()
                pol = R(pari.polredabs(pol))
                fields.append(NumberField(pol, "a"))
        self.decomposition = res
        self.fields = fields
        return res

    def HeckeFields(self):
        if self.decomposition is None:
            self.HeckeDecomposition()
        return self.fields

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

def SMFPrecomputedScalarBasis(k):
    bases = {2: [],
             4: ["-Co20^2 + 3*Co40"],
             6: ["-28*Co20^3 + 57*Co20*Co40 + 3*Co60"],
             8: ["Co20^4 - 6*Co20^2*Co40 + 9*Co40^2"],
             10: ["-160*Co20^5 + 1341*Co20^3*Co40 - 2016*Co20*Co40^2 - 57*Co20^2*Co60 + 36*Co100",
                  "28*Co20^5 - 141*Co20^3*Co40 + 171*Co20*Co40^2 - 3*Co20^2*Co60 + 9*Co40*Co60"],
             12: ["784*Co20^6 - 3192*Co20^4*Co40 + 3249*Co20^2*Co40^2 - 168*Co20^3*Co60 + 342*Co20*Co40*Co60 + 9*Co60^2",
                  "-Co20^6 + 9*Co20^4*Co40 - 27*Co20^2*Co40^2 + 27*Co40^3",
                  "96*Co20^6 - 305*Co20^4*Co40 + 240*Co20^2*Co40^2 - 35*Co20^3*Co60 + 48*Co20*Co40*Co60 + 12*Co20*Co100"],
             14: ["160*Co20^7 - 1821*Co20^5*Co40 + 6039*Co20^3*Co40^2 + 57*Co20^4*Co60 - 6048*Co20*Co40^3 - 171*Co20^2*Co40*Co60 - 36*Co20^2*Co100 + 108*Co40*Co100",
                  "-28*Co20^7 + 225*Co20^5*Co40 - 594*Co20^3*Co40^2 + 3*Co20^4*Co60 + 513*Co20*Co40^3 - 18*Co20^2*Co40*Co60 + 27*Co40^2*Co60"],
             16: ["9952*Co20^8 - 80469*Co20^6*Co40 + 198720*Co20^4*Co40^2 - 879*Co20^5*Co60 - 155952*Co20^2*Co40^3 + 9495*Co20^3*Co40*Co60 - 14256*Co20*Co40^2*Co60 - 171*Co20^2*Co60^2 - 324*Co20^3*Co100 + 108*Co60*Co100",
                  "-784*Co20^8 + 5544*Co20^6*Co40 - 12825*Co20^4*Co40^2 + 168*Co20^5*Co60 + 9747*Co20^2*Co40^3 - 846*Co20^3*Co40*Co60 + 1026*Co20*Co40^2*Co60 - 9*Co20^2*Co60^2 + 27*Co40*Co60^2",
                  "Co20^8 - 12*Co20^6*Co40 + 54*Co20^4*Co40^2 - 108*Co20^2*Co40^3 + 81*Co40^4",
                  "-96*Co20^8 + 593*Co20^6*Co40 - 1155*Co20^4*Co40^2 + 35*Co20^5*Co60 + 720*Co20^2*Co40^3 - 153*Co20^3*Co40*Co60 + 144*Co20*Co40^2*Co60 - 12*Co20^3*Co100 + 36*Co20*Co40*Co100"],
             18: ["-21952*Co20^9 + 134064*Co20^7*Co40 - 272916*Co20^5*Co40^2 + 7056*Co20^6*Co60 + 185193*Co20^3*Co40^3 - 28728*Co20^4*Co40*Co60 + 29241*Co20^2*Co40^2*Co60 - 756*Co20^3*Co60^2 + 1539*Co20*Co40*Co60^2 + 27*Co60^3",
                  "-160*Co20^9 + 2301*Co20^7*Co40 - 11502*Co20^5*Co40^2 - 57*Co20^6*Co60 + 24165*Co20^3*Co40^3 + 342*Co20^4*Co40*Co60 - 18144*Co20*Co40^4 - 513*Co20^2*Co40^2*Co60 + 36*Co20^4*Co100 - 216*Co20^2*Co40*Co100 + 324*Co40^2*Co100",
                  "28*Co20^9 - 309*Co20^7*Co40 + 1269*Co20^5*Co40^2 - 3*Co20^6*Co60 - 2295*Co20^3*Co40^3 + 27*Co20^4*Co40*Co60 + 1539*Co20*Co40^4 - 81*Co20^2*Co40^2*Co60 + 81*Co40^3*Co60",
                  "-2688*Co20^9 + 14012*Co20^7*Co40 - 24105*Co20^5*Co40^2 + 1268*Co20^6*Co60 + 13680*Co20^3*Co40^3 - 4254*Co20^4*Co40*Co60 + 3456*Co20^2*Co40^2*Co60 - 105*Co20^3*Co60^2 - 336*Co20^4*Co100 + 144*Co20*Co40*Co60^2 + 684*Co20^2*Co40*Co100 + 36*Co20*Co60*Co100"]}
    if k in bases.keys():
        return bases[k]
    else:
        return None
