from functools import reduce
from sage.structure.sage_object import SageObject
from sage.matrix.constructor import Matrix
from sage.modules.free_module import VectorSpace
from sage.rings.big_oh import O
from sage.rings.infinity import infinity
from sage.rings.rational_field import QQ
from sage.rings.integer_ring import ZZ
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.all import NumberField, pari
from sage.sets.set import Set

from BinarySexticsCovariants import BinarySexticsCovariants as BSC
from DimFormulaSMFScalarValuedLevel1WithoutCharacter import dim_splitting_SV_All_weight
from DimFormulaSMFVectorValuedLevel1WithoutCharacter import dim_splitting_VV_All_weight
from DimFormulaSMFScalarValuedLevel1WithCharacter import dim_splitting_SV_All_weight_charac
from DimFormulaSMFVectorValuedLevel1WithCharacter import dim_splitting_VV_All_weight_charac
from FJexp import VectorFJexp, FJexp
from ThetaFourier import Chi
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

    def __init__(self, k, j, character = False):
        self.k = k
        self.j = j
        self.prec = 3
        self.dim = None
        self.basis = None
        self.decomposition = None
        self.fields = None
        self.character = character

    def __str__(self):
        s = "Space of Siegel modular form of weight ("+str(self.k)+"," + str(self.j) + ")"
        if self.character:
            s += " with character"
        return s

    def __repr__(self):
        return str(self)

    def SetBasis(self, L):
        CRing = RingOfCovariants()
        self.basis = [CRing(x) for x in L]

    def Dimension(self):
        if not self.dim is None:
            return self.dim

        if self.j == 0 and self.character:
            self.dim = dim_splitting_SV_All_weight_charac(self.k)['total_dim']
        elif self.j == 0:
            self.dim = dim_splitting_SV_All_weight(self.k)['total_dim']
        elif self.character:
            self.dim = dim_splitting_VV_All_weight_charac(self.k, self.j)['total_dim']
        else:
            self.dim = dim_splitting_VV_All_weight(self.k, self.j)['total_dim']
        return self.dim

    def _subs_chi(basis, chi, t_chi, s_prec):
        RingCov = BSC.LCov[0].parent()
        basis_expanded = [RingCov(b.subs(BSC.DCov)) for b in basis]
        exps = list(chi.dict().keys())
        t_chi_vals = list(t_chi.coeffs.values())
        R = t_chi_vals[0].parent()
        t_chi_comps = [t_chi.coeffs.get(exp, R(0)) for exp in exps]
        assert len(t_chi_comps) == 7
        gens = list(reduce(lambda x,y:x.union(y), [Set(b.variables()) for b in basis]))
        gens_exp = [g.subs(BSC.DCov) for g in gens]
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
        #the above line is completely broken when b = 1, so instead, do:
        for l in range(len(b_comps_exp)):
            if basis[l] == 1:
                b_comps_exp[l] = VectorFJexp(chi.parent()(1), s_prec)
        return b_comps_exp, b_exps

    def _create_coeff_matrix(b_comps_exp, b_exps, qexp, i, up_to_val):
        Rs = reduce(lambda x,y: x + y,
                    [reduce(lambda x,y : x + y,
                            [list(b_c.coeffs.values()) for b_c in b_c_e.coeffs.values()])
                     for b_c_e in b_comps_exp])[0].parent()
        all_vals = []
        all_coeffs = []
        for b_c_e in b_comps_exp:
            b_c = b_c_e.coeffs[b_exps[i]]
            mon = b_c.coeffs.get(qexp, Rs(0))
            v = mon.valuation()
            coeffs = list(mon)
            all_vals.append(v)
            if (v >= up_to_val):
                all_coeffs.append([])
            else:
                all_coeffs.append(coeffs[:up_to_val-v])
        min_val = min(all_vals)
        if (min_val < up_to_val):
            max_len = max([len(all_coeffs[j]) + all_vals[j] for j in range(len(all_vals)) if all_vals[j] < up_to_val])
            for j in range(len(all_vals)):
                v = all_vals[j]
                if (v >= up_to_val):
                    v = max_len
                all_coeffs[j] = [0 for l in range(v-min_val)] + all_coeffs[j]
        max_len = max([len(a) for a in all_coeffs])
        all_coeffs = [a + [0 for j in range(max_len-len(a))] for a in all_coeffs]
        mat_coeffs = Matrix(all_coeffs)
        return mat_coeffs

    def _solve_linear_system(V, b_comps_exp, b_exps, up_to_val=0):
        ker = V
        qexps = reduce(lambda x,y: x.union(y),
                       [reduce(lambda x,y: x.union(y),
                               [Set(list(b_c.coeffs.keys()))
                                for b_c in b_c_e.coeffs.values()])
                        for b_c_e in b_comps_exp])
        for qexp in qexps:
            for i in range(len(b_exps)):
                mat_coeffs = SMF._create_coeff_matrix(b_comps_exp, b_exps, qexp, i, up_to_val)
                ker_mat = mat_coeffs.kernel()
                ker = ker.intersection(ker_mat)
        return ker

    def _GetBasisWithPoles(bsc, prec, taylor_prec, pole_ord, dim):
        print("Creating basis of covariants...")
        basis = bsc.GetBasis()
        print("Done!")
        if (len(basis) == 0):
            basis = []
            return basis, prec, taylor_prec

        V = VectorSpace(QQ, len(basis))
        ker = V
        prec = prec-1
        s_prec = taylor_prec-10
        print("Attempting to find a basis for covariants in "+str(bsc)+" with pole of order at most "+str(pole_ord))
        print("Trying to get to dimension ", dim)
        is_first_outer = True
        while ((is_first_outer) or (ker.dimension() > dim)):
            is_first_outer = False
            prec += 1
            if (SMF.prec < prec):
                print("Recomputing expansion of chi_6_m_2 to precision {}...".format(prec))
                SMF.chi = Chi(6,-2).GetFJexp(prec)
                SMF.prec = prec
                print("Done!")

            ker_dim = infinity
            is_first = True
            while ((is_first) or
                   ((ker.dimension() > dim) and (ker.dimension() < ker_dim))):
                print("Dimension obtained is ", ker.dimension())
                is_first = False
                ker_dim = ker.dimension()
                s_prec += 10
                # Compute Taylor expansion: this is cheap.
                print("increasing precision in s to {}...".format(s_prec))
                t_chi = VectorFJexp(SMF.chi, s_prec)

                # Substitution
                print("Substituting chi_6_m_2 in basis...")
                b_comps_exp, b_exps = SMF._subs_chi(basis, SMF.chi, t_chi, s_prec)
                print("Done!")

                #Linear algebra
                print("Solving linear system...")
                ker = SMF._solve_linear_system(V, b_comps_exp, b_exps, up_to_val= -pole_ord)
                print("Done!")

        # Take only highest valuations
        basis = [sum([b.denominator()*b[i]*basis[i] for i in range(len(basis))]) for b in ker.basis()]
        return basis, prec, s_prec

    def GetBasis(self, prec=3, taylor_prec=20):
        if (not self.basis is None and prec <= self.prec):
            return self.basis

        k = self.k
        j = self.j
        chi10 = SMF._GetBasisWithPoles(BSC(10,0), prec, taylor_prec, -1, 1)[0][0]
        self.basis = []
        dim = self.Dimension()

        a_max = k + j//2
        if (self.character):
            a_max -= 5

        a_min = a_max % 10
        pole_ord = 2 * (a_max // 10)
        if (self.character):
            pole_ord += 1

        a = a_min
        while (len(self.basis) < dim):
            bsc = BSC(a, j)
            self.basis, self.prec, self.s_prec = SMF._GetBasisWithPoles(bsc, prec, taylor_prec, pole_ord, dim)
            self.basis = [(chi10)**(pole_ord // 2) * b for b in self.basis]
            a += 10
            pole_ord -= 2

        return self.basis

    def WriteBasisToFile(self, filename, mode):
        d = self.Dimension()
        s = "Space of Siegel modular forms of weight ({}, {})".format(self.k, self.j)
        if d == 0:
            return
        if self.character:
            s += " with character\n"
            i = 1
        else:
            s += " without character\n"
            i = 0
        with open(filename, mode) as f:
            if mode == "a":
                f.write("\n\n")
            B = self.GetBasis()
            f.write(s)
            f.write(str(i) + "\n")
            for k in range(d):
                f.write(str(B[k]))
                if k < d - 1:
                    f.write("\n")

    def WriteDecompositionToFile(self, filename, mode):
        if self.Dimension() == 0:
            return
        s = "Eigenform of weight ({}, {})".format(self.k, self.j)
        if self.character:
            s += " with character"
            i = 1
        else:
            s += " without character"
            i = 0
        F = self.HeckeFields()
        D = self.HeckeDecomposition()
        d = len(D)
        with open(filename, mode) as f:
            if mode == "a":
                f.write("\n\n")
            for k in range(d):
                f.write(s + ", number {}\n".format(k + 1))
                f.write(str(i) + "\n")
                f.write(str(F[k].defining_polynomial()))
                f.write("\n")
                e = len(D[k])
                for l in range(e):
                    f.write(str(D[k][l]))
                    if l < e - 1:
                        f.write("\n")
                if k < d - 1:
                    f.write("\n\n")

    # This computes the Hecke action on full basis
    def HeckeAction(self, q, filename="../data/temp", log=True):
        self.WriteBasisToFile(filename + ".in", "w")
        call = ["./hecke_matrices.exe", "{}".format(q), filename + ".in", filename + ".out"]
        run = subprocess.run(call, capture_output=True, check=True)
        subprocess.run(["rm", filename + ".in"])
        if log:
            with open(filename + ".log", "w") as f:
                f.write(run.stdout.decode("ASCII"))

        d = self.Dimension()
        M = Matrix(QQ, d, d)
        with open(filename + ".out", "r") as f:
            for k in range(d):
                line = f.readline().strip("[]\n").split(" ")
                assert len(line) == d, "Line is not of expected length {}".format(d)
                for j in range(d):
                    M[k,j] = QQ(line[j])
        subprocess.run(["rm", filename + ".out"])
        return M

    # This computes a list of Hecke fields as QQ(x)/f_i(x) and lists of
    # covariants over QQ [c^i_0, ..., c_i^{d-1}] such that \sum c^i_k x^k is a
    # Hecke eigenform
    def HeckeDecomposition(self):
        if not self.decomposition is None:
            return self.decomposition
        M = self.HeckeAction(3)
        #print("Matrix of Hecke action at 2:\n{}".format(M))
        fac = M.characteristic_polynomial().factor()
        res = []
        fields = []
        roots = []
        for k in range(len(fac)):
            pol = fac[k][0]
            print("Found eigenvalue with minimal polynomial {}".format(pol))
            if pol.degree() == 1:
                F = QQ
                root = pol.roots()[0][0]
            else:
                R = pol.parent()
                oldpol = pol
                newpol = R(pari.polredbest(pol))
                while (newpol != oldpol):
                    oldpol = newpol
                    newpol = R(pari.polredbest(newpol))
                    print("After one more polredbest:")
                    print(newpol)
                #newpol = R(pari.polredabs(newpol))
                Ry = PolynomialRing(QQ, "y")
                F = NumberField(newpol, "a")
                print("Number field constructed")
                root = F(pari.nfroots(Ry(newpol), pol)[0])
            print("Hecke decomposition: found factor and number field")
            print(pol)
            print(F)
            fields.append(F)
            roots.append(root)
        self.fields = fields

        for k in range(len(self.fields)):
            F = self.fields[k]
            N = Matrix(F, M)
            V = (N - roots[k]).left_kernel().basis()
            assert len(V) == 1, "Should find exactly one eigenvector"
            v = V[0].denominator() * V[0]; #coordinates of v are integers in F.
            #print("Found eigenvector {}".format(v))

            coefficients = []
            g = ZZ(1)
            for l in range(F.degree()):
                if F is QQ:
                    w = v
                else:
                    w = [y.polynomial().padded_list(F.degree())[l] for y in v]
                elt = 0
                for m in range(self.Dimension()):
                    elt += w[m] * self.basis[m]
                coefficients.append(elt)
                g = g.gcd(elt.content())
            for l in range(F.degree()):
                coefficients[l] = coefficients[l]/g
            res.append(coefficients)

        self.decomposition = res
        self.fields = fields
        return res

    def HeckeFields(self):
        if self.decomposition is None:
            self.HeckeDecomposition()
        return self.fields

    def HeckeActionOnEigenvectors(self, q, filename="../data/temp", log=True):
        self.WriteDecompositionToFile(filename + ".in", "w")
        call = ["./hecke_eigenvalues.exe", "{}".format(q), filename + ".in", filename + ".out"]
        if self.character:
            call[1] = "./hecke_eigenvalues_with_character.exe"
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

#polredabs is running into problems when k is too large...
def WriteAllSpaces(kbound = 20, jbound = 16, dimbound = 6, filename = "../data/all.in"):
    mode = "w"
    for j in range(0, jbound + 1, 2):
        for k in range(kbound + 1):
            if k == 0 and j == 0:
                continue
            for char in [False, True]:
                print("\nDoing SMF({}, {}, character = {})".format(k, j, char))
                S = SMF(k, j, character = char)
                d = S.Dimension()
                if d > 0 and d <= dimbound:
                    S.GetBasis()
                    print("Basis done")
                    S.WriteDecompositionToFile(filename, mode);
                    mode = "a"

def WritePrimes(bound = 200, filename = "../data/primes.in"):
    with open(filename, "w") as f:
        for j in range(bound, 1, -1):
            if ZZ(j).is_prime():
                f.write(str(j))
                f.write("\n")
                if j*j <= bound:
                    f.write(str(j*j))
                    f.write("\n")
