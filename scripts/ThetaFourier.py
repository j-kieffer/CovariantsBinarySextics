import sage
from sage.all import GF, ZZ, QQ, prod, PolynomialRing, exp
from pathlib import Path
from sage.all import FunctionField
from sage.rings.polynomial.laurent_polynomial_ring import LaurentPolynomialRing
from sage.rings.power_series_ring import PowerSeriesRing
from sage.structure.sage_object import SageObject
from sage.matrix.matrix_space import MatrixSpace
from sage.misc.functional import sqrt
from sage.functions.other import ceil, floor
from sage.rings.big_oh import O
from sage.rings.number_field.number_field import QuadraticField
from sage.functions.other import factorial

class ThetaCharacteristic(SageObject):

    M2F2 = MatrixSpace(GF(2), 2)
    def M2F2_sort(a):
        return a.sort_key

    def get_all_chars():
        return sorted([ThetaCharacteristic(x) for x in ThetaCharacteristic.M2F2], key=ThetaCharacteristic.M2F2_sort)

    def get_odd_chars():
        """
        Returns all odd characteristics, ordered lexicographically.

        EXAMPLES:

        Making sure we get the right order. ::

            sage: ThetaCharacteristic.get_odd_chars()
            [[0 1]
             [0 1],
             [0 1]
             [1 1],
             [1 0]
             [1 0],
             [1 0]
             [1 1],
             [1 1]
             [0 1],
             [1 1]
             [1 0]]
        """
        return sorted([x for x in ThetaCharacteristic.get_all_chars() if x.is_odd()], key=ThetaCharacteristic.M2F2_sort)

    def get_even_chars():
        return sorted([x for x in ThetaCharacteristic.get_all_chars() if x.is_even()], key=ThetaCharacteristic.M2F2_sort)

    def __init__(self, mat):
        """
        initializes a characteristic from a 2 by 2 matrix over GF(2)
        """
        self.mat = mat
        self.mu = mat[0]
        self.nu = mat[1]
        self.mu1 = ZZ(self.mu[0])
        self.mu2 = ZZ(self.mu[1])
        self.nu1 = ZZ(self.nu[0])
        self.nu2 = ZZ(self.nu[1])
        self.sort_key = tuple(list(self.mu) + list(self.nu))
        return

    def is_odd(self):
        return self.mu*self.nu == 1

    def is_even(self):
        return self.mu*self.nu == 0

    def __repr__(self):
        return repr(self.mat)

# Ideas for further optimization:
# - compute all theta expansions at once
# - store expansions to avoid recomputing them, esp. cusp expansions (only q_prec varies)
# - use ideal (q1^n, q3^n) with less generators?
# TODO:
# - write documentation (EXAMPLES...)

class NewChi(SageObject):

    #todo: cache some expansions?

    def __init__(self, k, j = 0):
        #at the moment we only support Chi(-2,6), Chi(8,6), Chi(10,0)
        assert [k, j] in [[-2, 6], [8, 6], [10, 0]]
        self.weight = [k, j]

    def weight(self):
        return self.weight

    def __repr__(self):
        if self.weight == [8, 6]:
            return "Siegel modular form chi_{8,6}"
        elif self.weight == [10, 0]:
            return "Siegel modular form chi_10"
        else: # self.weight == [-2, 6]
            return "Siegel modular function chi_{-2,6}"

    ###### Helper functions for this class ######

    def _theta(q18, q38, q24, q_prec, char, gradient = [0,0]):
        #omit power of i
        #enumerate all points (n0,n1) such that (2*n0+a0)^2 + (2*n1+a1)^2 <= q_prec
        nmax = ceil((sqrt(q_prec) + 1)/2)
        all_pts = []
        for n0 in range(-nmax, nmax + 1):
            for n1 in range(-nmax, nmax + 1):
                if (2*n0+ char.mu1) ** 2 + (2*n1 + char.mu2) ** 2 <= q_prec:
                    all_pts.append([n0,n1])
        #sum
        res = q18.parent()(0)
        for pt in all_pts:
            n0 = pt[0]
            n1 = pt[1]
            term = q24 ** ((2 * n0 + char.mu1) * (2 * n1 + char.mu2))
            term *= q18 ** ((2 * n0 + char.mu1) ** 2) * q38 ** ((2 * n1 + char.mu2) ** 2)
            term *= (n0 + char.mu1/2) ** gradient[0] * (n1 + char.mu2/2) ** gradient[1]
            if (n0 * char.nu1 + n1 * char.nu2) % 2 == 1:
                term = -term
            res += term
        return res

    def _diag_q24(s, s_prec):
        q24 = s.parent()(0)
        c = QQ(1)
        d = QQ(1)/4
        for i in range(s_prec + 1):
            q24 += c/ZZ(i).factorial() * s ** i
            c *= d
            d -= 1
        return q24

    def _diag_parent_ring(q_prec, s_prec):
        A = PolynomialRing(QQ, ["q1", "q3", "s"])
        q1 = A.gen(0)
        q3 = A.gen(1)
        s = A.gen(2)
        generators = [q1 ** i * q3 ** (q_prec + 1 - i)
                      for i in range(q_prec + 2)] + [s**(s_prec + 1)]
        I = A.ideal(generators)
        R = A.quotient(I, names = ["q1", "q3", "s"])
        return R

    def _cusp_parent_ring(q_prec):
        A = PolynomialRing(QQ, ["q1", "q3", "q2", "q2inv"]);
        q1 = A.gen(0)
        q3 = A.gen(1)
        q2 = A.gen(2)
        q2inv = A.gen(3)
        generators = [q1 ** i * q3 ** (q_prec + 1 - i)
                      for i in range(q_prec + 2)] + [q2 * q2inv - 1];
        I = A.ideal(generators)
        R = A.quotient(I, names = ["q1", "q3", "q2", "q2inv"])
        return R

    def _diag_convert(qexp, q_shift, s_shift):
        R = qexp.parent()
        coeffs = qexp.coefficients()
        exponents = qexp.exponents()
        res = R(0)
        q1 = R.gen(0)
        q3 = R.gen(1)
        s = R.gen(2)
        for i in range(len(exponents)):
            e = exponents[i]
            assert e[0] % 8 == 0 and e[1] % 8 == 0
            res += coeffs[i] * q1 ** (e[0] / 8 + q_shift) * q3 ** (e[1] / 8 + q_shift) * s ** (e[2] + s_shift)
        return res

    def _cusp_convert(qexp, q1q3_shift = 0):
        R = qexp.parent()
        coeffs = qexp.coefficients()
        exponents = qexp.exponents()
        res = R(0)
        q1 = R.gen(0)
        q3 = R.gen(1)
        q2 = R.gen(2)
        q2inv = R.gen(3)
        for i in range(len(exponents)):
            e = exponents[i]
            assert e[0] % 8 == 0 and e[1] % 8 == 0 and e[2] % 4 == 0 and e[3] % 4 == 0
            res += coeffs[i] * q1 ** (e[0] / 8 + q1q3_shift) * q3 ** (e[1] / 8 + q1q3_shift) * q2 ** (e[2] / 4) * q2inv ** (e[3] / 4)
        return res

    def _binary_sextic(R, coeffs):
        Rxy = PolynomialRing(R, ["x", "y"])
        x = Rxy.gen(0)
        y = Rxy.gen(1)
        coeffs = coeffs + [0 for i in range(7 - len(coeffs))]
        res = Rxy(0)
        for i in range(7):
            res += coeffs[i] * x ** i * y ** (6 - i)
        return res

    def _cusp_div_diag(qexp, delta):
        R = qexp.parent()
        pol = qexp.lift()
        A = pol.parent()
        q2 = A.gen(2)
        q2inv = A.gen(3)
        d = pol.degree(q2inv)
        pol = (q2**d * qexp).lift()
        r = (q2 ** 2 - 2 * q2 + 1) ** delta
        assert r.divides(pol)
        pol = pol // r
        return R(pol) * q2inv ** (d - delta)

    ###### Main methods ######

    def diagonal_expansion(self, q_prec, s_prec):
        #divided by q1 q3 s^2 for (10,0) and q1 q3 s for (8,6)
        q8_prec = 8 * (q_prec + 1)
        s8_prec = s_prec + 1
        if self.weight == [10, 0] or self.weight == [-2, 6]:
            s8_prec += 1

        R8 = NewChi._diag_parent_ring(q8_prec, s8_prec)
        R = NewChi._diag_parent_ring(q_prec, s_prec)
        R8x = PolynomialRing(R8, "x")
        x = R8x.gen()
        q18 = R8.gen(0)
        q38 = R8.gen(1)
        q24 = NewChi._diag_q24(R8.gen(2), s8_prec);
        even = ThetaCharacteristic.get_even_chars()
        odd = ThetaCharacteristic.get_odd_chars()

        if self.weight == [10, 0]:
            res = R8(1)
            for char in even:
                res *= NewChi._theta(q18, q38, q24, q8_prec, char)
            res = QQ(2) ** (-12) * res ** 2
            res = R(NewChi._diag_convert(res.lift(), -1, -2))
            return res

        elif self.weight == [8, 6]:
            res = R8x(1)
            for char in even:
                res *= NewChi._theta(q18, q38, q24, q8_prec, char)
            for char in odd:
                res *= (NewChi._theta(q18, q38, q24, q8_prec, char, gradient = [1,0]) * x
                        + NewChi._theta(q18, q38, q24, q8_prec, char, gradient = [0,1]))
            res *= QQ(2) ** (-6)
            coeffs = [R(NewChi._diag_convert(c.lift(), -1, -1))
                      for c in res.coefficients(sparse=False)]
            return NewChi._binary_sextic(R, coeffs)

        elif self.weight == [-2, 6]: #can reuse even thetas
            res = R8(1)
            for char in even:
                res *= NewChi._theta(q18, q38, q24, q8_prec, char)
            chi10 = QQ(2) ** (-12) * res ** 2
            chi10 = R(NewChi._diag_convert(chi10.lift(), -1, -2))

            res = R8x(res)
            q24 = NewChi._diag_q24(R8.gen(2), s8_prec - 1);
            for char in odd:
                res *= (NewChi._theta(q18, q38, q24, q8_prec, char, gradient = [1,0]) * x
                        + NewChi._theta(q18, q38, q24, q8_prec, char, gradient = [0,1]))
            res *= QQ(2) ** (-6)
            coeffs = [R(NewChi._diag_convert(c.lift(), -1, -1))
                      for c in res.coefficients(sparse=False)]
            return NewChi._binary_sextic(R, coeffs) / chi10

    def cusp_expansion(self, q_prec):
        # divided by q1 q3 (q2 - 2 + q2inv) for chi10 and q1 q3 for chi86
        q8_prec = 8 * (q_prec + 1)
        R8 = NewChi._cusp_parent_ring(q8_prec)
        R = NewChi._cusp_parent_ring(q_prec)
        q18 = R8.gen(0)
        q38 = R8.gen(1)
        q24 = R8.gen(2)
        R8x = PolynomialRing(R8, "x")
        x = R8x.gen()
        even = ThetaCharacteristic.get_even_chars()
        odd = ThetaCharacteristic.get_odd_chars()

        if self.weight == [10, 0]:
            res = R8(1)
            for char in even:
                res *= NewChi._theta(q18, q38, q24, q8_prec, char)
            res = QQ(2) ** (-12) * res ** 2
            res = R(NewChi._cusp_convert(res.lift(), -1))
            res = NewChi._cusp_div_diag(res, 1)
            return res

        elif self.weight == [8, 6]:
            res = R8x(1)
            for char in even:
                res *= NewChi._theta(q18, q38, q24, q8_prec, char)
            for char in odd:
                res *= (NewChi._theta(q18, q38, q24, q8_prec, char, gradient = [1,0]) * x
                        + NewChi._theta(q18, q38, q24, q8_prec, char, gradient = [0,1]))
            res *= QQ(2) ** (-6)
            coeffs = [R(NewChi._cusp_convert(c.lift(), -1))
                      for c in res.coefficients(sparse=False)]
            return NewChi._binary_sextic(R, coeffs)

        else: # self.weight == [-2, 6]
            res = R8(1)
            for char in even:
                res *= NewChi._theta(q18, q38, q24, q8_prec, char)
            chi10 = QQ(2) ** (-12) * res ** 2
            chi10 = R(NewChi._cusp_convert(chi10.lift(), -1))
            chi10 = NewChi._cusp_div_diag(chi10, 1)

            res = R8x(res)
            for char in odd:
                res *= (NewChi._theta(q18, q38, q24, q8_prec, char, gradient = [1,0]) * x
                        + NewChi._theta(q18, q38, q24, q8_prec, char, gradient = [0,1]))
            res *= QQ(2) ** (-6)
            coeffs = [R(NewChi._cusp_convert(c.lift(), -1))
                      for c in res.coefficients(sparse=False)]
            return NewChi._binary_sextic(R, coeffs) / chi10

class qExpSiegel(SageObject):
    def __init__(self, qexp, gens, base):
       self.base = base
       self.gens = gens
       self.qexp = qexp

    def __repr__(self):
        return repr(self.qexp)

    def __call__(self, x1, x12, x2, y1, y2):
        coeffs = self.coefficients()
        eval_coeffs = {}
        for m in coeffs.keys():
            R = coeffs[m].base_ring()
            value_func = coeffs[m](R(y1), R(y2))
            value = value_func.substitute(x12)
            mon = x1**m.exponents()[0][0]*x2**m.exponents()[0][1]
            eval_coeffs[mon] = value
        return sum([eval_coeffs[m]*m for m in eval_coeffs.keys()])

    def variables(self):
        return self.gens

    def coefficients(self):
        return self.qexp.coefficients()

    def __eq__(self, other):
        # print("type(other)=", type(other))
        if (type(other) in [sage.rings.multi_power_series_ring_element.MPowerSeries, sage.rings.integer.Integer, int]):
            return self.qexp == other
        if (type(other) == ThetaWithChar):
            return self.qexp == other.qexp

    def base_ring(self):
        return self.base

    def derivative(self, z):
        coeffs = self.coefficients()
        deriv_coeffs = {}
        for m in coeffs.keys():
            assert z in coeffs[m].parent().gens()
            deriv_coeffs[m] = coeffs[m].derivative(z)
        qexp = sum([deriv_coeffs[m]*m for m in deriv_coeffs.keys()])
        return qExpSiegel(qexp, self.gens, self.base)

    def __rmul__(self, qexp):
        return qExpSiegel(qexp*self.qexp, self.gens, self.base)

class ThetaWithChar(qExpSiegel):
    def __init__(self, char, prec, const=False):
        if const:
            self.base = QQ
            S = FunctionField(QQ, "r12")
            r12 = S.gen()
        else:
            QQi = QuadraticField(-1, "i")
            i = QQi.gen()
            self.base = QQi
            QQiu = FunctionField(QQi, "r12")
            r12 = QQiu.gen()
            S = LaurentPolynomialRing(QQiu, ["zeta1", "zeta2"])
            zeta1, zeta2 = S.gens()
        R = PowerSeriesRing(S, ["r1", "r2"])
        r1, r2 = R.gens()
        theta = R(0)
        mu1 = char.mu1
        mu2 = char.mu2
        nu1 = char.nu1
        nu2 = char.nu2
        d1 = sqrt(prec + 1 - mu2)
        min_n1 = ceil((-mu1 - d1) / 2)
        max_n1 = floor((-mu1 + d1) / 2)
        for n1 in range(min_n1, max_n1 + 1):
            d2 = sqrt(prec + 1 - (2*n1 + mu1)**2)
            min_n2 = ceil((-mu2 - d2) / 2)
            max_n2 = floor((-mu2 + d2) / 2)
            for n2 in range(min_n2, max_n2 + 1):
                if const:
                    zeta_term = 1
                    coeff = int((-1)**(n1*nu1 + n2*nu2))
                else:
                    zeta_term = zeta1**(2*n1+mu1) * zeta2**(2*n2+mu2)
                    coeff = i**((2*n1+mu1)*nu1 + (2*n2+mu2)*nu2)
                r_term = r1**((2*n1+mu1)**2) * r12**((2*n1+mu1)*(2*n2+mu2)) * r2**((2*n2+mu2)**2)
                theta += coeff*zeta_term*r_term
        if const:
            factor = int((-1)**((mu1*nu1 + mu2*nu2) // 2))
            theta *= factor
            self.gens = r1, r12, r2
        else:
            self.gens = r1, r12, r2, zeta1, zeta2
        self.qexp = theta + O(r1**(prec+1))

def CheckThetaConstant(char, prec):
    theta = ThetaWithChar(char, prec)
    r1, r12, r2, zeta1, zeta2 = theta.variables()
    theta_const = ThetaWithChar(char, prec, const=True)
    check1 = (theta(r1,r12,r2,1,1) == theta_const)
    # print("check1=", check1)
    if char.is_odd():
        check2 = (theta_const == 0)
        # print("check2=", check2)
        check3 = (theta(r1,r12,r2,1,1) == 0)
        # print("check3=", check3)
        return (check1 and check2 and check3)
    return check1

def G(idx, prec):
    # These are the G_i(1) and G_i(2) (dividing G by -pi)
    char = ThetaCharacteristic.get_odd_chars()[idx-1] # indexing in the paper starts at 1
    theta = ThetaWithChar(char, prec)
    r1, r12, r2, zeta1, zeta2 = theta.variables()
    i = theta.base_ring().gen()
    # TODO: figure out if we would rather keep G1 and G2 as type qExpSiegel
    G1 = (zeta1*theta.derivative(zeta1))(r1,r12,r2,1,1) / i
    G2 = (zeta2*theta.derivative(zeta2))(r1,r12,r2,1,1) / i
    return [G1, G2]

def CheckG(i, prec):
    char = ThetaCharacteristic.get_odd_chars()[i-1] # indexing in the paper starts at 1
    S = FunctionField(QQ, "r12")
    r12 = S.gen()
    R = PowerSeriesRing(S, ["r1" ,"r2"])
    r1, r2 = R.gens()
    G1 = R(0)
    G2 = R(0)
    mu1 = char.mu1
    mu2 = char.mu2
    nu1 = char.nu1
    nu2 = char.nu2
    d1 = sqrt(prec + 1 - mu2)
    min_n1 = ceil((-mu1 - d1) / 2)
    max_n1 = floor((-mu1 + d1) / 2)
    for n1 in range(min_n1, max_n1 + 1):
        d2 = sqrt(prec + 1 - (2*n1 + mu1)**2)
        min_n2 = ceil((-mu2 - d2) / 2)
        max_n2 = floor((-mu2 + d2) / 2)
        for n2 in range(min_n2, max_n2 + 1):
            coeff1 = int((-1)**(n1*nu1 + n2*nu2) * (2*n1 + mu1))
            coeff2 = int((-1)**(n1*nu1 + n2*nu2) * (2*n2 + mu2))
            r_term = r1**((2*n1+mu1)**2) * r12**((2*n1+mu1)*(2*n2+mu2)) * r2**((2*n2+mu2)**2)
            G1 += coeff1*r_term
            G2 += coeff2*r_term
    G1 += O(r1**(prec+1))
    G2 += O(r1**(prec+1))
    return [G1, G2] == G(i, prec)

def get_chi5(prec):
    thetas = [ThetaWithChar(chi, prec, const=True) for chi in ThetaCharacteristic.get_even_chars()]
    return prod([th.qexp for th in thetas])/(-64)

def get_chi63(prec):
    Gs = [G(i,prec) for i in range(1,7)]
    R = Gs[0][0].parent()
    S = PolynomialRing(R, ["x", "y"])
    x,y = S.gens()
    return prod([g[0]*x+g[1]*y for g in Gs]) / 64

def change_r_to_q(qexp):
    # R = qexp.base_ring().base_ring().base_ring()
    S = qexp.base_ring().base_ring()
    R = QQ
    Ru = FunctionField(R, "u")
    u = Ru.gen()
    Ruq = PowerSeriesRing(Ru, ["q1", "q2"])
    q1, q2 = Ruq.gens()
    qexp_dict = qexp.dict()
    res = Ruq(0)
    for exp in qexp_dict.keys():
        new_exp = (exp[0] // 8, exp[1] // 8)
        coeff_dict = qexp_dict[exp].dict()
        coeff = [c for c in coeff_dict.values()][0]
        num_dict = coeff.numerator().dict()
        den_dict = coeff.denominator().dict()
        num = Ru(0)
        for num_exp in num_dict.keys():
            num += num_dict[num_exp]*u**(num_exp // 4)
        denom = Ru(0)
        for den_exp in den_dict.keys():
            denom += den_dict[den_exp]*u**(den_exp // 4)
        mon = num / denom
        res += mon * q1**new_exp[0] * q2**new_exp[1]
    return res

def change_r_to_q_cov(cov):
    cov_coeffs = cov.dict()
    res = 0
    for exp in cov_coeffs.keys():
        qexp = change_r_to_q(cov_coeffs[exp])
        R = PolynomialRing(qexp.parent(), ["x", "y"])
        x,y = R.gens()
        mon = qexp*x**exp[0]*y**exp[1]
        res = R(res) + mon
    return res

class Chi(SageObject):
    def __init__(self,k,j):
        # at the moment we only support Chi_6_minus_2
        assert (k == 6) and (j == -2)
        self.FJexp = None
        self.prec = 0
        self.fname = "chi6m2_fjexp.dat"
        file_exists = Path(self.fname).is_file()
        if (file_exists):
            self.ReadFJexpFromFile(self.fname)

    def GetFJexp(self, prec=0):
        if (self.FJexp is None) or (prec > self.prec):
            prec = max(prec, 2)
            self.FJexp = self._ComputeFJexp(prec)
            self.prec = prec
            self.WriteFJexpToFile(self.fname)
        # truncating to match required precision
        chi = self.FJexp
        q = chi.parent().base().gens()
        chi = sum([(chi.monomial_coefficient(m) + O(q[0]**prec))*m for m in chi.monomials()])
        return chi

    def _ComputeFJexp(self, prec):
        assert prec >= 2
        chi5 = get_chi5(4*prec)
        chi63 = get_chi63(4*prec)
        r1, r2 = chi5.parent().gens()
        r12 = chi5.base_ring().gen()
        lc = (r12**2 - r12**(-2))*r1**4*r2**4
        chi6m2_33_times_lc = ((chi5 / lc)**(-1) * chi63).dict() # (x^3*y^3)
        chi6m2_33_times_lc_mons = chi6m2_33_times_lc.keys()
        lc_exp = [k for k in lc.dict()][0]
        lc_mon = lc.dict()[lc_exp]
        R = chi63.parent()
        chi6m2 = R(0)
        r1, r2 = chi63.base_ring().gens()
        x, y = chi63.parent().gens()
        for exp in chi6m2_33_times_lc_mons:
            coeff = chi6m2_33_times_lc[exp]
            coeff_dict = coeff.dict()
            for k in coeff_dict.keys():
                chi6m2_coeff = (coeff_dict[k] / lc_mon ) * r1**(k[0]-lc_exp[0]) * r2**(k[1]-lc_exp[1])
                chi6m2 += chi6m2_coeff * x**(exp[0]) * y**(exp[1])
        chi = change_r_to_q_cov(chi6m2)
        q = chi.parent().base().gens()
        chi = sum([(chi.monomial_coefficient(m) + O(q[0]**prec))*m for m in chi.monomials()])
        return chi

    def WriteFJexpToFile(self, filename):
        f = open(filename, "w")
        chi = self.GetFJexp(self.prec)
        chi_dict = { k :  chi.dict()[k].dict() for k in chi.dict().keys()}
        f.write("(" + str(self.prec) + ",")
        f.write(str(chi_dict).replace('^', '**') + ")")
        f.close()

    def SetFJexp(self, fjexp):
        self.FJexp = fjexp
        self.prec = fjexp.prec

    def ReadFJexpFromFile(self, filename):
        f = open(filename)
        Ru = FunctionField(QQ, "u")
        u = Ru.gen()
        Ruq = PowerSeriesRing(Ru, ["q1", "q2"])
        q1, q2 = Ruq.gens()
        Ruqxy = PolynomialRing(Ruq, ["x", "y"])
        x,y = Ruqxy.gens()
        self.prec, chi_dict = eval(f.read())
        self.FJexp = Ruqxy(chi_dict) + O(q1**self.prec)
        f.close()

def rat_func_sub(f, u):
    num = f.numerator().subs(u)
    denom = f.denominator().subs(u)
    return num / denom

def rat_func_to_pow_ser(f):
    R = PowerSeriesRing(QQ, "u")
    return R(f.numerator())/R(f.denominator())



