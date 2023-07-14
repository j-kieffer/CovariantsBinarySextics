import sage
from sage.all import GF, ZZ, QQ, prod, PolynomialRing
from sage.all import FunctionField
from sage.rings.polynomial.laurent_polynomial_ring import LaurentPolynomialRing
from sage.rings.power_series_ring import PowerSeriesRing
from sage.matrix.matrix_space import MatrixSpace
from sage.misc.functional import sqrt
from sage.functions.other import ceil, floor
from sage.rings.big_oh import O
from sage.rings.number_field.number_field import QuadraticField

class ThetaCharacteristic(object):

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

class qExpSiegel(object):
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
    from ThetaFourier import ThetaCharacteristic, ThetaWithChar, G
    Gs = [G(i,prec) for i in range(1,7)]
    R = Gs[0][0].parent()
    S = PolynomialRing(R, ["x", "y"])
    x,y = S.gens()
    return prod([g[0]*x+g[1]*y for g in Gs]) / 64

def get_chi6m2(prec):
    chi5 = get_chi5(prec)
    chi63 = get_chi63(prec)
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
        chi6m2_coeff = coeff.parent()(0)
        for k in coeff_dict.keys():
            chi6m2_coeff += (coeff_dict[k] / lc_mon ) * r1**(k[0]-lc_exp[0]) * r2**(k[1]-lc_exp[1])
        chi6m2 += chi6m2_coeff * x**(exp[0]) * y**(exp[1])
    return chi6m2
            
