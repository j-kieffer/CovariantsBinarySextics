
from BinarySexticsCovariants import *

#Testing that the basic covariants have content 1
R = PolynomialRing(QQ, 7, "a")
a = R.gens()
Rx.<x,y> = PolynomialRing(R, ["x","y"])
f = Rx(0)
for i in range(7):
    f += a[i] * x**(6-i) * y**i
basic = EvaluateBasicCovariants(f, leading_coefficient = False)

for j in range(26):
    assert basic[j].denominator() == 1
    gcdlist = [c.content() for c in basic[j].coefficients()]
    assert gcd(gcdlist) == 1

#Testing precomputed scalar bases
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

