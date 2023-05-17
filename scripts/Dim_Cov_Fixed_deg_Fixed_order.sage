"""
   The function dimCovFixDegFixOrdN(a,b) for N=1, 2 or 3 returns 
   the dimension of C_{a,b}. The N refers to the formula used from 
   the notes (1.N+1).
   The second one is the slowest one, the first and the third are rather
   fast. I do not know which is the fastest 1 or 3, you can decide which 
   one is and then we will use this one, maybe the third one...
"""


def dimCovFixDegFixOrd1(a,b):
    PS.<t,s> = PowerSeriesRing(QQ,default_prec=a+b+1)
    denom = (t^2 + t + 1)*(t^4 + t^3 + t^2 + t + 1)*(t^2 + 1)*(t + 1)^3*(t - 1)^4*(s^2*t - 1)*(s^4*t - 1)*(s^6*t - 1)
    num0 = -t^8 - t^7 + t^5 + t^4 + t^3 - t - 1
    num2 = s^2*t*(t + 1)*(t^7 - t^4 - t^3 - t^2 + 1)
    num4 = s^4*t*(t^8 + t^7 - t^5 - t^4 - t^3 - t^2 + 1)
    num6 = -s^6*t^2*(t^8 - t^6 - t^5 - t^4 - t^3 + t + 1)
    num8 = -s^8*t^2*(t + 1)*(t^7 - t^5 - t^4 - t^3 + 1)
    num10 = s^10*t^3*(t^8 + t^7 - t^5 - t^4 - t^3 + t + 1)
    num = num0+num2+num4+num6+num8+num10
    f = num/denom
    g = f.polynomial()
    d = g.coefficient([a,b]) 
    return d


def dimCovFixDegFixOrd2(a,b):
    if (b % 2) == 1:
       return 0
    elif (b % 2) == 0:
       k = ZZ(a)
       n = ZZ(3*a-b/2)
       d1 =len(Partitions(n, max_length=k, max_part=6).list())
       d2 = len(Partitions(n-1, max_length=k, max_part=6).list())
       d =d1-d2
       return d

def dimCovFixDegFixOrd3(a,b):
    R.<q> = PolynomialRing(QQ)
    if (b % 2) == 1:
       return 0
    elif (b % 2) == 0:
       k = ZZ(a)
       n = ZZ(3*a-b/2)
       f = (1-q)*gaussian_binomial(6+k,k)
       d = f.list()[n]
       return d
