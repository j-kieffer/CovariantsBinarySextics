from BinarySexticsCovariants import BinarySexticsCovariants as BSC
# from ThetaFourier import ThetaCharacteristic, ThetaWithChar, G, get_chi6m2
from ThetaFourier import get_chi6m2

def E4(prec):
    Co20 = BSC.GetCov("Co20")
    Co40 = BSC.GetCov("Co40")
    f = Co20**2 - 3*Co40
    chi6m2 = get_chi6m2(prec)
    coeffs = chi6m2.coefficients()
    # E4 is scalar-valued
    f = f.coefficients()[0]
    return f(coeffs) / (-20)
    
