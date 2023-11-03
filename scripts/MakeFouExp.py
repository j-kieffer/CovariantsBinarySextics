from BinarySexticsCovariants import BinarySexticsCovariants as BSC
from ThetaFourier import Chi

Co16 = BSC.GetCov("Co16")

Co20 = BSC.GetCov("Co20")
Co24 = BSC.GetCov("Co24")
Co28 = BSC.GetCov("Co28")

Co32 = BSC.GetCov("Co32")
Co36 = BSC.GetCov("Co36")
Co38 = BSC.GetCov("Co38")
Co312 = BSC.GetCov("Co312")


Co40 = BSC.GetCov("Co40")
Co44 = BSC.GetCov("Co44")
Co46 = BSC.GetCov("Co46")
Co410 = BSC.GetCov("Co410")

Co52 = BSC.GetCov("Co52")
Co54 = BSC.GetCov("Co54")
Co58 = BSC.GetCov("Co58")

Co60 = BSC.GetCov("Co60")
Co661 = BSC.GetCov("Co661")
Co662 = BSC.GetCov("Co662")

Co72 = BSC.GetCov("Co72")
Co74 = BSC.GetCov("Co74")

Co82 = BSC.GetCov("Co82")

Co94 = BSC.GetCov("Co94")

Co100 = BSC.GetCov("Co100")
Co102 = BSC.GetCov("Co102")

Co122 = BSC.GetCov("Co122")

Co150 = BSC.GetCov("Co150")

def MakeFE(f,prec):
    chi = Chi(6,-2)
    chi6m2 = chi.GetFJexp(prec)
    coeffs = chi6m2.coefficients()
    Lf = f.coefficients()
    lenf = len(Lf)
    Lc = [Lf[k](coeffs) for k in range(lenf)]
    return Lc
    
