from sage.rings.integer_ring import ZZ
from sage.rings.power_series_ring import PowerSeriesRing

from DimFormulaPlusMinusNewFormGamma0 import dimension_new_cusp_forms_plus_level_2, dimension_new_cusp_forms_minus_level_2

def dim_SV_sp4Z_even_weight_with_charac(k):
    """
    Compute the dimension of M_{0,k}(Sp(4,Z),eps) for
    k even
    """
    R = PowerSeriesRing(ZZ, "t", default_prec=k+1)
    t = R.gen()
    num = t**30
    denom = (1-t**4) * (1-t**6) * (1-t**10) * (1-t**12)
    f = num / denom
    k = ZZ(k)
    d = f.list()[k]
    return d

def dim_splitting_SV_even_weight_charac(k):
    """
    Compute the dimension of M_{0,k}(Sp(4,Z),eps),
                             S_{0,k}(Sp(4,Z),eps),
                             E_{0,k}(Sp(4,Z),eps),
                             KE_{0,k}(Sp(4,Z),eps),
                             SK_{0,k}(Sp(4,Z),eps),
                             S^{gen}_{0,k}(Sp(4,Z),eps)
    for k even.
    """
    k=ZZ(k)
    dtotal = dim_SV_sp4Z_even_weight_with_charac(k)
    deis = 0
    dklingeneis = 0
    dsaitokurokawa = 0
    dgenuine = dtotal
    dcusp = dsaitokurokawa+dgenuine
    dnoncusp = deis + dklingeneis
    L={}
    L['degree'] = 2
    L['family'] = 'S'
    L['level'] = 1
    L['weight'] = [k,0]
    L['char_orbit'] = 1
    L['total_dim'] = dtotal
    L['cusp_dim'] = dcusp
    L['eis_dim'] = dnoncusp
    L['eis_F_dim'] = deis
    L['eis_Q_dim'] = dklingeneis
    L['cusp_P_dim'] = dsaitokurokawa
    L['cusp_Y_dim'] = 0
    L['cusp_G_dim'] = dgenuine
    return L

def dim_SV_sp4Z_odd_weight_with_charac(k):
    """
    Compute the dimension of M_{0,k}(Sp(4,Z),eps) for
    k odd
    """
    R = PowerSeriesRing(ZZ, "t", default_prec=k+1)
    t = R.gen()
    num = t**5
    denom = (1-t**4) * (1-t**6) * (1-t**10) * (1-t**12)
    f = num / denom
    k = ZZ(k)
    d = f.list()[k]
    return d

def dim_splitting_SV_odd_weight_charac(k):
    """
    Idem dim_splitting_SV_even_weight_Charac but for k odd
    """
    k=ZZ(k)
    dtotal = dim_SV_sp4Z_odd_weight_with_charac(k)
    deis = 0
    dklingeneis = 0
    dsaitokurokawa = dimension_new_cusp_forms_plus_level_2(2*k-2)
    dgenuine = dtotal-dsaitokurokawa
    dcusp = dtotal
    dnoncusp = deis + dklingeneis
    L={}
    L['degree'] = 2
    L['family'] = 'S'
    L['level'] = 1
    L['weight'] = [k,0]
    L['char_orbit'] = 1
    L['total_dim'] = dtotal
    L['cusp_dim'] = dcusp
    L['eis_dim'] = dnoncusp
    L['eis_F_dim'] = deis
    L['eis_Q_dim'] = dklingeneis
    L['cusp_P_dim'] = dsaitokurokawa
    L['cusp_Y_dim'] = 0
    L['cusp_G_dim'] = dgenuine
    return L

def dim_splitting_SV_All_weight_charac(k):
    """
    Put everything together
    """
    k = ZZ(k)
    if k in [0, 1, 2]:
         return {
    'degree': 2,
    'family': 'S',
    'level': 1,
    'weight': [k, 0],
    'char_orbit' : 1,
    'total_dim': 0,
    'cusp_dim': 0,
    'eis_dim': 0,
    'eis_F_dim': 0,
    'eis_Q_dim': 0,
    'cusp_P_dim': 0,
    'cusp_Y_dim': 0,
    'cusp_G_dim': 0}


    if (k % 2) == 1:
        return dim_splitting_SV_odd_weight_charac(k)

    if (k % 2) == 0 and  k > 2:
        return dim_splitting_SV_even_weight_charac(k)



