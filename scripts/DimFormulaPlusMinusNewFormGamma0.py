from sage.rings.integer_ring import ZZ
from sage.modular.arithgroup.all import Gamma0
from sage.modular.dims import dimension_new_cusp_forms

"""
The following two procedures compute the dimension
of the plus and minus subspaces of the space of new
forms on Gamma_0(2). Here the plus and minus signs
correspond to the sign of the eigenvalues of the
Atkin-Lehner involution acting on the space of new
forms on Gamma_0(2).
The formulas are taken from Theorem 2 of

[1] Kimball Martin
    Refined dimensions of cusp forms, and equidistribution and bias of signs
    Journal of Number Theory
    188 (2018) 1–17

WARNING: In Theorem 2 of [1] the plus/minus signs correspond to
         w_f which is the sign in the functional equation of L(f,s)
         for f a new form on Gamma_0(2) so
         w_f=(-1)^{k/2} \\lambda_{W_2} for f \\in S_{k}(Gamma_0(2))^{new}
"""



def dimension_new_cusp_forms_plus_level_2(k):
    """
    Compute the dimension of the plus space of
    new cusp forms on Gamma_0(2)
    """
    k = ZZ(k)

    if k==0 or k==2:
        return ZZ(0)

    if (k % 8) == 0:
        return ZZ((1/2)*dimension_new_cusp_forms(Gamma0(2),k)+1/2)

    if (k % 8) == 2:
        return ZZ((1/2)*dimension_new_cusp_forms(Gamma0(2),k)-1/2)

    elif (k % 8) == 4 or (k % 8)== 6:
        return ZZ((1/2)*dimension_new_cusp_forms(Gamma0(2),k))


def dimension_new_cusp_forms_minus_level_2(k):
    """
    Compute the dimension of the minus space of
    new cusp forms on Gamma_0(2)
    """
    k = ZZ(k)

    if k==0 or k==2:
        return ZZ(0)

    if (k % 8) == 0:
        return ZZ((1/2)*dimension_new_cusp_forms(Gamma0(2),k)-1/2)

    if (k % 8) == 2:
        return ZZ((1/2)*dimension_new_cusp_forms(Gamma0(2),k)+1/2)

    elif (k % 8) == 4 or (k % 8)== 6:
        return ZZ((1/2)*dimension_new_cusp_forms(Gamma0(2),k))

