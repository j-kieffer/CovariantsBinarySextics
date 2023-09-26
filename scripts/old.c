

/* static char* g2_covariants_str[] = { */
/* #include "acb_theta/g2_basic_covariants.in" */
/* }; */

/* static void */
/* g2_basic_covariant_eval(acb_poly_t r, const fmpz_mpoly_t cov, */
/*     acb_srcptr chi, const fmpz_mpoly_ctx_t ctx, slong prec) */
/* { */
/*     slong d = fmpz_mpoly_degree_si(cov, 7, ctx); */
/*     acb_ptr val; */
/*     fmpz_mpoly_univar_t u; */
/*     fmpz_mpoly_t coef; */
/*     acb_t c; */
/*     slong k; */

/*     val = _acb_vec_init(9); */
/*     fmpz_mpoly_univar_init(u, ctx); */
/*     fmpz_mpoly_init(coef, ctx); */
/*     acb_init(c); */

/*     _acb_vec_set(val, chi, 7); */
/*     acb_one(&val[7]); */
/*     acb_one(&val[8]); */
/*     fmpz_mpoly_to_univar(u, cov, 8, ctx); */
/*     acb_poly_zero(r); */

/*     for (k = 0; k <= d; k++) */
/*     { */
/*         fmpz_mpoly_univar_get_term_coeff(coef, u, k, ctx); */
/*         acb_eval_fmpz_mpoly(c, coef, val, ctx, prec); */
/*         acb_poly_set_coeff_acb(r, k, c); */
/*     } */

/*     _acb_vec_clear(val, 9); */
/*     fmpz_mpoly_univar_clear(u, ctx); */
/*     fmpz_mpoly_clear(coef, ctx); */
/*     acb_clear(c); */
/* } */

/* void */
/* acb_theta_g2_basic_covariants_old(acb_poly_struct* cov, const acb_poly_t r, slong prec) */
/* { */
/*     slong nb = ACB_THETA_G2_BASIC_NB; */
/*     char* vars[9] = {"a0", "a1", "a2", "a3", "a4", "a5", "a6", "x", "y"}; */
/*     fmpz_mpoly_ctx_t ctx; */
/*     fmpz_mpoly_t pol; */
/*     acb_ptr chi; */
/*     slong k; */

/*     fmpz_mpoly_ctx_init(ctx, 9, ORD_LEX); */
/*     fmpz_mpoly_init(pol, ctx); */
/*     chi = _acb_vec_init(7); */

/*     for (k = 0; k <= 6; k++) */
/*     { */
/*         acb_poly_get_coeff_acb(&chi[k], r, 6 - k); */
/*     } */

/*     for (k = 0; k < nb; k++) */
/*     { */
/*         fmpz_mpoly_set_str_pretty(pol, g2_covariants_str[k], (const char**) vars, ctx); */
/*         g2_basic_covariant_eval(&cov[k], pol, chi, ctx, prec); */
/*     } */

/*     fmpz_mpoly_clear(pol, ctx); */
/*     fmpz_mpoly_ctx_clear(ctx); */
/*     _acb_vec_clear(chi, 7); */
/* } */



slong acb_theta_g2_hecke_nb(slong q)
{
    slong p;
    int is_T1;

    if (n_is_prime(q))
    {
        p = q;
        is_T1 = 0;
    }
    else
    {
        p = n_sqrt(q);
        is_T1 = 1;
        if (p * p != q || !n_is_prime(p))
        {
            return 0;
        }
    }

    if (is_T1)
    {
        return p + n_pow(p, 2) + n_pow(p, 3) + n_pow(p, 4);
    }
    else
    {
        return 1 + p + n_pow(p, 2) + n_pow(p, 3);
    }
}


static void
hecke_coset(fmpz_mat_t m, slong k, slong p)
{
    slong a, b, c;
    slong i;

    if ((k < 0) || (k >= acb_theta_g2_hecke_nb(p)))
    {
        return;
    }

    fmpz_mat_zero(m);

    if (k < n_pow(p, 3))
    {
        /* Case 1 */
        a = k % p;
        b = (k / p) % p;
        c = (k / n_pow(p, 2)) % p;
        for (i = 0; i < 2; i++)
        {
            fmpz_one(fmpz_mat_entry(m, i, i));
        }
        for (i = 2; i < 4; i++)
        {
            fmpz_set_si(fmpz_mat_entry(m, i, i), p);
        }
        fmpz_set_si(fmpz_mat_entry(m, 0, 2), a);
        fmpz_set_si(fmpz_mat_entry(m, 0, 3), b);
        fmpz_set_si(fmpz_mat_entry(m, 1, 2), b);
        fmpz_set_si(fmpz_mat_entry(m, 1, 3), c);
    }
    else if (k < 1 + n_pow(p, 3))
    {
        /* Case 2 */
        fmpz_set_si(fmpz_mat_entry(m, 0, 0), p);
        fmpz_set_si(fmpz_mat_entry(m, 1, 1), p);
        fmpz_set_si(fmpz_mat_entry(m, 2, 2), 1);
        fmpz_set_si(fmpz_mat_entry(m, 3, 3), 1);
    }
    else if (k < 1 + n_pow(p, 3) + p)
    {
        /* Case 3 */
        a = k - n_pow(p, 3) - 1;
        fmpz_set_si(fmpz_mat_entry(m, 0, 0), 1);
        fmpz_set_si(fmpz_mat_entry(m, 0, 2), a);
        fmpz_set_si(fmpz_mat_entry(m, 1, 1), p);
        fmpz_set_si(fmpz_mat_entry(m, 2, 2), p);
        fmpz_set_si(fmpz_mat_entry(m, 3, 3), 1);
    }
    else
    {
        /* Case 4 */
        a = (k - 1 - n_pow(p, 3) - p) % p;
        b = ((k - 1 - n_pow(p, 3) - p)/p) % p;
        fmpz_set_si(fmpz_mat_entry(m, 0, 0), p);
        fmpz_set_si(fmpz_mat_entry(m, 1, 0), -a);
        fmpz_set_si(fmpz_mat_entry(m, 1, 1), 1);
        fmpz_set_si(fmpz_mat_entry(m, 1, 3), b);
        fmpz_set_si(fmpz_mat_entry(m, 2, 2), 1);
        fmpz_set_si(fmpz_mat_entry(m, 2, 3), a);
        fmpz_set_si(fmpz_mat_entry(m, 3, 3), p);
    }
}

static void
hecke_T1_coset(fmpz_mat_t m, slong k, slong p)
{
    slong a, b, c;
    slong i;

    if ((k < 0) || (k >= acb_theta_g2_hecke_nb(p * p)))
    {
        return;
    }

    fmpz_mat_zero(m);

    if (k == 0)
    {
        /* Case 1 */
        fmpz_set_si(fmpz_mat_entry(m, 0, 0), p);
        fmpz_set_si(fmpz_mat_entry(m, 1, 1), n_pow(p, 2));
        fmpz_set_si(fmpz_mat_entry(m, 2, 2), p);
        fmpz_set_si(fmpz_mat_entry(m, 3, 3), 1);
    }
    else if (k < 1 + (n_pow(p, 2)-1) )
    {
        /* Case 2 */
        if (k < 1 + (p-1))
        {
            /* a is zero, b too, c is anything nonzero */
            a = 0;
            b = 0;
            c = k;
        }
        else
        {
            /* a is nonzero, b is anything, c is b^2/a */
            /* k-p is between 0 and p(p-1)-1 */
            a = (k-p) % (p-1);
            a += 1;
            b = (k-p) % p;
            c = (b*b) % p;
            c *= n_invmod(a, p);
            c = c % p;
        }
        for (i = 0; i < 4; i++) fmpz_set_si(fmpz_mat_entry(m, i, i), p);
        fmpz_set_si(fmpz_mat_entry(m, 0, 2), a);
        fmpz_set_si(fmpz_mat_entry(m, 0, 3), b);
        fmpz_set_si(fmpz_mat_entry(m, 1, 2), b);
        fmpz_set_si(fmpz_mat_entry(m, 1, 3), c);
    }
    else if (k < n_pow(p, 2) + p)
    {
        /* Case 3 */
        a = k - n_pow(p, 2);
        fmpz_set_si(fmpz_mat_entry(m, 0, 0), n_pow(p, 2));
        fmpz_set_si(fmpz_mat_entry(m, 1, 0), -a*p);
        fmpz_set_si(fmpz_mat_entry(m, 1, 1), p);
        fmpz_set_si(fmpz_mat_entry(m, 2, 2), 1);
        fmpz_set_si(fmpz_mat_entry(m, 2, 3), a);
        fmpz_set_si(fmpz_mat_entry(m, 3, 3), p);
    }
    else if (k < n_pow(p, 2) + p + n_pow(p, 3))
    {
        /* Case 4 */
        k = k - n_pow(p, 2) - p;
        b = k % p;
        a = k / p;
        fmpz_set_si(fmpz_mat_entry(m, 0, 0), 1);
        fmpz_set_si(fmpz_mat_entry(m, 0, 2), a);
        fmpz_set_si(fmpz_mat_entry(m, 0, 3), -b);
        fmpz_set_si(fmpz_mat_entry(m, 1, 1), p);
        fmpz_set_si(fmpz_mat_entry(m, 1, 2), -p*b);
        fmpz_set_si(fmpz_mat_entry(m, 2, 2), n_pow(p, 2));
        fmpz_set_si(fmpz_mat_entry(m, 3, 3), p);
    }
    else
    {
        /* Case 5 */
        k = k - n_pow(p, 3) - n_pow(p, 2) - p;
        a = k%p;
        k = k/p;
        b = k%p;
        c = k/p;
        fmpz_set_si(fmpz_mat_entry(m, 0, 0), p);
        fmpz_set_si(fmpz_mat_entry(m, 0, 3), b*p);
        fmpz_set_si(fmpz_mat_entry(m, 1, 0), -a);
        fmpz_set_si(fmpz_mat_entry(m, 1, 1), 1);
        fmpz_set_si(fmpz_mat_entry(m, 1, 2), b);
        fmpz_set_si(fmpz_mat_entry(m, 1, 3), a*b+c);
        fmpz_set_si(fmpz_mat_entry(m, 2, 2), p);
        fmpz_set_si(fmpz_mat_entry(m, 2, 3), a*p);
        fmpz_set_si(fmpz_mat_entry(m, 3, 3), n_pow(p, 2));
    }
}

static void
hecke_T1_covariants(acb_ptr res, const acb_mat_t tau, slong p, slong prec)
{
    slong nb = ACB_THETA_G2_BASIC_NB;
    fmpz_mat_t mat;
    acb_mat_t w, c, cinv;
    acb_poly_t r;
    slong k;

    fmpz_mat_init(mat, 4, 4);
    acb_mat_init(w, 2, 2);
    acb_mat_init(c, 2, 2);
    acb_mat_init(cinv, 2, 2);
    acb_poly_init(r);

    for (k = 0; k < acb_theta_g2_hecke_nb(p * p); k++)
    {
        hecke_T1_coset(mat, k, p);
        acb_siegel_transform_cocycle_inv(w, c, cinv, mat, tau, prec);
        acb_theta_g2_fundamental_covariant(r, w, prec);
        acb_theta_g2_detk_symj(r, cinv, r, -2, 6, prec);
        acb_theta_g2_basic_covariants_lead(res + nb * k, r, prec);
    }

    fmpz_mat_clear(mat);
    acb_mat_clear(w);
    acb_mat_clear(c);
    acb_mat_clear(cinv);
    acb_poly_clear(r);
}

static void
hecke_covariants(acb_ptr res, const acb_mat_t tau, slong p, slong prec)
{
    slong nb = ACB_THETA_G2_BASIC_NB;
    fmpz_mat_t mat;
    acb_mat_t w, c, cinv;
    acb_poly_t r;
    slong k;

    fmpz_mat_init(mat, 4, 4);
    acb_mat_init(w, 2, 2);
    acb_mat_init(c, 2, 2);
    acb_mat_init(cinv, 2, 2);
    acb_poly_init(r);

    for (k = 0; k < acb_theta_g2_hecke_nb(p); k++)
    {
        hecke_coset(mat, k, p);
        acb_siegel_transform_cocycle_inv(w, c, cinv, mat, tau, prec);
        acb_theta_g2_fundamental_covariant(r, w, prec);
        acb_theta_g2_detk_symj(r, cinv, r, -2, 6, prec);
        acb_theta_g2_basic_covariants_lead(res + nb * k, r, prec);
    }

    fmpz_mat_clear(mat);
    acb_mat_clear(w);
    acb_mat_clear(c);
    acb_mat_clear(cinv);
    acb_poly_clear(r);
}

void
acb_theta_g2_basic_covariants_hecke(acb_ptr res, const acb_mat_t tau, slong q, slong prec)
{
    slong nb = ACB_THETA_G2_BASIC_NB;
    slong p;
    acb_poly_t r;
    int is_T1;

    if (n_is_prime(q))
    {
        p = q;
        is_T1 = 0;
    }
    else
    {
        p = n_sqrt(q);
        is_T1 = 1;
        if (p * p != q || !n_is_prime(p))
        {
            return;
        }
    }

    acb_poly_init(r);

    acb_theta_g2_fundamental_covariant(r, tau, prec);
    acb_theta_g2_basic_covariants_lead(res, r, prec);
    if (is_T1)
    {
        hecke_T1_covariants(res + nb, tau, p, prec);
    }
    else
    {
        hecke_covariants(res + nb, tau, p, prec);
    }

    acb_poly_clear(r);
}


void acb_theta_g2_covariant_weight(slong* k, slong* j, const fmpz_mpoly_t pol,
    const fmpz_mpoly_ctx_t ctx)
{
    slong e[ACB_THETA_G2_BASIC_NB];
    slong klist[] = ACB_THETA_G2_BASIC_K;
    slong jlist[] = ACB_THETA_G2_BASIC_J;
    slong i;

    fmpz_mpoly_get_term_exp_si(e, pol, 0, ctx);
    *k = 0;
    *j = 0;
    for (i = 0; i < ACB_THETA_G2_BASIC_NB; i++)
    {
        *k += e[i] * klist[i];
        *j += e[i] * jlist[i];
    }
    *k -= (*j/2);
}


void acb_theta_g2_slash_basic_covariants(acb_poly_struct* res, const acb_mat_t c,
    const acb_poly_struct* cov, slong prec)
{
    slong klist[] = ACB_THETA_G2_BASIC_K;
    slong jlist[] = ACB_THETA_G2_BASIC_J;
    slong nb = ACB_THETA_G2_BASIC_NB;
    slong nb_j = ACB_THETA_G2_MAX_J/2 + 1;
    acb_t det;
    acb_ptr det_pow;
    acb_ptr inv_pow;
    acb_poly_t x, y;
    acb_poly_struct* pow_x;
    acb_poly_struct* pow_y;
    acb_poly_struct** products;
    slong i, j, k, e;

    /* Init everything */
    acb_init(det);
    det_pow = _acb_vec_init(ACB_THETA_G2_MAX_K + 1);
    inv_pow = _acb_vec_init(ACB_THETA_G2_NEG_EXP + 1);
    acb_poly_init(x);
    acb_poly_init(y);
    pow_x = flint_malloc((ACB_THETA_G2_MAX_J + 1) * sizeof(acb_poly_struct));
    pow_y = flint_malloc((ACB_THETA_G2_MAX_J + 1) * sizeof(acb_poly_struct));
    for (k = 0; k < ACB_THETA_G2_MAX_J + 1; k++)
    {
        acb_poly_init(&pow_x[k]);
        acb_poly_init(&pow_y[k]);
    }
    products = flint_malloc(nb_j * sizeof(acb_poly_struct*));
    for (k = 0; k < nb_j; k++)
    {
        products[k] = flint_malloc((2 * k + 1) * sizeof(acb_poly_struct));
        for (j = 0; j < 2 * k + 1; j++)
        {
            acb_poly_init(&products[k][j]);
        }
    }

    /* Precompute products and powers of det */
    acb_mat_det(det, c, prec);
    _acb_vec_set_powers(det_pow, det, ACB_THETA_G2_MAX_K + 1, prec);
    acb_inv(det, det, prec);
    _acb_vec_set_powers(inv_pow, det, ACB_THETA_G2_NEG_EXP + 1, prec);
    acb_poly_set_coeff_acb(x, 0, acb_mat_entry(c, 1, 0));
    acb_poly_set_coeff_acb(x, 1, acb_mat_entry(c, 0, 0));
    acb_poly_set_coeff_acb(y, 0, acb_mat_entry(c, 1, 1));
    acb_poly_set_coeff_acb(y, 1, acb_mat_entry(c, 0, 1));
    acb_poly_one(&pow_x[0]);
    acb_poly_one(&pow_y[0]);
    for (k = 1; k < ACB_THETA_G2_MAX_J + 1; k++)
    {
        acb_poly_mul(&pow_x[k], &pow_x[k - 1], x, prec);
        acb_poly_mul(&pow_y[k], &pow_y[k - 1], y, prec);
    }
    for (k = 0; k < nb_j; k++)
    {
        for (j = 0; j < 2 * k + 1; j++)
        {
            acb_poly_mul(&products[k][j], &pow_x[j], &pow_y[2 * k - j], prec);
        }
    }

    /* Make substitutions and scalar products */
    for (i = 0; i < nb; i++)
    {
        acb_theta_g2_subst_covariant(&res[i], products[jlist[i]/2], &cov[i], jlist[i], prec);
        e = klist[i] - jlist[i]/2;
        if (e >= 0)
        {
            acb_poly_scalar_mul(&res[i], &res[i], &det_pow[e], prec);
        }
        else
        {
            acb_poly_scalar_mul(&res[i], &res[i], &inv_pow[-e], prec);
        }
    }

    /* Clear */
    acb_clear(det);
    _acb_vec_clear(det_pow, ACB_THETA_G2_MAX_K + 1);
    _acb_vec_clear(inv_pow, ACB_THETA_G2_NEG_EXP + 1);
    acb_poly_clear(x);
    acb_poly_clear(y);
    for (k = 0; k < ACB_THETA_G2_MAX_J + 1; k++)
    {
        acb_poly_clear(&pow_x[k]);
        acb_poly_clear(&pow_y[k]);
    }
    flint_free(pow_x);
    flint_free(pow_y);
    for (k = 0; k < nb_j; k++)
    {
        for (j = 0; j < 2 * k + 1; j++)
        {
            acb_poly_clear(&products[k][j]);
        }
        flint_free(products[k]);
    }
    flint_free(products);
}


void acb_theta_g2_covariant(acb_poly_t r, const fmpz_mpoly_t pol,
    const acb_poly_struct* basic, const fmpz_mpoly_ctx_t ctx, slong prec)
{
    acb_poly_eval_fmpz_mpoly(r, pol, basic, ctx, prec);
}


int acb_get_approx_fmpq(fmpq_t y, const acb_t x, slong prec)
{
    int res = 0;
    mag_t im;

    mag_init(im);
    arb_get_mag(im, acb_imagref(x));

    if (mag_cmp_2exp_si(im, -prec / 8) < 0)
    {
        res = arb_get_approx_fmpq(y, acb_realref(x), prec);
    }

    mag_clear(im);
    return res;
}

void
acb_eval_fmpz_mpoly(acb_t res, const fmpz_mpoly_t pol, acb_srcptr val,
    const fmpz_mpoly_ctx_t ctx, slong prec)
{
    slong n = fmpz_mpoly_ctx_nvars(ctx);
    slong L = fmpz_mpoly_length(pol, ctx);
    slong* degrees = flint_malloc(n * sizeof(slong));
    slong j, k;
    acb_ptr* powers = flint_malloc(n * sizeof(acb_ptr));
    acb_t ev, temp;
    fmpz_t coeff;
    slong exp;

    fmpz_mpoly_degrees_si(degrees, pol, ctx);
    for (k = 0; k < n; k++)
    {
        powers[k] = _acb_vec_init(degrees[k] + 2);
        acb_one(&(powers[k][0]));
        for (j = 1; j <= degrees[k]; j++)
        {
            acb_mul(&(powers[k][j]), &(powers[k][j - 1]), &val[k], prec);
        }
    }
    acb_init(ev);
    acb_init(temp);
    fmpz_init(coeff);

    acb_zero(ev);
    for (j = 0; j < L; j++)
    {
        fmpz_mpoly_get_term_coeff_fmpz(coeff, pol, j, ctx);
        acb_set_fmpz(temp, coeff);
        for (k = 0; k < n; k++)
        {
            exp = fmpz_mpoly_get_term_var_exp_si(pol, j, k, ctx);
            acb_mul(temp, temp, &(powers[k][exp]), prec);
        }
        acb_add(ev, ev, temp, prec);
    }

    acb_set(res, ev);

    acb_clear(ev);
    acb_clear(temp);
    fmpz_clear(coeff);
    for (k = 0; k < n; k++)
    {
        _acb_vec_clear(powers[k], degrees[k]+2);
    }
    flint_free(degrees);
    flint_free(powers);
}

static acb_poly_struct*
_acb_poly_vec_init(slong n)
{
    slong k;
    acb_poly_struct* ptr = flint_malloc(n * sizeof(acb_poly_struct));
    for (k = 0; k < n; k++)
    {
        acb_poly_init(&ptr[k]);
    }
    return ptr;
}

static void
_acb_poly_vec_clear(acb_poly_struct* ptr, slong n)
{
    slong k;
    for (k = 0; k < n; k++)
    {
        acb_poly_clear(&ptr[k]);
    }
    flint_free(ptr);
}

void
acb_poly_eval_fmpz_mpoly(acb_poly_t res, const fmpz_mpoly_t pol,
    const acb_poly_struct* val, const fmpz_mpoly_ctx_t ctx, slong prec)
{
    slong n = fmpz_mpoly_ctx_nvars(ctx);
    slong L = fmpz_mpoly_length(pol, ctx);
    slong* degrees = flint_malloc(n * sizeof(slong));
    slong j, k;
    acb_poly_struct** powers = flint_malloc(n * sizeof(acb_struct*));
    acb_poly_t ev, temp;
    fmpz_poly_t c;
    fmpz_t coeff;
    slong exp;

    fmpz_mpoly_degrees_si(degrees, pol, ctx);
    for (k = 0; k < n; k++)
    {
        powers[k] = _acb_poly_vec_init(degrees[k] + 2);
        acb_poly_one(&(powers[k][0]));
        for (j = 1; j <= degrees[k]; j++)
        {
            acb_poly_mul(&(powers[k][j]), &(powers[k][j - 1]), &val[k], prec);
        }
    }
    acb_poly_init(ev);
    acb_poly_init(temp);
    fmpz_init(coeff);
    fmpz_poly_init(c);

    acb_poly_zero(ev);
    for (j = 0; j < L; j++)
    {
        fmpz_mpoly_get_term_coeff_fmpz(coeff, pol, j, ctx);
        fmpz_poly_set_fmpz(c, coeff);
        acb_poly_set_fmpz_poly(temp, c, prec);
        for (k = 0; k < n; k++)
        {
            exp = fmpz_mpoly_get_term_var_exp_si(pol, j, k, ctx);
            acb_poly_mul(temp, temp, &(powers[k][exp]), prec);
        }
        acb_poly_add(ev, ev, temp, prec);
    }

    acb_poly_set(res, ev);

    acb_poly_clear(ev);
    acb_poly_clear(temp);
    fmpz_clear(coeff);
    fmpz_poly_clear(c);
    for (k = 0; k < n; k++)
    {
        _acb_poly_vec_clear(powers[k], degrees[k]+2);
    }
    flint_free(degrees);
    flint_free(powers);
}


int arb_get_approx_fmpq(fmpq_t y, const arb_t x, slong prec)
{
    int res;
    mpz_t n, d;
    fmpz_t c;
    arb_t z;

    mpz_init(n);
    mpz_init(d);
    fmpz_init(c);
    arb_init(z);

    res = arf_get_approx_fmpq(y, arb_midref(x), prec);

    if (res)
    {
        fmpq_get_mpz_frac(n, d, y);
        fmpz_set_mpz(c, d);
        arb_mul_fmpz(z, x, c, prec);
        res = (mag_cmp_2exp_si(arb_radref(z), - prec/8) < 0);
    }

    mpz_clear(n);
    mpz_clear(d);
    fmpz_clear(c);
    arb_clear(z);
    return res;
}


/* This uses the formula dA = A Phi(A^{-1} dP A^{-T}) where A is
   lower-triangular, P = A A^T, d denotes some scalar derivative, and
   Phi_{i,j}(M) is M_{i,j} for i>j, 1/2 M_{i,i} for i=j, and 0 for i<j */

void arb_mat_spd_radius(arf_t r, const arb_mat_t A, slong prec)
{
    slong g = arb_mat_nrows(A);
    arb_mat_t cho, inv;
    mag_t b, binv;
    arf_t t;
    int res;
    slong k, j;

    arb_mat_init(cho, g, g);
    arb_mat_init(inv, g, g);
    mag_init(b);
    mag_init(binv);
    arf_init(t);

    res = arb_mat_cho(cho, A, prec);
    if (!res)
    {
        arf_nan(r);
    }
    else
    {
        /* Get accepted deformation on cho for infinity norm */
        arf_pos_inf(r);
        for (k = 0; k < g; k++)
        {
            arb_get_lbound_arf(t, arb_mat_entry(cho, k, k), prec);
            arf_min(r, r, t);
        }
        arf_mul_2exp_si(r, r, -1);

        /* Add error to cho */
        for (k = 0; k < g; k++)
        {
            for (j = 0; j <= k; j++)
            {
                arb_add_error_arf(arb_mat_entry(cho, k, j), r);
            }
        }

        /* Get induced norms */
        arb_mat_bound_inf_norm(b, cho);
        arb_mat_one(inv);
        arb_mat_solve_tril(inv, cho, inv, 0, prec);
        arb_mat_bound_inf_norm(binv, inv);

        /* Propagate bound */
        arf_set_mag(t, b);
        arf_div(r, r, t, prec, ARF_RND_FLOOR);
        arf_set_mag(t, binv);
        arf_div(r, r, t, prec, ARF_RND_FLOOR);
        arf_div(r, r, t, prec, ARF_RND_FLOOR);
    }

    arb_mat_clear(cho);
    arb_mat_clear(inv);
    mag_clear(b);
    mag_clear(binv);
    arf_clear(t);
}


static int
cont_frac_step(fmpz_t r, arf_t next, const arf_t current, slong prec, slong tol_exp)
{
    int res = 0;
    arf_get_fmpz(r, current, ARF_RND_FLOOR);
    arf_sub_fmpz(next, current, r, prec, ARF_RND_NEAR);
    if (arf_cmp_2exp_si(next, tol_exp) < 0)
    {
        res = 1;
    }
    else
    {
        arf_ui_div(next, 1, next, prec, ARF_RND_NEAR);
    }
    return res;
}

static void
cont_frac_get_fmpq(fmpq_t c, fmpz* r_vec, slong nb_steps)
{
    slong k;
    fmpq_zero(c);
    fmpq_add_fmpz(c, c, &r_vec[nb_steps-1]);
    for (k = nb_steps-2; k >= 0; k--)
    {
        fmpq_inv(c, c);
        fmpq_add_fmpz(c, c, &r_vec[k]);
    }
}

int arf_get_approx_fmpq(fmpq_t y, const arf_t x, slong prec)
{
    arf_t z;
    int res = 1;
    int stop = 0;
    slong max_steps = prec / 2;
    fmpz* r_vec;
    slong k;

    arf_init(z);
    r_vec = _fmpz_vec_init(max_steps);

    arf_set(z, x);
    k = 0;
    for (k = 0; (k < max_steps) && !stop; k++)
    {
        stop = cont_frac_step(&r_vec[k], z, z, prec, -prec / 8);
    }

    if (k == max_steps)
    {
        res = 0;
    }
    else
    {
        res = 1;
        cont_frac_get_fmpq(y, r_vec, k);
    }

    arf_clear(z);
    _fmpz_vec_clear(r_vec, max_steps);
    return res;
}



/* This is copied from flint/src/fmpz_mat/io.c */

#ifdef FLINT_HAVE_FILE

#define xxx_putc(c)        \
do {                       \
    z = fputc((c), file);  \
    if (z <= 0)            \
        return z;          \
} while (0)

#define xxx_fmpq_print(f)        \
do {                             \
    z = fmpq_fprint(file, (f));  \
    if (z <= 0)                  \
        return z;                \
} while(0)

int fmpq_mat_fprint_pretty(FILE * file, const fmpq_mat_t mat)
{
    int z;
    slong i, j;
    slong r = mat->r;
    slong c = mat->c;

    xxx_putc('[');
    for (i = 0; i < r; i++)
    {
        xxx_putc('[');
        for (j = 0; j < c; j++)
        {
            xxx_fmpq_print(mat->rows[i] + j);
            if (j != c - 1)
                xxx_putc(' ');
        }
        xxx_putc(']');
        xxx_putc('\n');
    }
    xxx_putc(']');

    return z;
}

#undef xxx_putc
#undef xxx_fmpq_print

#endif
