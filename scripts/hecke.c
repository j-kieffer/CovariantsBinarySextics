/* Compilation:
gcc -I/home/jean/install/include/flint -I/home/jean/install/include hecke.c -L/home/jean/install/lib -lflint -lgmp -o hecke.exe

Usage:
./hecke.exe q filename_in filename_out

Each line in filename_in is a covariant encoded as a multivariate polynomial in
Co16, etc. with integral coefficients. Consecutive lines are elements in the
basis of one space. Bases for different spaces are separated by a newline.

A list of matrices is printed to filename_out. Each one encodes the Hecke
action (T(p) if q=p is prime, T_1(p^2) if q=p^2) on the input space. These are
matrices with either integral coefficients (maybe after multiplication by a
small cofactor). If a given matrix is proved to be integral by other means,
then the result is certified. */

#include <stdlib.h>
#include "fmpq.h"
#include "fmpq_mat.h"
#include "acb_theta.h"

void parse_integers(slong* nb_spaces, slong** dims, const char* filename_in)
{
    FILE* file_in;
    char* str;
    size_t nb, nb_prev;
    slong dim;

    file_in = fopen(filename_in, "r");
    if (file_in == NULL)
    {
        flint_printf("Error: could not read file %s\n", filename_in);
        flint_abort();
    }

    *nb_spaces = 0;
    dim = 0;
    nb_prev = 0;

    while (!feof(file_in))
    {
        str = NULL;
        nb = 0;
        getline(&str, &nb, file_in);
        str[strcspn(str, "\n")] = 0; /* remove final newline */
        nb = strcspn(str, "");
        /* flint_printf("(parse_integers) read line with nb = %wd, nb_prev = %wd\n", nb, nb_prev);
           flint_printf("line: %s\n", str); */
        flint_free(str);

        if (nb > 0 && nb_prev == 0)
        {
            (*nb_spaces)++;
            *dims = flint_realloc(*dims, (*nb_spaces + 1) * sizeof(slong));
            dim = 1;
        }
        else if (nb > 0)
        {
            dim++;
        }
        else if (nb == 0 && nb_prev > 0)
        {
            (*dims)[*nb_spaces - 1] = dim;
            dim = 0;
        }
        nb_prev = nb;
    }

    if (nb_prev > 0)
    {
        (*dims)[*nb_spaces - 1] = dim;
        dim = 0;
    }
    fclose(file_in);
}

void parse_covariants(fmpz_mpoly_struct** pols, slong nb_spaces, const slong* dims,
    const char* filename_in, const fmpz_mpoly_ctx_t ctx)
{
    char** vars;
    char* str;
    size_t nb;
    FILE* file_in;
    slong inds[26] = {16, 20, 24, 28, 32, 36, 38, 312, 40, 44, 46, 410, 52, 54, 58, 60, 661, 662, 72, 74, 82, 94, 100, 102, 122, 150};
    slong k, j;

    vars = flint_malloc(26 * sizeof(char*));
    for (k = 0; k < 26; k++)
    {
        vars[k] = flint_malloc(6 * sizeof(char));
        flint_sprintf(vars[k], "Co%wd", inds[k]);
    }

    file_in = fopen(filename_in, "r");
    if (file_in == NULL)
    {
        flint_printf("Error: could not read file %s\n", filename_in);
        flint_abort();
    }

    for (k = 0; k < nb_spaces; k++)
    {
        for (j = 0; j < dims[k]; j++)
        {
            str = NULL;
            nb = 0;
            getline(&str, &nb, file_in);
            str[strcspn(str, "\n")] = 0; /* remove final newline */
            fmpz_mpoly_set_str_pretty(&pols[k][j], str, (const char**) vars, ctx);
            flint_free(str);
            flint_printf("(parse_covariants) k = %wd, j = %wd, poly:\n", k, j);
            fmpz_mpoly_print_pretty(&pols[k][j], (const char**) vars, ctx);
            flint_printf("\n");
        }

        if (!feof(file_in))
        {
            str = NULL;
            nb = 0;
            getline(&str, &nb, file_in);
            str[strcspn(str, "\n")] = 0; /* remove final newline */
            nb = strcspn(str, "");
            if (nb != 0)
            {
                flint_printf("(parse_covariants) Error: no empty line after k = %wd, dim = %wd\n",
                    k, dims[k]);
            }
            flint_free(str);
        }
    }

    fclose(file_in);
    for (k = 0; k < 26; k++)
    {
        flint_free(vars[k]);
    }
    flint_free(vars);
}

void get_mf_weight(slong *k, slong *j, const fmpz_mpoly_t pol, const fmpz_mpoly_ctx_t ctx)
{
    slong e[26];
    slong klist[26] = {1,2,2,2,3,3,3,3,4,4,4,4,5,5,5,6,6,6,7,7,8,9,10,10,12,15};
    slong jlist[26] = {6,0,4,8,2,6,8,12,0,4,6,10,2,4,8,0,6,6,2,4,2,4,0,2,2,0};
    slong i;

    fmpz_mpoly_get_term_exp_si(e, pol, 0, ctx);
    *k = 0;
    *j = 0;
    for (i = 0; i < 26; i++)
    {
        *k += e[i] * klist[i];
        *j += e[i] * jlist[i];
    }
    *k -= (*j/2);

    flint_printf("(get_mf_weight) found k = %wd, j = %wd\n", *k, *j);
}

slong hecke_nb_cosets(slong ell)
{
  return (n_pow(ell,4) - 1) / (ell - 1);
}

slong hecke_nb_T1_cosets(slong ell)
{
    return ell + n_pow(ell, 2) + n_pow(ell, 3) + n_pow(ell, 4);
}

void hecke_coset(fmpz_mat_t m, slong k, slong p)
{
    slong a, b, c;
    slong i;

    if ((k < 0) || (k >= hecke_nb_cosets(p)))
    {
        flint_printf("(hecke_coset) Error: no matrix numbered %wd\n", k);
        fflush(stdout);
        flint_abort();
    }

    fmpz_mat_zero(m);

    if (k == 0)
    {
        /* Case 1 */
        fmpz_set_si(fmpz_mat_entry(m, 0, 0), p);
        fmpz_set_si(fmpz_mat_entry(m, 1, 1), p);
        fmpz_set_si(fmpz_mat_entry(m, 2, 2), 1);
        fmpz_set_si(fmpz_mat_entry(m, 3, 3), 1);
    }
    else if (k < 1 + n_pow(p, 3))
    {
        a = (k - 1) % p;
        b = ((k - 1) / p) % p;
        c = ((k - 1) / n_pow(p, 2)) % p;
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

void hecke_T1_coset(fmpz_mat_t m, slong k, slong p)
{
    slong a, b, c;
    slong i;

    if ((k < 0) || (k >= hecke_nb_T1_cosets(p)))
    {
        flint_printf("(hecke_T1_coset) Error: no matrix numbered %wd\n", k);
        fflush(stdout);
        flint_abort();
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

void hecke_slash(acb_poly_t im, const acb_mat_t star, const acb_poly_t val,
    slong k, slong j, slong prec)
{
    acb_poly_t x, y, res, t, u;
    acb_mat_t inv;
    acb_t a;
    slong i;

    acb_mat_init(inv, 2, 2);
    acb_poly_init(x);
    acb_poly_init(y);
    acb_poly_init(res);
    acb_poly_init(t);
    acb_poly_init(u);
    acb_init(a);

    acb_mat_inv(inv, star, prec);
    acb_poly_set_coeff_acb(x, 0, acb_mat_entry(inv, 1, 0));
    acb_poly_set_coeff_acb(x, 1, acb_mat_entry(inv, 0, 0));
    acb_poly_set_coeff_acb(y, 0, acb_mat_entry(inv, 1, 1));
    acb_poly_set_coeff_acb(y, 1, acb_mat_entry(inv, 0, 1));

    if (acb_poly_degree(val) > j)
    {
        flint_printf("(hecke_slash) Error: degree too high\n");
        flint_abort();
    }
    for (i = 0; i <= j; i++)
    {
        acb_poly_get_coeff_acb(a, val, i);
        acb_poly_pow_ui(t, x, i, prec);
        acb_poly_pow_ui(u, y, j - i, prec);
        acb_poly_mul(t, t, u, prec);
        acb_poly_scalar_mul(t, t, a, prec);
        acb_poly_add(res, res, t, prec);
    }

    acb_mat_det(a, inv, prec);
    acb_pow_ui(a, a, k, prec);
    acb_poly_scalar_mul(im, res, a, prec);

    acb_mat_clear(inv);
    acb_poly_clear(x);
    acb_poly_clear(y);
    acb_poly_clear(res);
    acb_poly_clear(t);
    acb_poly_clear(u);
    acb_clear(a);
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

static slong
cont_frac_max_nb_steps(const acb_t x, slong prec)
{
    return prec/2;
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

int acb_rationalize(fmpq_t c, fmpz_t den, const acb_t x,
    const fmpz_t probable_den, slong prec)
{
    acb_t z;
    arf_t current;
    mpz_t n, d;
    fmpz_t d_fmpz;
    int res = 1;
    int stop = 0;
    slong max_steps = cont_frac_max_nb_steps(x, prec);
    fmpz* r_vec;
    slong k;
    slong tol_exp;

    acb_init(z);
    arf_init(current);
    mpz_init(n);
    mpz_init(d);
    fmpz_init(d_fmpz);
    r_vec = _fmpz_vec_init(max_steps);

    acb_mul_fmpz(z, x, probable_den, prec);

    if (!arb_contains_zero(acb_imagref(z)))
    {
        flint_printf("(acb_rationalize) Error: contains no real number\n");
        acb_printd(x, 10); flint_printf("\n");
        fflush(stdout);
        flint_abort();
    }

    if (mag_cmp_2exp_si(arb_radref(acb_realref(z)), 0) > 0)
    {
        /* Too imprecise */
        res = 0;
    }

    if (res)
    {
        arf_set(current, arb_midref(acb_realref(z)));
        k = 0;
        while (!stop && (k < max_steps))
        {
            if (k < 2)
            {
                tol_exp = -prec/2;
            }
            else
            {
                tol_exp = -prec/8;
            }
            stop = cont_frac_step(&r_vec[k], current, current, prec, tol_exp);
            k++;
        }
        if (k == max_steps)
        {
            res = 0;
        }
        else
        {
            res = 1;
            cont_frac_get_fmpq(c, r_vec, k);
            fmpq_div_fmpz(c, c, probable_den);
            fmpq_get_mpz_frac(n, d, c);
            fmpz_set_mpz(d_fmpz, d);
            fmpz_lcm(den, d_fmpz, probable_den);
        }
    }

    acb_clear(z);
    arf_clear(current);
    mpz_clear(n);
    mpz_clear(d);
    fmpz_clear(d_fmpz);
    _fmpz_vec_clear(r_vec, max_steps);
    return res;
}

int hecke_act_on_space(fmpq_mat_t mat, const fmpz_mpoly_struct* pols, slong dim,
    const acb_poly_struct* basic_covs, const acb_mat_struct* stars,
    slong nb, slong q, int is_T1, const fmpz_mpoly_ctx_t ctx, slong prec)
{
    /* We just use the first dim matrices tau. */
    acb_mat_t s, t, hecke;
    acb_poly_t u, v;
    acb_t f;
    fmpz_t den;
    slong j, k, l;
    slong k0, j0;
    int res = 1;

    acb_mat_init(s, dim, dim);
    acb_mat_init(t, dim, dim);
    acb_mat_init(hecke, dim, dim);
    acb_poly_init(u);
    acb_poly_init(v);
    acb_init(f);
    fmpz_init(den);

    /* Get weight */
    get_mf_weight(&k0, &j0, &pols[0], ctx);

    /* Evaluate pols at base points */
    for (k = 0; k < dim; k++)
    {
        /* Put kth polynomial in kth row */
        for (j = 0; j < dim; j++)
        {
            acb_theta_g2_covariant(u, &pols[k], &basic_covs[26 * (nb + 1) * j], ctx, prec);
            acb_poly_get_coeff_acb(acb_mat_entry(s, k, j), u, 0);
        }
    }

    /* Construct image under Hecke */
    for (k = 0; k < dim; k++)
    {
        for (j = 0; j < dim; j++)
        {
            /* Get Hecke value for kth polynomial at tau_j */
            acb_poly_zero(u);
            for (l = 0; l < nb; l++)
            {
                acb_theta_g2_covariant(v, &pols[k],
                    &basic_covs[26 * (nb + 1) * j + 26 * (1 + l)], ctx, prec);
                hecke_slash(v, &stars[nb * j + l], v, k0, j0, prec);
                acb_poly_add(u, u, v, prec);
            }
            acb_set_si(f, q);
            if (is_T1)
            {
                acb_pow_ui(f, f, 4 * k0 + 2 * j0 - 6, prec);
            }
            else
            {
                acb_pow_ui(f, f, 2 * k0 + j0 - 3, prec);
            }
            acb_poly_scalar_mul(u, u, f, prec);
            acb_poly_get_coeff_acb(acb_mat_entry(t, k, j), u, 0);
        }
    }
    /* flint_printf("(hecke_act_on_space) source, target:\n");
       acb_mat_printd(s, 5);
       acb_mat_printd(t, 5); */

    acb_mat_inv(s, s, prec);
    acb_mat_mul(hecke, t, s, prec);
    flint_printf("(hecke_act_on_space) found Hecke matrix:\n");
    acb_mat_printd(hecke, 5);

    /* Round to integral matrix */
    fmpz_one(den);
    for (j = 0; (j < dim) && res; j++)
    {
        for (k = 0; (k < dim) && res; k++)
        {
            acb_mul_fmpz(f, acb_mat_entry(hecke, j, k), den, prec);
            res = acb_rationalize(fmpq_mat_entry(mat, j, k), den,
                acb_mat_entry(hecke, j, k), den, prec);
        }
    }
    if (res)
    {
        flint_printf("Success with denominator ");
        fmpz_print(den);
        flint_printf("\n");
    }
    else
    {
        flint_printf("Fail at precision %wd, increase precision\n", prec);
    }

    acb_mat_clear(s);
    acb_mat_clear(t);
    acb_mat_clear(hecke);
    acb_poly_clear(u);
    acb_poly_clear(v);
    acb_clear(f);
    fmpz_clear(den);
    return res;
}

int hecke_attempt(fmpq_mat_struct* mats, fmpz_mpoly_struct** pols,
    slong* dims, slong nb_spaces, slong q, const fmpz_mpoly_ctx_t ctx, slong prec)
{
    flint_printf("\n(hecke_attempt) attempt at precision %wd\n", prec);

    flint_rand_t state;
    slong max_dim;
    arb_mat_t x, y;
    acb_mat_struct* tau;
    acb_poly_struct* basic_covs;
    acb_mat_struct* stars;
    fmpz_mat_t mat;
    acb_mat_t w;
    arf_t t;
    slong nb, k, j;
    int is_T1 = 0;
    int res = 1;

    /* Get nb, max_dim */
    if (n_is_prime(q))
    {
        nb = hecke_nb_cosets(q);
    }
    else
    {
        if (!n_is_square(q))
        {
            flint_printf("Error: q must be prime or the square of a prime, got %wd\n", q);
            flint_abort();
        }
        q = n_sqrt(q);
        if (!n_is_prime(q))
        {
            flint_printf("Error: q must be prime or the square of a prime, got %wd\n", q * q);
            flint_abort();
        }
        nb = hecke_nb_T1_cosets(q);
        is_T1 = 1;
    }
    max_dim = 0;
    for (k = 0; k < nb_spaces; k++)
    {
        max_dim = FLINT_MAX(max_dim, dims[k]);
    }
    flint_printf("(hecke_attempt) max_dim = %wd\n", max_dim);

    /* Init */
    flint_randinit(state);
    tau = flint_malloc(max_dim * sizeof(acb_mat_struct));
    for (k = 0; k < max_dim; k++)
    {
        acb_mat_init(&tau[k], 2, 2);
    }
    basic_covs = flint_malloc(26 * max_dim * (nb + 1) * sizeof(acb_poly_struct));
    for (k = 0; k < 26 * max_dim * (nb + 1); k++)
    {
        acb_poly_init(&basic_covs[k]);
    }
    stars = flint_malloc(max_dim * nb * sizeof(acb_mat_struct));
    for (k = 0; k < max_dim * nb; k++)
    {
        acb_mat_init(&stars[k], 2, 2);
    }
    arb_mat_init(x, 2, 2);
    arb_mat_init(y, 2, 2);
    arf_init(t);
    fmpz_mat_init(mat, 4, 4);
    acb_mat_init(w, 2, 2);

    /* Choose base points */
    flint_printf("(hecke_attempt) generating %wd base points\n", max_dim);
    for (k = 0; k < max_dim; k++)
    {
        /* Imaginary part is [1 + t, 1/4; 1/4, 1 + t] with 0<=t<=1 */
        arf_one(t);
        arf_mul_2exp_si(t, t, -2);
        arb_set_arf(arb_mat_entry(y, 0, 1), t);
        arb_set_arf(arb_mat_entry(y, 1, 0), t);
        arf_one(t);
        arf_mul_2exp_si(t, t, -n_clog(nb_spaces, 2));
        arf_mul_si(t, t, k, ARF_RND_NEAR, prec);
        arf_add_si(t, t, 1, prec, ARF_RND_NEAR);
        arb_set_arf(arb_mat_entry(y, 0, 0), t);
        arb_set_arf(arb_mat_entry(y, 1, 1), t);
        /* Real part is uniformly random in [0,1] */
        arf_urandom(arb_midref(arb_mat_entry(x, 0, 0)), state, prec, ARF_RND_NEAR);
        arf_urandom(arb_midref(arb_mat_entry(x, 0, 1)), state, prec, ARF_RND_NEAR);
        arb_set(arb_mat_entry(x, 1, 0), arb_mat_entry(x, 0, 1));
        arf_urandom(arb_midref(arb_mat_entry(x, 1, 1)), state, prec, ARF_RND_NEAR);
        acb_mat_set_real_imag(&tau[k], x, y);
        /* acb_mat_printd(&tau[k], 5); */
    }

    /* Get basic covariants at base points */
    flint_printf("(hecke_attempt) computing basic covariants at %wd base points...\n",
        max_dim);
    for (k = 0; k < max_dim; k++)
    {
        acb_theta_g2_basic_covariants(&basic_covs[26 * (nb + 1) * k], &tau[k], prec);
    }

    /* Get stars and basic covariants for each Hecke matrix */
    flint_printf("(hecke_attempt) computing basic covariants at %wd Hecke images...\n",
        nb * max_dim);
    for (j = 0; j < nb; j++)
    {
        (is_T1 ? hecke_T1_coset(mat, j, q) : hecke_coset(mat, j, q));
        fmpz_mat_print_pretty(mat);
        flint_printf("\n");
        for (k = 0; k < max_dim; k++)
        {
            acb_siegel_cocycle(&stars[nb * k + j], mat, &tau[k], prec);
            acb_siegel_transform(w, mat, &tau[k], prec);
            acb_theta_g2_basic_covariants(&basic_covs[26 * (nb + 1) * k + 26 * (1 + j)],
                w, prec);
            /* acb_mat_printd(w, 5); */
        }
    }

    /* Get integral matrix for each space */
    for (k = 0; (k < nb_spaces) && res; k++)
    {
        flint_printf("\n(hecke_attempt) getting matrix on space number %wd of dimension %wd\n",
            k, dims[k]);
        res = hecke_act_on_space(&mats[k], pols[k], dims[k], basic_covs, stars,
            nb, q, is_T1, ctx, prec);
    }

    /* Clear and exit */
    flint_randclear(state);
    for (k = 0; k < max_dim; k++)
    {
        acb_mat_clear(&tau[k]);
    }
    flint_free(tau);
    for (k = 0; k < 26 * max_dim * (nb + 1); k++)
    {
        acb_poly_clear(&basic_covs[k]);
    }
    flint_free(basic_covs);
    for (k = 0; k < max_dim * nb; k++)
    {
        acb_mat_clear(&stars[k]);
    }
    flint_free(stars);
    arb_mat_clear(x);
    arb_mat_clear(y);
    arf_clear(t);
    fmpz_mat_clear(mat);
    acb_mat_clear(w);
    return res;
}

/* This is copied from flint/src/fmpz_mat/io.c */

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

int main(int argc, const char *argv[])
{
    slong q, nb_spaces;
    slong* dims = NULL;
    slong prec;
    fmpz_mpoly_struct** pols;
    fmpz_mpoly_ctx_t ctx;
    fmpq_mat_struct* mats;
    FILE* file_out;
    slong k, j;
    int done = 0;

    if (argc != 4)
    {
        flint_printf("Error: expected 3 arguments (p or p^2, filename_in, filename_out), got %wd\n", argc - 1);
        flint_abort();
    }

    flint_printf("(hecke) Call with q = %s, input: %s, output: %s\n", argv[1], argv[2], argv[3]);

    fmpz_mpoly_ctx_init(ctx, 26, ORD_LEX);

    q = strtol(argv[1], NULL, 10);
    parse_integers(&nb_spaces, &dims, argv[2]);
    pols = flint_malloc(nb_spaces * sizeof(fmpz_mpoly_struct*));
    mats = flint_malloc(nb_spaces * sizeof(fmpq_mat_struct));

    for (k = 0; k < nb_spaces; k++)
    {
        fmpq_mat_init(&mats[k], dims[k], dims[k]);
        pols[k] = flint_malloc(dims[k] * sizeof(fmpz_mpoly_struct));
        for (j = 0; j < dims[k]; j++)
        {
            fmpz_mpoly_init(&pols[k][j], ctx);
        }
    }

    parse_covariants(pols, nb_spaces, dims, argv[2], ctx);

    prec = 100;
    while (!done)
    {
        done = hecke_attempt(mats, pols, dims, nb_spaces, q, ctx, prec);
        prec += 100;
    }

    file_out = fopen(argv[3], "w");
    if (file_out == NULL)
    {
        flint_printf("Error: unable to write to file %s\n", argv[3]);
        flint_abort();
    }
    for (k = 0; k < nb_spaces; k++)
    {
        fmpq_mat_fprint_pretty(file_out, &mats[k]);
        fprintf(file_out, "\n\n");
    }
    fclose(file_out);

    for (k = 0; k < nb_spaces; k++)
    {
        for (j = 0; j < dims[k]; j++)
        {
            fmpz_mpoly_clear(&pols[k][j], ctx);
        }
        flint_free(pols[k]);
        fmpq_mat_clear(&mats[k]);
    }
    flint_free(pols);
    flint_free(mats);
    flint_free(dims);
    fmpz_mpoly_ctx_clear(ctx);

    flint_cleanup();
    return 0;
}
