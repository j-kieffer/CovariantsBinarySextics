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
#include <string.h>
#include "fmpz_vec.h"
#include "fmpz_mpoly.h"
#include "fmpq.h"
#include "fmpq_mat.h"
#include "acb_theta.h"
#include "profiler.h"

/* ---------- Read input ---------- */

static void
parse_integers(slong* nb_spaces, slong** dims, const char* filename_in)
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

static void
parse_covariants(fmpz_mpoly_vec_t pols, slong nb_spaces, const slong* dims,
    const slong* pols_indices, const char* filename_in, const fmpz_mpoly_ctx_t ctx)
{
    char** vars;
    char* str;
    size_t nb;
    FILE* file_in;
    slong inds[ACB_THETA_G2_COV_NB] = {16, 20, 24, 28, 32, 36, 38, 312, 40, 44, 46, 410, 52, 54, 58, 60, 661, 662, 72, 74, 82, 94, 100, 102, 122, 150};
    slong k, j;

    vars = flint_malloc(ACB_THETA_G2_COV_NB * sizeof(char*));
    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
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
            fmpz_mpoly_set_str_pretty(fmpz_mpoly_vec_entry(pols, pols_indices[k] + j),
                str, (const char**) vars, ctx);
            flint_free(str);
            flint_printf("(parse_covariants) k = %wd, j = %wd, poly:\n", k, j);
            fmpz_mpoly_print_pretty(fmpz_mpoly_vec_entry(pols, pols_indices[k] + j),
                (const char**) vars, ctx);
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
    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        flint_free(vars[k]);
    }
    flint_free(vars);
}

/* ---------- Recognize rational numbers ---------- */

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

static int
arf_get_approx_fmpq(fmpq_t y, const arf_t x, slong prec)
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

static int
arb_get_approx_fmpq(fmpq_t y, const arb_t x, slong prec)
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

static int
acb_get_approx_fmpq(fmpq_t y, const acb_t x, slong prec)
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

/* ---------- Print output ---------- */

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

#undef xxx_putc
#undef xxx_fmpq_print

/* ---------- Weights and cosets ---------- */

#define COV_K {1,2,2,2,3,3,3,3,4,4,4,4,5,5,5,6,6,6,7,7,8,9,10,10,12,15}
#define COV_J {6,0,4,8,2,6,8,12,0,4,6,10,2,4,8,0,6,6,2,4,2,4,0,2,2,0}

static void
covariant_weight(slong* k, slong* j, const fmpz_mpoly_t pol, const fmpz_mpoly_ctx_t ctx)
{
    slong e[ACB_THETA_G2_COV_NB];
    slong klist[] = COV_K;
    slong jlist[] = COV_J;
    slong i;

    *k = 0;
    *j = 0;
    if (fmpz_mpoly_total_degree_si(pol, ctx) == 0)
    {
        return;
    }

    fmpz_mpoly_get_term_exp_si(e, pol, 0, ctx);
    for (i = 0; i < ACB_THETA_G2_COV_NB; i++)
    {
        *k += e[i] * klist[i];
        *j += e[i] * jlist[i];
    }
    *k -= (*j/2);
}

static slong
hecke_nb(slong p)
{
    return 1 + p + n_pow(p, 2) + n_pow(p, 3);
}

static slong hecke_nb_T1(slong p)
{
    return p + n_pow(p, 2) + n_pow(p, 3) + n_pow(p, 4);
}

static void
hecke_coset(fmpz_mat_t m, slong k, slong p)
{
    slong a, b, c;
    slong i;

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

/* ---------- Evaluate multivariate polynomials ---------- */

/* static void */
/* acb_eval_fmpz_mpoly_vec_1(acb_ptr res, const fmpz_mpoly_vec_t pols, */
/*     slong nb, acb_srcptr val, const fmpz_mpoly_ctx_t ctx, slong prec) */
/* { */
/*     slong k; */
/*     slong dmax = -1; */
/*     slong* ds; */
/*     acb_ptr pow; */

/*     ds = flint_malloc(nb * sizeof(slong)); */
/*     for (k = 0; k < nb; k++) */
/*     { */
/*         ds[k] = fmpz_mpoly_degree_si(fmpz_mpoly_vec_entry(pols, k), 0, ctx); */
/*         dmax = FLINT_MAX(dmax, ds[k]); */
/*     } */

/*     pow = _acb_vec_init(dmax + 1); */

/*     _acb_vec_set_powers(pow, &val[0], dmax + 1, prec); */
/*     for (k = 0; k < nb; k++) */
/*     { */
/*         acb_set(&res[k], &pow[ds[k]]); */
/*     } */

/*     _acb_vec_clear(pow, dmax + 1); */
/*     flint_free(ds); */
/* } */

/* /\* Evaluate several polynomials on the same set of variables recursively *\/ */
/* static void */
/* acb_eval_fmpz_mpoly_vec_rec(acb_ptr res, const fmpz_mpoly_vec_t pols, slong nb, */
/*     acb_srcptr val, slong i, const fmpz_mpoly_ctx_t ctx, slong prec) */
/* { */
/*     fmpz_mpoly_univar_t A; */
/*     slong* lens; */
/*     slong** indices; */
/*     slong** degrees; */
/*     fmpz** coeffs; */
/*     slong max_diff = 0; */
/*     fmpz_mpoly_vec_t pols_rec; */
/*     fmpz_mpoly_t c, g; */
/*     acb_ptr rec, pow; */
/*     slong nb_rec = 0; */
/*     slong k, j, l; */

/*     if (i == 0) */
/*     { */
/*         acb_eval_fmpz_mpoly_vec_1(res, pols, nb, val, ctx, prec); */
/*         return; */
/*     } */
/*     if (nb == 0) */
/*     { */
/*         return; */
/*     } */

/*     fmpz_mpoly_univar_init(A, ctx); */
/*     lens = flint_malloc(nb * sizeof(slong)); */
/*     indices = flint_malloc(nb * sizeof(slong*)); */
/*     degrees = flint_malloc(nb * sizeof(slong*)); */
/*     coeffs = flint_malloc(nb * sizeof(fmpz*)); */
/*     fmpz_mpoly_vec_init(pols_rec, 0, ctx); */
/*     fmpz_mpoly_init(c, ctx); */
/*     fmpz_mpoly_init(g, ctx); */

/*     flint_printf("(eval_fmpz_mpoly) i = %wd, got %wd polynomials\n", i, nb); */

/*     for (k = 0; k < nb; k++) */
/*     { */
/*         fmpz_mpoly_to_univar(A, fmpz_mpoly_vec_entry(pols, k), i, ctx); */
/*         lens[k] = fmpz_mpoly_univar_length(A, ctx); */
/*         indices[k] = flint_malloc(lens[k] * sizeof(slong)); */
/*         degrees[k] = flint_malloc((lens[k] + 1) * sizeof(slong)); */
/*         coeffs[k] = _fmpz_vec_init(lens[k]); */
/*         degrees[k][0] = 0; */

/*         for (j = 0; j < lens[k]; j++) */
/*         { */
/*             fmpz_mpoly_univar_get_term_coeff(c, A, lens[k] - 1 - j, ctx); */
/*             degrees[k][j + 1] = fmpz_mpoly_univar_get_term_exp_si(A, lens[k] - 1 - j, ctx); */
/*             if (fmpz_mpoly_is_zero(c, ctx)) */
/*             { */
/*                 indices[k][j] = -1; */
/*             } */
/*             else */
/*             { */
/*                 fmpz_mpoly_primitive_part(g, c, ctx); */
/*                 fmpz_divexact(&coeffs[k][j], fmpz_mpoly_term_coeff_ref(c, 0, ctx), */
/*                     fmpz_mpoly_term_coeff_ref(g, 0, ctx)); */

/*                 l = fmpz_mpoly_vec_insert_unique(pols_rec, g, ctx); */
/*                 if (l == nb_rec) */
/*                 { */
/*                     nb_rec++; */
/*                 } */
/*                 indices[k][j] = l; */
/*             } */

/*             if (degrees[k][j + 1] < degrees[k][j]) */
/*             { */
/*                 flint_printf("error: decreasing degrees at j = %wd (%wd < %wd)\n", */
/*                     j, degrees[k][j + 1], degrees[k][j]); */
/*                 flint_abort(); */
/*             } */
/*             max_diff = FLINT_MAX(max_diff, degrees[k][j + 1] - degrees[k][j]); */
/*         } */
/*     } */

/*     rec = _acb_vec_init(nb_rec); */
/*     pow = _acb_vec_init(max_diff + 1); */

/*     acb_eval_fmpz_mpoly_vec_rec(rec, pols_rec, nb_rec, val, i - 1, ctx, prec); */
/*     _acb_vec_set_powers(pow, &val[i], max_diff + 1, prec); */

/*     for (k = 0; k < nb; k++) */
/*     { */
/*         acb_zero(&res[k]); */
/*         for (j = lens[k] - 1; j >= 0; j--) */
/*         { */
/*             acb_addmul_fmpz(&res[k], &rec[indices[k][j]], &coeffs[k][j], prec); */
/*             acb_mul(&res[k], &res[k], &pow[degrees[k][j + 1] - degrees[k][j]], prec); */
/*         } */
/*     } */

/*     fmpz_mpoly_univar_clear(A, ctx); */
/*     for (k = 0; k < nb; k++) */
/*     { */
/*         flint_free(indices[k]); */
/*         _fmpz_vec_clear(coeffs[k], lens[k]); */
/*         flint_free(degrees[k]); */
/*     } */
/*     flint_free(indices); */
/*     flint_free(degrees); */
/*     flint_free(coeffs); */
/*     flint_free(lens); */
/*     fmpz_mpoly_vec_clear(pols_rec, ctx); */
/*     fmpz_mpoly_clear(c, ctx); */
/*     fmpz_mpoly_clear(g, ctx); */
/*     _acb_vec_clear(rec, nb_rec); */
/*     _acb_vec_clear(pow, max_diff + 1); */
/* }

static void
acb_eval_fmpz_mpoly_vec(acb_ptr res, const fmpz_mpoly_vec_t pols, slong nb,
    acb_srcptr val, const fmpz_mpoly_ctx_t ctx, slong prec)
{
    acb_eval_fmpz_mpoly_vec_rec(res, pols, nb, val,
        fmpz_mpoly_ctx_nvars(ctx) - 1, ctx, prec);
        }*/

/* How many terms with variables i,...,25? */
static slong
add_chain_total_nb(slong i, slong maxk, slong maxj)
{
    slong klist[] = COV_K;
    slong jlist[] = COV_J;
    slong d = maxk / klist[i];
    slong res = 0;
    slong l;

    if (maxj < 0 || maxk < 0)
    {
        return 0;
    }
    else if (i == ACB_THETA_G2_COV_NB)
    {
        return 1;
    }

    if (jlist[i] > 0)
    {
        d = FLINT_MIN(d, maxj / jlist[i]);
    }
    for (l = 0; l <= d; l++)
    {
        res += add_chain_total_nb(i + 1, maxk - l * klist[i], maxj - l * jlist[i]);
    }

    return res;
}

/* return index of exponent in vector */
static slong
add_chain_index(const slong* exp, slong maxk, slong maxj)
{
    slong klist[] = COV_K;
    slong jlist[] = COV_J;
    slong i, l;
    slong res = 0;

    for (i = 0; i < ACB_THETA_G2_COV_NB; i++)
    {
        for (l = 0; l < exp[i]; l++)
        {
            /* lex order: add nb of vectors starting with l instead of exp[i] */
            res += add_chain_total_nb(i + 1, maxk - l * klist[i], maxj - l * jlist[i]);
        }
    }
    return res;
}

/* return exponent of given index in vector */
static slong
add_chain_exp(slong* exp, slong index, slong maxk, slong maxj)
{
    slong klist[] = COV_K;
    slong jlist[] = COV_J;
    slong k, j, i, l;
    slong r = 0;

    k = maxk;
    j = maxj;
    for (i = 0; i < ACB_THETA_G2_COV_NB; i++)
    {
        l = 0;
        while (r <= index)
        {
            r += add_chain_total_nb(i + 1, k, j);
            k -= klist[i];
            j -= jlist[i];
            l++;
        }
        k += klist[i];
        j += jlist[i];
        r -= add_chain_total_nb(i + 1, k, j);
        exp[i] = l - 1;
    }
}

/* set add_chain to pair of indices for the sum, or (-1, var) */
static slong
add_chain_all_terms(slong* add_chain, slong nb, slong maxk, slong maxj)
{
    slong* exp;
    slong* e1;
    slong* e2;
    slong l, d, i, l0;

    exp = flint_malloc(ACB_THETA_G2_COV_NB * sizeof(slong));
    e1 = flint_malloc(ACB_THETA_G2_COV_NB * sizeof(slong));
    e2 = flint_malloc(ACB_THETA_G2_COV_NB * sizeof(slong));

    for (i = 0; i < nb; i++)
    {
        add_chain_exp(exp, i, maxk, maxj);

        flint_printf("(add_chain_all_terms) i = %wd, exponent:\n", i);
        for (l = 0; l < ACB_THETA_G2_COV_NB; l++)
        {
            flint_printf("%wd ", exp[l]);
        }
        flint_printf("\n");

        d = 0;
        for (l = 0; l < ACB_THETA_G2_COV_NB; l++)
        {
            d += exp[l];
            if (exp[l] > 0)
            {
                l0 = l;
            }
        }
        if (d == 0)
        {
            add_chain[2 * i] = -1;
            add_chain[2 * i + 1] = -1;
        }
        else if (d == 1)
        {
            add_chain[2 * i] = -1;
            add_chain[2 * i + 1] = l0;
        }
        else /* split in half */
        {
            l0 = 0;
            for (l = 0; l < ACB_THETA_G2_COV_NB; l++)
            {
                if (l0 % 2 == 0)
                {
                    e1[l] = exp[l] / 2;
                    e2[l] = exp[l] - e1[l];
                }
                else
                {
                    e2[l] = exp[l] / 2;
                    e1[l] = exp[l] - e2[l];
                }
                if (exp[l] > 0)
                {
                    l0++;
                }
            }
            add_chain[2 * i] = add_chain_index(e1, maxk, maxj);
            add_chain[2 * i + 1] = add_chain_index(e2, maxk, maxj);
        }
    }

    flint_free(exp);
    flint_free(e1);
    flint_free(e2);
}

/* static void */
/* set_add_chains(slong** add_chain, slong* nb, slong** indices, fmpz** coeffs, */
/*     slong* nb_terms, const fmpz_mpoly_vec_t pols, slong nb_pols, const fmpz_mpoly_ctx_t ctx) */
/* { */
/*     slong maxk = 0; */
/*     slong maxj = 0; */
/*     slong k, j, i, l; */
/*     slong* exp; */

/*     exp = flint_malloc(ACB_THETA_G2_COV_NB * sizeof(slong)); */

/*     /\* set maxk, maxj *\/ */
/*     for (i = 0; i < nb_pols; i++) */
/*     { */
/*         covariant_weight(&k, &j, fmpz_mpoly_vec_entry(pols, i), ctx); */
/*         k += j/2; */
/*         maxk = FLINT_MAX(maxk, k); */
/*         maxj = FLINT_MAX(maxj, j); */
/*     } */

/*     /\* set addition chain for terms *\/ */
/*     *nb = add_chain_total_nb(0, maxk, maxj); */

/*     flint_printf("(set_add_chains) found maxk = %wd, maxj = %wd, %wd terms\n", */
/*        maxk, maxj, *nb); */
/*     *add_chain = flint_malloc(2 * (*nb) * sizeof(slong)); */
/*     add_chain_all_terms(*add_chain, *nb, maxk, maxj); */
    
/*     flint_printf("(set_add_chains) addchain:\n"); */
/*     for (l = 0; l < (*nb); l++) */
/*     { */
/*         flint_printf("(%wd, %wd), ", (*add_chain)[2 * l], (*add_chain)[2 * l + 1]); */
/*     } */

/*     /\* set addition chain for each polynomial *\/ */
/*     for (i = 0; i < nb_pols; i++) */
/*     { */
/*         nb_terms[i] = fmpz_mpoly_length(fmpz_mpoly_vec_entry(pols, i), ctx); */
/*         indices[i] = flint_malloc(nb_terms[i] * sizeof(slong)); */
/*         coeffs[i] = _fmpz_vec_init(nb_terms[i]); */
/*         for (l = 0; l < nb_terms[i]; l++) */
/*         { */
/*             fmpz_mpoly_get_term_coeff_fmpz(&coeffs[i][l], */
/*                 fmpz_mpoly_vec_entry(pols, i), l, ctx); */
/*             fmpz_mpoly_get_term_exp_si(exp, */
/*                 fmpz_mpoly_vec_entry(pols, i), l, ctx); */
/*             indices[i][l] = add_chain_index(exp, maxk, maxj); */
/*         } */
/*     } */

/*     /\* flint_printf("(set_add_chains) done. addchain:\n"); *\/ */
/*     /\* for (l = 0; l < (*nb); l++) *\/ */
/*     /\* { *\/ */
/*     /\*     flint_printf("(%wd, %wd), ", (*add_chain)[2 * l], (*add_chain)[2 * l + 1]); *\/ */
/*     /\* } *\/ */
/*     /\* flint_printf("\nindices and coeffs for first poly:\n"); *\/ */
/*     /\* for (l = 0; l < nb_terms[0]; l++) *\/ */
/*     /\* { *\/ */
/*     /\*     flint_printf("(%wd, ", indices[0][l]); *\/ */
/*     /\*     fmpz_print(&coeffs[0][l]); *\/ */
/*     /\*     flint_printf("), "); *\/ */
/*     /\* } *\/ */
/*     /\* flint_printf("\n"); *\/ */

/*     flint_free(exp); */
/* } */

/* static void */
/* acb_eval_fmpz_mpoly_vec(acb_t res, const fmpz_mpoly_vec_t pols, slong nb, acb_srcptr val, */
/*     const fmpz_mpoly_ctx_t ctx, slong prec) */
/* { */
/*     slong* add_chain; */
/*     slong n, max_nb_terms; */
/*     slong** indices; */
/*     fmpz** coeffs; */
/*     slong* nb_terms; */
/*     acb_ptr all_terms; */
/*     acb_ptr temp; */
/*     slong k, l; */

/*     indices = flint_malloc(nb * sizeof(slong*)); */
/*     coeffs = flint_malloc(nb * sizeof(fmpz*)); */
/*     nb_terms = flint_malloc(nb * sizeof(slong)); */

/*     /\* set addition chains *\/ */
/*     set_add_chains(&add_chain, &n, indices, coeffs, nb_terms, pols, nb, ctx); */

/*     /\* set all terms *\/ */
/*     all_terms = _acb_vec_init(n); */
/*     for (k = 0; k < n; k++) */
/*     { */
/*         /\* flint_printf("(set_all_terms) k = %wd, chain: (%wd, %wd)\n", k, */
/*            add_chain[2 * k], add_chain[2 * k + 1]); *\/ */
/*         if (add_chain[2 * k] == -1) */
/*         { */
/*             if (add_chain[2 * k + 1] == -1) */
/*             { */
/*                 acb_one(&all_terms[k]); */
/*             } */
/*             else */
/*             { */
/*                 acb_set(&all_terms[k], &val[add_chain[2 * k + 1]]); */
/*             } */
/*         } */
/*         else */
/*         { */
/*             acb_mul(&all_terms[k], &all_terms[add_chain[2 * k]], */
/*                 &all_terms[add_chain[2 * k + 1]], prec); */
/*         } */
/*     } */

/*     /\* set each poly *\/ */
/*     max_nb_terms = 0; */
/*     for (k = 0; k < nb; k++) */
/*     { */
/*         max_nb_terms = FLINT_MAX(max_nb_terms, nb_terms[k]); */
/*     } */
/*     temp = _acb_vec_init(max_nb_terms); */

/*     for (k = 0; k < nb; k++) */
/*     { */
/*         for (l = 0; l < nb_terms[k]; l++) */
/*         { */
/*             acb_set(&temp[l], &all_terms[indices[k][l]]); */
/*         } */
/*         acb_dot_fmpz(&res[k], NULL, 0, temp, 1, coeffs[k], 1, nb_terms[k], prec); */
/*     } */

/*     _acb_vec_clear(all_terms, n); */
/*     _acb_vec_clear(temp, max_nb_terms); */
/*     for (k = 0; k < nb; k++) */
/*     { */
/*         flint_free(indices[k]); */
/*         _fmpz_vec_clear(coeffs[k], nb_terms[k]); */
/*     } */
/*     flint_free(indices); */
/*     flint_free(coeffs); */
/*     flint_free(nb_terms); */
/*     flint_free(add_chain); */
/* } */

static int
exp_le(const slong* e1, const slong* e2)
{
    slong k;
    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        if (e1[k] > e2[k])
        {
            return 0;
        }
    }
    return 1;
}

static int
exp_lt_lex(const slong* e1, const slong* e2)
{
    slong k;
    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        if (e1[k] > e2[k])
        {
            return 0;
        }
        if (e1[k] < e2[k])
        {
            return 1;
        }
    }
    return 0;
}

static void
exp_sub(slong* res, const slong* e1, const slong* e2)
{
    slong k;
    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        res[k] = e1[k] - e2[k];
    }
}

static slong
exp_search(const slong* all_exps, slong bound, const slong* exp)
{
    slong low = 0;
    slong up = FLINT_MAX(0, bound - 1);
    slong mid;

    while (low < up)
    {
        mid = (up + low)/2;
        if (exp_lt_lex(all_exps + mid * ACB_THETA_G2_COV_NB, exp))
        {
            low = mid + 1;
        }
        else
        {
            up = mid;
        }
    }
    return low;
}

static int
exp_is_zero(const slong* exp)
{
    slong k;
    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        if (exp[k] != 0)
        {
            return 0;
        }
    }
    return 1;
}

static void
set_add_chains(slong** all_exps, slong** add_chain, slong* nb_all,
    slong** indices, fmpz** coeffs, slong* nb_terms, slong* max_degrees, slong* lmax,
    const fmpz_mpoly_vec_t pols, slong nb, const fmpz_mpoly_ctx_t ctx)
{
    fmpz_mpoly_t sum, m;
    fmpz_t c;
    slong* exp;
    slong k, j;
    int found;

    fmpz_mpoly_init(sum, ctx);
    fmpz_mpoly_init(m, ctx);
    fmpz_init(c);
    exp = flint_malloc(ACB_THETA_G2_COV_NB * sizeof(slong));

    /* Get nb_terms, lmax, max_degrees */
    *lmax = 0;
    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        max_degrees[k] = 0;
    }
    for (k = 0; k < nb; k++)
    {
        nb_terms[k] = fmpz_mpoly_length(fmpz_mpoly_vec_entry(pols, k), ctx);
        *lmax = FLINT_MAX(*lmax, nb_terms[k]);
        fmpz_mpoly_degrees_si(exp, fmpz_mpoly_vec_entry(pols, k), ctx);
        for (j = 0; j < ACB_THETA_G2_COV_NB; j++)
        {
            max_degrees[j] = FLINT_MAX(max_degrees[j], exp[j]);
        }
    }

    /* Make polynomial containing all monomials + powers of one variable */
    fmpz_one(c);
    for (k = 0; k < nb; k++)
    {
        for (j = 0; j < nb_terms[k]; j++)
        {
            fmpz_mpoly_get_term_monomial(m, fmpz_mpoly_vec_entry(pols, k), j, ctx);
            fmpz_mpoly_set_coeff_fmpz_monomial(sum, c, m, ctx);
        }
    }
    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        for (j = 1; j <= max_degrees[k]; j++)
        {
            fmpz_mpoly_gen(m, k, ctx);
            fmpz_mpoly_pow_ui(m, m, j, ctx);
            fmpz_mpoly_set_coeff_fmpz_monomial(sum, c, m, ctx);
        }
    }

    /* Get all exponents */
    *nb_all = fmpz_mpoly_length(sum, ctx);
    *all_exps = flint_malloc((*nb_all) * ACB_THETA_G2_COV_NB * sizeof(slong));
    *add_chain = flint_malloc(2 * (*nb_all) * sizeof(slong));
    for (j = 0; j < *nb_all; j++)
    {
        fmpz_mpoly_get_term_exp_si((*all_exps) + j * ACB_THETA_G2_COV_NB, sum,
            *nb_all - 1 - j, ctx); /* terms are in revlex order. */
    }

    /* Make addition chain with the exponents we have */
    for (k = 0; k < *nb_all; k++)
    {
        found = 0;
        for (j = 0; (j < k) && !found; j++)
        {
            if (exp_is_zero((*all_exps) + j * ACB_THETA_G2_COV_NB))
            {
                continue;
            }

            if (exp_le((*all_exps) + j * ACB_THETA_G2_COV_NB,
                    (*all_exps) + k * ACB_THETA_G2_COV_NB))
            {
                exp_sub(exp, (*all_exps) + k * ACB_THETA_G2_COV_NB,
                    (*all_exps) + j * ACB_THETA_G2_COV_NB);
                if (fmpz_mpoly_get_coeff_si_ui(sum, (ulong*) exp, ctx))
                {
                    found = 1;
                    (*add_chain)[2 * k] = j;
                    (*add_chain)[2 * k + 1] = exp_search(*all_exps, k, exp);
                }
            }
        }

        if (!found)
        {
            (*add_chain)[2 * k] = -1;
            (*add_chain)[2 * k + 1] = -1;
        }
    }

    /* Get indices, coefficients, max_degrees */
    *lmax = 0;
    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        max_degrees[k] = 0;
    }
    for (k = 0; k < nb; k++)
    {
        coeffs[k] = _fmpz_vec_init(nb_terms[k]);
        indices[k] = flint_malloc(2 * nb_terms[k] * sizeof(slong));

        for (j = 0; j < nb_terms[k]; j++)
        {
            fmpz_mpoly_get_term_coeff_fmpz(&coeffs[k][j], fmpz_mpoly_vec_entry(pols, k), j, ctx);
            fmpz_mpoly_get_term_exp_si(exp, fmpz_mpoly_vec_entry(pols, k), j, ctx);
            indices[k][j] = exp_search(*all_exps, *nb_all, exp);
        }

        *lmax = FLINT_MAX(*lmax, nb_terms[k]);
        fmpz_mpoly_degrees_si(exp, fmpz_mpoly_vec_entry(pols, k), ctx);
        for (j = 0; j < ACB_THETA_G2_COV_NB; j++)
        {
            max_degrees[j] = FLINT_MAX(max_degrees[j], exp[j]);
        }
    }

    fmpz_mpoly_clear(sum, ctx);
    fmpz_mpoly_clear(m, ctx);
    fmpz_clear(c);
    flint_free(exp);
}

static void
acb_eval_fmpz_mpoly_vec(acb_t res, const fmpz_mpoly_vec_t pols, slong nb, acb_srcptr val,
    const fmpz_mpoly_ctx_t ctx, slong prec)
{
    slong* all_exps;
    slong* add_chain;
    slong nb_all;
    slong** indices;
    fmpz** coeffs;
    slong* nb_terms;
    slong* max_degrees;
    acb_ptr terms, temp;
    acb_ptr* powers = flint_malloc(ACB_THETA_G2_COV_NB * sizeof(acb_ptr));
    slong lmax, k, j;

    indices = flint_malloc(nb * sizeof(slong*));
    coeffs = flint_malloc(nb * sizeof(fmpz*));
    nb_terms = flint_malloc(nb * sizeof(slong));
    max_degrees = flint_malloc(ACB_THETA_G2_COV_NB * sizeof(slong));

    /* Get addition chains */
    flint_printf("addition chains:\n");
    TIMEIT_ONCE_START;
    set_add_chains(&all_exps, &add_chain, &nb_all, indices, coeffs, nb_terms, max_degrees,
        &lmax, pols, nb, ctx);
    TIMEIT_ONCE_STOP;

    /* Get powers */
    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        powers[k] = _acb_vec_init(max_degrees[k] + 1);
        _acb_vec_set_powers(powers[k], &val[k], max_degrees[k] + 1, prec);
    }
    terms = _acb_vec_init(nb_all);
    temp = _acb_vec_init(lmax);

    /* Get all terms */
    flint_printf("all terms:\n");
    TIMEIT_START;
    for (k = 0; k < nb_all; k++)
    {
        if (add_chain[2 * k] == -1)
        {
            acb_one(&terms[k]);
            for (j = 0; j < ACB_THETA_G2_COV_NB; j++)
            {
                acb_mul(&terms[k], &terms[k],
                    &powers[j][all_exps[k * ACB_THETA_G2_COV_NB + j]], prec);
            }
        }
        else
        {
            acb_mul(&terms[k], &terms[add_chain[2 * k]], &terms[add_chain[2 * k + 1]], prec);
        }
    }
    TIMEIT_STOP;

    flint_printf("all dots:\n");
    TIMEIT_START;
    /* Get dots */
    for (k = 0; k < nb; k++)
    {
        for (j = 0; j < nb_terms[k]; j++)
        {
            acb_set(&temp[j], &terms[indices[k][j]]);
        }
        acb_dot_fmpz(&res[k], NULL, 0, temp, 1, coeffs[k], 1, nb_terms[k], prec);
    }
    TIMEIT_STOP;

    for (k = 0; k < nb; k++)
    {
        flint_free(indices[k]);
        _fmpz_vec_clear(coeffs[k], nb_terms[k]);
    }
    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        _acb_vec_clear(powers[k], max_degrees[k] + 1);
    }
    flint_free(all_exps);
    flint_free(add_chain);
    flint_free(indices);
    flint_free(coeffs);
    flint_free(nb_terms);
    flint_free(max_degrees);
    flint_free(powers);
    _acb_vec_clear(terms, nb_all);
    _acb_vec_clear(temp, lmax);
}

/* static void */
/* acb_eval_fmpz_mpoly_vec(acb_t res, const fmpz_mpoly_vec_t pols, slong nb, acb_srcptr val, */
/*     const fmpz_mpoly_ctx_t ctx, slong prec) */
/* { */
/*     slong n = fmpz_mpoly_ctx_nvars(ctx); */
/*     slong* degrees = flint_malloc(n * sizeof(slong)); */
/*     slong* max_degrees = flint_malloc(n * sizeof(slong)); */
/*     slong j, k, l, L, Lmax; */
/*     acb_ptr* powers = flint_malloc(n * sizeof(acb_ptr)); */
/*     fmpz* coeffs; */
/*     acb_ptr terms; */
/*     slong exp; */

/*     for (k = 0; k < n; k++) */
/*     { */
/*         max_degrees[k] = 0; */
/*     } */
/*     Lmax = 0; */
/*     for (l = 0; l < nb; l++) */
/*     { */
/*         fmpz_mpoly_degrees_si(degrees, fmpz_mpoly_vec_entry(pols, l), ctx); */
/*         for (k = 0; k < n; k++) */
/*         { */
/*             max_degrees[k] = FLINT_MAX(max_degrees[k], degrees[k]); */
/*         } */
/*         Lmax = FLINT_MAX(Lmax, fmpz_mpoly_length(fmpz_mpoly_vec_entry(pols, l), ctx)); */
/*     } */

/*     for (k = 0; k < n; k++) */
/*     { */
/*         powers[k] = _acb_vec_init(max_degrees[k] + 1); */
/*         _acb_vec_set_powers(powers[k], &val[k], max_degrees[k] + 1, prec); */
/*     } */
/*     coeffs = _fmpz_vec_init(Lmax); */
/*     terms = _acb_vec_init(Lmax); */

/*     for (l = 0; l < nb; l++) */
/*     { */
/*         L = fmpz_mpoly_length(fmpz_mpoly_vec_entry(pols, l), ctx); */
        
/*         flint_printf("%wd terms:\n", L); */
/*         TIMEIT_START; */
/*         for (j = 0; j < L; j++) */
/*         { */
/*             fmpz_mpoly_get_term_coeff_fmpz(&coeffs[j], fmpz_mpoly_vec_entry(pols, l), j, ctx); */
/*             acb_one(&terms[j]); */

/*             for (k = 0; k < n; k++) */
/*             { */
/*                 exp = fmpz_mpoly_get_term_var_exp_si(fmpz_mpoly_vec_entry(pols, l), j, k, ctx); */
/*                 acb_mul(&terms[j], &terms[j], &(powers[k][exp]), prec); */
/*             } */
/*         } */
/*         TIMEIT_STOP; */

/*         flint_printf("dot:\n"); */
/*         TIMEIT_START; */
/*         acb_dot_fmpz(&res[l], NULL, 0, terms, 1, coeffs, 1, L, prec); */
/*         TIMEIT_STOP; */
/*     } */

/*     for (k = 0; k < n; k++) */
/*     { */
/*         _acb_vec_clear(powers[k], max_degrees[k] + 1); */
/*     } */
/*     flint_free(degrees); */
/*     flint_free(max_degrees); */
/*     flint_free(powers); */
/*     _fmpz_vec_clear(coeffs, Lmax); */
/*     _acb_vec_clear(terms, Lmax); */
/* } */


/* /\* ---------- Numerical Hecke action ---------- *\/ */

/* Add term corresponding to k^th coset to all matrices */
static void
hecke_add_term(acb_mat_struct* hecke, const fmpz_mpoly_vec_t pols, slong nb_spaces,
    const slong* dims, slong* pols_indices, const acb_mat_struct* taus,
    slong max_dim, slong k, slong p,
    int is_T1, const fmpz_mpoly_ctx_t ctx, slong prec)
{
    fmpz_mat_t mat;
    acb_mat_t w, c, cinv;
    acb_poly_t r;
    acb_ptr basic;
    acb_ptr res;
    slong nb = pols_indices[nb_spaces];
    acb_t v;
    slong i, j, l;

    fmpz_mat_init(mat, 4, 4);
    acb_mat_init(w, 2, 2);
    acb_mat_init(c, 2, 2);
    acb_mat_init(cinv, 2, 2);
    acb_poly_init(r);
    acb_init(v);
    basic = _acb_vec_init(ACB_THETA_G2_COV_NB);
    res = _acb_vec_init(nb);

    (is_T1 ? hecke_T1_coset(mat, k, p) : hecke_coset(mat, k, p));
    for (j = 0; j < max_dim; j++)
    {
        flint_printf("theta:\n");
        TIMEIT_START;
        
        acb_siegel_transform_cocycle_inv(w, c, cinv, mat, &taus[j], prec);
        acb_theta_g2_sextic(r, w, prec);
        acb_theta_g2_detk_symj(r, cinv, r, -2, 6, prec);
        acb_theta_g2_covariants_lead(basic, r, prec);
        TIMEIT_STOP;

        acb_eval_fmpz_mpoly_vec(res, pols, nb, basic, ctx, prec);

        for (i = 0; i < nb_spaces; i++)
        {
            if (j < dims[i])
            {
                for (l = 0; l < dims[i]; l++)
                {
                    acb_add(acb_mat_entry(&hecke[i], l, j),
                        acb_mat_entry(&hecke[i], l, j), &res[pols_indices[i] + l], prec);
                }
            }
        }
    }

    fmpz_mat_clear(mat);
    acb_mat_clear(w);
    acb_mat_clear(c);
    acb_mat_clear(cinv);
    acb_poly_clear(r);
    acb_clear(v);
    _acb_vec_clear(basic, ACB_THETA_G2_COV_NB);
    _acb_vec_clear(res, nb);
}

static void
hecke_source(acb_mat_struct* source, const fmpz_mpoly_vec_t pols, slong nb_spaces,
    const slong* dims, const slong* pols_indices, const acb_mat_struct* taus,
    slong max_dim, const fmpz_mpoly_ctx_t ctx, slong prec)
{
    acb_poly_t r;
    acb_ptr basic;
    acb_ptr res;
    slong i, j, l;
    slong nb = pols_indices[nb_spaces];

    acb_poly_init(r);
    basic = _acb_vec_init(ACB_THETA_G2_COV_NB);
    res = _acb_vec_init(nb);

    for (j = 0; j < max_dim; j++)
    {
        acb_theta_g2_sextic(r, &taus[j], prec);
        acb_theta_g2_covariants_lead(basic, r, prec);
        acb_eval_fmpz_mpoly_vec(res, pols, nb, basic, ctx, prec);

        for (i = 0; i < nb_spaces; i++)
        {
            if (j < dims[i])
            {
                for (l = 0; l < dims[i]; l++)
                {
                    acb_set(acb_mat_entry(&source[i], l, j), &res[pols_indices[i] + l]);
                }
            }
        }
    }

    acb_poly_clear(r);
    _acb_vec_clear(basic, ACB_THETA_G2_COV_NB);
    _acb_vec_clear(res, nb);
}

static void
hecke_generate_base_points(acb_mat_struct* tau, slong max_dim, slong prec)
{
    flint_rand_t state;
    arb_mat_t x, y;
    arf_t t;
    slong k;

    flint_randinit(state);
    arf_init(t);
    arb_mat_init(x, 2, 2);
    arb_mat_init(y, 2, 2);

    for (k = 0; k < max_dim; k++)
    {
        /* Imaginary part is [1 + t, 1/4; 1/4, 1 + t] with 0<=t<=1 */
        arf_one(t);
        arf_mul_2exp_si(t, t, -2);
        arb_set_arf(arb_mat_entry(y, 0, 1), t);
        arb_set_arf(arb_mat_entry(y, 1, 0), t);
        arf_one(t);
        arf_mul_2exp_si(t, t, -n_clog(max_dim, 2));
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

    flint_randclear(state);
    arf_clear(t);
    arb_mat_clear(x);
    arb_mat_clear(y);
}

static int
hecke_attempt(fmpq_mat_struct* mats, const fmpz_mpoly_vec_t pols, slong nb_spaces,
    slong* dims, slong* pols_indices, slong max_dim, slong p, int is_T1,
    const fmpz_mpoly_ctx_t ctx, slong prec)
{
    acb_mat_struct* tau;
    acb_mat_struct* hecke;
    acb_mat_struct* source;
    acb_t f;
    slong k, j, l;
    slong k0, j0;
    slong nb = (is_T1 ? hecke_nb_T1(p) : hecke_nb(p));
    int res = 1;

    /* Init */
    tau = flint_malloc(max_dim * sizeof(acb_mat_struct));
    for (k = 0; k < max_dim; k++)
    {
        acb_mat_init(&tau[k], 2, 2);
    }
    acb_init(f);
    hecke = flint_malloc(nb_spaces * sizeof(acb_mat_struct));
    source = flint_malloc(nb_spaces * sizeof(acb_mat_struct));
    for (k = 0; k < nb_spaces; k++)
    {
        acb_mat_init(&hecke[k], dims[k], dims[k]);
        acb_mat_init(&source[k], dims[k], dims[k]);
    }

    flint_printf("\n(hecke_attempt) attempt at precision %wd\n", prec);
    hecke_generate_base_points(tau, max_dim, prec);

    flint_printf("(hecke_attempt) evaluating covariants at base points...\n");
    hecke_source(source, pols, nb_spaces, dims, pols_indices, tau, max_dim, ctx, prec);
    for (k = 0; (k < nb_spaces) && res; k++)
    {
        res = acb_mat_inv(&source[k], &source[k], prec);
    }

    flint_printf("(hecke_attempt) evaluating Hecke action...\n");
    for (k = 0; (k < nb) && res; k++)
    {
        if (k % 100 == 0)
        {
            flint_printf("%wd/%wd\n", k, nb);
        }
        hecke_add_term(hecke, pols, nb_spaces, dims, pols_indices, tau, max_dim,
            k, p, is_T1, ctx, prec);
    }

    /* Get rational matrix for each space */
    flint_printf("(hecke_attempt) recognizing matrices...\n");
    for (k = 0; (k < nb_spaces) && res; k++)
    {
        acb_mat_mul(&hecke[k], &hecke[k], &source[k], prec);
        covariant_weight(&k0, &j0, fmpz_mpoly_vec_entry(pols, pols_indices[k]), ctx);
        acb_set_si(f, p);
        if (is_T1)
        {
            acb_pow_si(f, f, 4 * k0 + 2 * j0 - 6, prec);
        }
        else
        {
            acb_pow_si(f, f, 2 * k0 + j0 - 3, prec);
        }
        acb_mat_scalar_mul_acb(&hecke[k], &hecke[k], f, prec);

        flint_printf("(hecke_attempt) found Hecke matrix on space number %wd:\n", k);
        acb_mat_printd(&hecke[k], 5);

        /* Round to integral matrix */
        for (j = 0; (j < dims[k]) && res; j++)
        {
            for (l = 0; (l < dims[k]) && res; l++)
            {
                res = acb_get_approx_fmpq(fmpq_mat_entry(&mats[k], j, l),
                    acb_mat_entry(&hecke[k], j, l), prec);
            }
        }

        if (res)
        {
            fmpq_mat_print(&mats[k]);
        }
    }

    if (res)
    {
        flint_printf("Success!\n");
    }
    else
    {
        flint_printf("Fail at precision %wd, increase precision\n", prec);
    }

    /* Clear and exit */
    for (k = 0; k < max_dim; k++)
    {
        acb_mat_clear(&tau[k]);
    }
    flint_free(tau);
    acb_clear(f);
    for (k = 0; k < nb_spaces; k++)
    {
        acb_mat_clear(&hecke[k]);
        acb_mat_clear(&source[k]);
    }
    flint_free(hecke);
    flint_free(source);
    return res;
}

/* ---------- Main ---------- */

int main(int argc, const char *argv[])
{
    slong q, nb_spaces, p, max_dim;
    int is_T1;
    slong* dims = NULL;
    slong prec;
    fmpz_mpoly_vec_t pols;
    slong* pols_indices;
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

    q = strtol(argv[1], NULL, 10);
    parse_integers(&nb_spaces, &dims, argv[2]);
    if (nb_spaces == 0)
    {
        flint_printf("Error: empty input\n");
        return 0;
    }

    fmpz_mpoly_ctx_init(ctx, ACB_THETA_G2_COV_NB, ORD_LEX);
    pols_indices = flint_malloc((nb_spaces + 1) * sizeof(slong));
    mats = flint_malloc(nb_spaces * sizeof(fmpq_mat_struct));
    pols_indices[0] = 0;

    for (k = 0; k < nb_spaces; k++)
    {
        fmpq_mat_init(&mats[k], dims[k], dims[k]);
        pols_indices[k + 1] = pols_indices[k] + dims[k];
    }
    fmpz_mpoly_vec_init(pols, pols_indices[nb_spaces], ctx);

    parse_covariants(pols, nb_spaces, dims, pols_indices, argv[2], ctx);

    /* Get p, is_T1, max_dim */
    if (n_is_prime(q))
    {
        p = q;
        is_T1 = 0;
    }
    else
    {
        if (!n_is_square(q))
        {
            flint_printf("Error: q must be prime or the square of a prime, got %wd\n", q);
            flint_abort();
        }
        p = n_sqrt(q);
        if (!n_is_prime(p))
        {
            flint_printf("Error: q must be prime or the square of a prime, got %wd\n", q * q);
            flint_abort();
        }
        is_T1 = 1;
    }
    max_dim = 0;
    for (k = 0; k < nb_spaces; k++)
    {
        max_dim = FLINT_MAX(max_dim, dims[k]);
    }
    flint_printf("(hecke) max_dim = %wd\n", max_dim);

    prec = 200;
    while (!done)
    {
        done = hecke_attempt(mats, pols, nb_spaces, dims, pols_indices,
            max_dim, p, is_T1, ctx, prec);
        prec *= 2;
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

    fmpz_mpoly_vec_clear(pols, ctx);
    flint_free(pols_indices);
    for (k = 0; k < nb_spaces; k++)
    {
        fmpq_mat_clear(&mats[k]);
    }
    flint_free(mats);
    flint_free(dims);
    fmpz_mpoly_ctx_clear(ctx);

    flint_cleanup();
    return 0;
}
