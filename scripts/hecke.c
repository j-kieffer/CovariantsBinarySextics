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
            /* flint_printf("(parse_covariants) k = %wd, j = %wd, poly:\n", k, j);
               fmpz_mpoly_print_pretty(fmpz_mpoly_vec_entry(pols, pols_indices[k] + j),
                (const char**) vars, ctx);
                flint_printf("\n");*/
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

/* ---------- Context for multivariate polynomial evaluation ---------- */

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

struct hecke_mpoly_ctx_struct
{
    slong* all_exps;
    slong* add_chain;
    slong nb_exps;

    slong** indices;
    fmpz** coeffs;
    slong* nb_terms;
    slong* max_degrees;
    slong* ks;
    slong* js;
    slong lmax;
    slong nb_pols;
};

typedef struct hecke_mpoly_ctx_struct hecke_mpoly_ctx_t[1];

#define hecke_mpoly_ctx_exp(ctx, k) ((ctx)->all_exps + k * ACB_THETA_G2_COV_NB)

static void
hecke_mpoly_ctx_init(hecke_mpoly_ctx_t ctx, const fmpz_mpoly_vec_t pols,
    slong nb, const fmpz_mpoly_ctx_t mctx)
{
    fmpz_mpoly_t sum, m;
    fmpz_t c;
    slong* exp;
    slong k, j;
    int found;

    ctx->indices = flint_malloc(nb * sizeof(slong*));
    ctx->coeffs = flint_malloc(nb * sizeof(fmpz*));
    ctx->nb_terms = flint_malloc(nb * sizeof(slong));
    ctx->max_degrees = flint_malloc(ACB_THETA_G2_COV_NB * sizeof(slong));
    ctx->ks = flint_malloc(nb * sizeof(slong));
    ctx->js = flint_malloc(nb * sizeof(slong));
    ctx->nb_pols = nb;

    fmpz_mpoly_init(sum, mctx);
    fmpz_mpoly_init(m, mctx);
    fmpz_init(c);
    exp = flint_malloc(ACB_THETA_G2_COV_NB * sizeof(slong));

    /* Get nb_terms, lmax, max_degrees, weights */
    ctx->lmax = 0;
    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        ctx->max_degrees[k] = 0;
    }
    for (k = 0; k < nb; k++)
    {
        ctx->nb_terms[k] = fmpz_mpoly_length(fmpz_mpoly_vec_entry(pols, k), mctx);
        ctx->lmax = FLINT_MAX(ctx->lmax, ctx->nb_terms[k]);
        fmpz_mpoly_degrees_si(exp, fmpz_mpoly_vec_entry(pols, k), mctx);
        for (j = 0; j < ACB_THETA_G2_COV_NB; j++)
        {
            ctx->max_degrees[j] = FLINT_MAX(ctx->max_degrees[j], exp[j]);
        }
        covariant_weight(&(ctx->ks[k]), &(ctx->js[k]), fmpz_mpoly_vec_entry(pols, k), mctx);
    }

    /* Make polynomial containing all monomials + powers of one variable */
    fmpz_one(c);
    for (k = 0; k < nb; k++)
    {
        for (j = 0; j < ctx->nb_terms[k]; j++)
        {
            fmpz_mpoly_get_term_monomial(m, fmpz_mpoly_vec_entry(pols, k), j, mctx);
            fmpz_mpoly_set_coeff_fmpz_monomial(sum, c, m, mctx);
        }
    }
    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        for (j = 1; j <= ctx->max_degrees[k]; j++)
        {
            fmpz_mpoly_gen(m, k, mctx);
            fmpz_mpoly_pow_ui(m, m, j, mctx);
            fmpz_mpoly_set_coeff_fmpz_monomial(sum, c, m, mctx);
        }
    }

    /* Get all exponents */
    ctx->nb_exps = fmpz_mpoly_length(sum, mctx);
    ctx->all_exps = flint_malloc((ctx->nb_exps) * ACB_THETA_G2_COV_NB * sizeof(slong));
    ctx->add_chain = flint_malloc(2 * (ctx->nb_exps) * sizeof(slong));
    for (j = 0; j < ctx->nb_exps; j++)
    {
        fmpz_mpoly_get_term_exp_si(hecke_mpoly_ctx_exp(ctx, j), sum,
            ctx->nb_exps - 1 - j, mctx); /* terms are in revlex order. */
    }

    /* Make addition chain with the exponents we have */
    for (k = 0; k < ctx->nb_exps; k++)
    {
        found = 0;
        for (j = 0; (j < k) && !found; j++)
        {
            if (exp_is_zero(hecke_mpoly_ctx_exp(ctx, j)))
            {
                continue;
            }

            if (exp_le(hecke_mpoly_ctx_exp(ctx, j), hecke_mpoly_ctx_exp(ctx, k)))
            {
                exp_sub(exp, hecke_mpoly_ctx_exp(ctx, k), hecke_mpoly_ctx_exp(ctx, j));

                if (fmpz_mpoly_get_coeff_si_ui(sum, (ulong*) exp, mctx))
                {
                    found = 1;
                    ctx->add_chain[2 * k] = j;
                    ctx->add_chain[2 * k + 1] = exp_search(ctx->all_exps, k, exp);
                }
            }
        }

        if (!found)
        {
            ctx->add_chain[2 * k] = -1;
            ctx->add_chain[2 * k + 1] = -1;
        }
    }

    /* Get indices and coefficients */
    for (k = 0; k < nb; k++)
    {
        ctx->coeffs[k] = _fmpz_vec_init(ctx->nb_terms[k]);
        ctx->indices[k] = flint_malloc(2 * ctx->nb_terms[k] * sizeof(slong));

        for (j = 0; j < ctx->nb_terms[k]; j++)
        {
            fmpz_mpoly_get_term_coeff_fmpz(&ctx->coeffs[k][j],
                fmpz_mpoly_vec_entry(pols, k), j, mctx);
            fmpz_mpoly_get_term_exp_si(exp, fmpz_mpoly_vec_entry(pols, k), j, mctx);
            ctx->indices[k][j] = exp_search(ctx->all_exps, ctx->nb_exps, exp);
        }
    }

    fmpz_mpoly_clear(sum, mctx);
    fmpz_mpoly_clear(m, mctx);
    fmpz_clear(c);
    flint_free(exp);
}

static void
hecke_mpoly_ctx_clear(hecke_mpoly_ctx_t ctx)
{
    slong k;

    flint_free(ctx->add_chain);
    flint_free(ctx->all_exps);
    for (k = 0; k < ctx->nb_pols; k++)
    {
        _fmpz_vec_clear(ctx->coeffs[k], ctx->nb_terms[k]);
        flint_free(ctx->indices[k]);
    }
    flint_free(ctx->coeffs);
    flint_free(ctx->indices);
    flint_free(ctx->nb_terms);
    flint_free(ctx->max_degrees);
    flint_free(ctx->ks);
    flint_free(ctx->js);
}

/* ---------- Numerical Hecke action ---------- */

static void
hecke_mpoly_eval(acb_ptr res, acb_srcptr val, const hecke_mpoly_ctx_t ctx, slong prec)
{
    acb_ptr* powers = flint_malloc(ACB_THETA_G2_COV_NB * sizeof(acb_ptr));
    acb_ptr terms, temp;
    slong k, j;

    /* Get powers */
    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        powers[k] = _acb_vec_init(ctx->max_degrees[k] + 1);
        _acb_vec_set_powers(powers[k], &val[k], ctx->max_degrees[k] + 1, prec);
    }
    terms = _acb_vec_init(ctx->nb_exps);
    temp = _acb_vec_init(ctx->lmax);

    /* Get all terms */
    for (k = 0; k < ctx->nb_exps; k++)
    {
        if (ctx->add_chain[2 * k] == -1)
        {
            acb_one(&terms[k]);
            for (j = 0; j < ACB_THETA_G2_COV_NB; j++)
            {
                acb_mul(&terms[k], &terms[k],
                    &powers[j][ctx->all_exps[k * ACB_THETA_G2_COV_NB + j]], prec);
            }
        }
        else
        {
            acb_mul(&terms[k], &terms[ctx->add_chain[2 * k]],
                &terms[ctx->add_chain[2 * k + 1]], prec);
        }
    }

    /* Get dots */
    for (k = 0; k < ctx->nb_pols; k++)
    {
        for (j = 0; j < ctx->nb_terms[k]; j++)
        {
            acb_set(&temp[j], &terms[ctx->indices[k][j]]);
        }
        acb_dot_fmpz(&res[k], NULL, 0, temp, 1, ctx->coeffs[k], 1, ctx->nb_terms[k], prec);
    }

    for (k = 0; k < ACB_THETA_G2_COV_NB; k++)
    {
        _acb_vec_clear(powers[k], ctx->max_degrees[k] + 1);
    }
    flint_free(powers);
    _acb_vec_clear(terms, ctx->nb_exps);
    _acb_vec_clear(temp, ctx->lmax);
}

/* Add term corresponding to k^th coset to all matrices */
static void
hecke_add_term(acb_mat_struct* hecke, slong nb_spaces,
    const slong* dims, slong* pols_indices, const acb_mat_struct* taus,
    slong max_dim, slong k, slong p,
    int is_T1, const hecke_mpoly_ctx_t ctx, slong prec)
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
        acb_siegel_transform_cocycle_inv(w, c, cinv, mat, &taus[j], prec);
        acb_theta_g2_sextic(r, w, prec);
        acb_theta_g2_detk_symj(r, cinv, r, -2, 6, prec);
        acb_theta_g2_covariants_lead(basic, r, prec);
        hecke_mpoly_eval(res, basic, ctx, prec);

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
hecke_source(acb_mat_struct* source, slong nb_spaces,
    const slong* dims, const slong* pols_indices, const acb_mat_struct* taus,
    slong max_dim, const hecke_mpoly_ctx_t ctx, slong prec)
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
        hecke_mpoly_eval(res, basic, ctx, prec);

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
hecke_attempt(fmpq_mat_struct* mats, slong nb_spaces,
    slong* dims, slong* pols_indices, slong max_dim, slong p, int is_T1,
    const hecke_mpoly_ctx_t ctx, slong prec)
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
    hecke_source(source, nb_spaces, dims, pols_indices, tau, max_dim, ctx, prec);
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
        hecke_add_term(hecke, nb_spaces, dims, pols_indices, tau, max_dim,
            k, p, is_T1, ctx, prec);
    }

    /* Get rational matrix for each space */
    flint_printf("(hecke_attempt) recognizing matrices...\n");
    for (k = 0; (k < nb_spaces) && res; k++)
    {
        acb_mat_mul(&hecke[k], &hecke[k], &source[k], prec);
        k0 = ctx->ks[pols_indices[k]];
        j0 = ctx->js[pols_indices[k]];
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
    hecke_mpoly_ctx_t hecke_ctx;
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

    flint_printf("(hecke) precomputing additions chains...\n");
    hecke_mpoly_ctx_init(hecke_ctx, pols, pols_indices[nb_spaces], ctx);

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
    flint_printf("(hecke) done; max_dim = %wd\n", max_dim);

    prec = 500;
    while (!done)
    {
        done = hecke_attempt(mats, nb_spaces, dims, pols_indices,
            max_dim, p, is_T1, hecke_ctx, prec);
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
    hecke_mpoly_ctx_clear(hecke_ctx);

    flint_cleanup();
    return 0;
}
