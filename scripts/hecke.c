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

int hecke_act_on_space(fmpq_mat_t mat, const fmpz_mpoly_struct* pols, slong dim,
    const acb_poly_struct* basic_covs,
    slong nb, slong q, int is_T1, const fmpz_mpoly_ctx_t ctx, slong prec)
{
    /* We just use the first dim matrices tau. */
    acb_mat_t s, t, hecke;
    acb_poly_t u, v;
    acb_t f;
    slong j, k, l;
    int res = 1;

    acb_mat_init(s, dim, dim);
    acb_mat_init(t, dim, dim);
    acb_mat_init(hecke, dim, dim);
    acb_poly_init(u);
    acb_poly_init(v);
    acb_init(f);

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

    res = acb_mat_inv(s, s, prec);
    acb_mat_mul(hecke, t, s, prec);
    if (res)
    {
        flint_printf("(hecke_act_on_space) found Hecke matrix:\n");
        acb_mat_printd(hecke, 5);
    }

    /* Round to integral matrix */
    for (j = 0; (j < dim) && res; j++)
    {
        for (k = 0; (k < dim) && res; k++)
        {
            res = acb_get_approx_fmpq(fmpq_mat_entry(mat, j, k),
                acb_mat_entry(hecke, j, k), prec);
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

    acb_mat_clear(s);
    acb_mat_clear(t);
    acb_mat_clear(hecke);
    acb_poly_clear(u);
    acb_poly_clear(v);
    acb_clear(f);
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
    arb_mat_init(x, 2, 2);
    arb_mat_init(y, 2, 2);
    arf_init(t);

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
        acb_theta_g2_basic_covariants_hecke(&basic_covs[26 * (nb + 1) * k], &tau[k], prec);
    }

    /* Get integral matrix for each space */
    for (k = 0; (k < nb_spaces) && res; k++)
    {
        flint_printf("\n(hecke_attempt) getting matrix on space number %wd of dimension %wd\n",
            k, dims[k]);
        res = hecke_act_on_space(&mats[k], pols[k], dims[k], basic_covs,
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
    arb_mat_clear(x);
    arb_mat_clear(y);
    arf_clear(t);
    return res;
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

    prec = 200;
    while (!done)
    {
        done = hecke_attempt(mats, pols, dims, nb_spaces, q, ctx, prec);
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
