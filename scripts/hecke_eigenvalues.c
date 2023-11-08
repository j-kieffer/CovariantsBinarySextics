/* Compilation:
gcc -I/home/jean/install/include/flint -I/home/jean/install/include hecke_eigenvalues.c -L/home/jean/install/lib -lflint -lgmp -o hecke_eigenvalues.exe

Usage:
./hecke_eigenvalues.exe q filename_in filename_out

Each block of lines in filename_in encodes a Hecke eigenform defined over a
number field. Blocks are separated by a newline. The first line of each block
is a polynomial in x defining the number field (of degree d say). The next d
lines are the coefficients of the Hecke eigenform in the basis 1,...,x^(d-1),
encoded as multivariate polynomials in Co16, etc. with integral coefficients.

A list of eigenvalues is printed to filename_out. Each eigenvalue is an integer
y in the associated number field, and is represented as the list of integers
Tr(y), Tr(xy), ..., Tr(x^(d-1) y). The result is always certified assuming that
the input is indeed an eigenform. */

#include "fmpz_poly.h"
#include "arb_fmpz_poly.h"
#include "hecke.c"

/* ---------- Read input ---------- */

static void
parse_covariants(fmpz_mpoly_vec_t pols, fmpz_poly_struct* fields, slong nb_spaces,
    const slong* dims, const slong* pols_indices, const char* filename_in,
    const fmpz_mpoly_ctx_t ctx)
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
        /* Get univariate polynomial */
        str = NULL;
        nb = 0;
        getline(&str, &nb, file_in);
        str[strcspn(str, "\n")] = 0; /* remove final newline */
        fmpz_poly_set_str(&fields[k], "x");
        flint_free(str);

        /* Get covariants */
        for (j = 0; j < dims[k]; j++)
        {
            str = NULL;
            nb = 0;
            getline(&str, &nb, file_in);
            str[strcspn(str, "\n")] = 0; /* remove final newline */
            fmpz_mpoly_set_str_pretty(fmpz_mpoly_vec_entry(pols, pols_indices[k] + j),
                str, (const char**) vars, ctx);
            flint_free(str);
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

/* ---------- Numerical Hecke action ---------- */

/* Add term corresponding to k^th coset to all matrices */
static void
hecke_add_term(acb_ptr hecke, slong len, const acb_mat_t tau,
    slong k, slong p, int is_T1, const hecke_mpoly_ctx_t ctx, slong prec)
{
    fmpz_mat_t mat;
    acb_mat_t w, c, cinv;
    acb_poly_t r;
    acb_ptr basic;
    acb_ptr res;
    acb_t v;

    fmpz_mat_init(mat, 4, 4);
    acb_mat_init(w, 2, 2);
    acb_mat_init(c, 2, 2);
    acb_mat_init(cinv, 2, 2);
    acb_poly_init(r);
    acb_init(v);
    basic = _acb_vec_init(ACB_THETA_G2_COV_NB);
    res = _acb_vec_init(len);

    (is_T1 ? hecke_T1_coset(mat, k, p) : hecke_coset(mat, k, p));
    acb_siegel_transform_cocycle_inv(w, c, cinv, mat, tau, prec);
    acb_theta_g2_sextic(r, w, prec);
    acb_theta_g2_detk_symj(r, cinv, r, -2, 6, prec);
    acb_theta_g2_covariants_lead(basic, r, prec);
    hecke_mpoly_eval(res, basic, ctx, prec);
    _acb_vec_add(hecke, hecke, res, len, prec);

    fmpz_mat_clear(mat);
    acb_mat_clear(w);
    acb_mat_clear(c);
    acb_mat_clear(cinv);
    acb_poly_clear(r);
    acb_clear(v);
    _acb_vec_clear(basic, ACB_THETA_G2_COV_NB);
    _acb_vec_clear(res, len);
}

static void
hecke_source(acb_ptr source, const acb_mat_t tau, const hecke_mpoly_ctx_t ctx, slong prec)
{
    acb_poly_t r;
    acb_ptr basic;

    acb_poly_init(r);
    basic = _acb_vec_init(ACB_THETA_G2_COV_NB);

    acb_theta_g2_sextic(r, tau, prec);
    acb_theta_g2_covariants_lead(basic, r, prec);
    hecke_mpoly_eval(source, basic, ctx, prec);

    acb_poly_clear(r);
    _acb_vec_clear(basic, ACB_THETA_G2_COV_NB);
}

static int
hecke_set_eigenvalues(fmpz* eigenvalues, acb_srcptr hecke, const fmpz_poly_t field, slong prec)
{
    slong d = fmpz_poly_degree(field);
    acb_ptr roots;
    acb_ptr pow;
    acb_t z;
    slong k, j;
    int res;

    roots = _acb_vec_init(d);
    pow = _acb_vec_init(2 * d * d);
    acb_init(z);

    arb_fmpz_poly_complex_roots(roots, field, 0, prec);

    for (k = 0; k < d; k++)
    {
        _acb_vec_set_powers(pow + 2 * k * d, &roots[k], 2 * d, prec);
    }
    for (k = 0; (k < d) && res; k++)
    {
        acb_zero(z);
        for (j = 0; j < d; j++)
        {
            acb_dot(z, z, 0, hecke, 1, pow + 2 * j * d + k, 1, d, prec);
        }
        res = acb_get_unique_fmpz(&eigenvalues[k], z);
        if (!acb_contains_int(z))
        {
            flint_printf("error: trace is not integral\n");
            acb_printd(z, 10);
            flint_printf("\n");
            flint_abort();
        }
    }

    _acb_vec_clear(roots, d);
    _acb_vec_clear(pow, 2 * d * d);
    acb_clear(z);
    return res;
}

static int
hecke_attempt(fmpz* eigenvalues, const fmpz_poly_t fields, slong nb_spaces,
    slong* dims, slong* pols_indices, slong p, int is_T1,
    const hecke_mpoly_ctx_t ctx, slong prec)
{
    slong len = pols_indices[nb_spaces];
    acb_mat_t tau;
    acb_ptr hecke;
    acb_ptr source;
    acb_t f;
    slong k, j, l;
    slong k0, j0;
    slong nb = (is_T1 ? hecke_nb_T1(p) : hecke_nb(p));
    int res = 1;

    /* Init */
    acb_mat_init(tau, 2, 2);
    hecke = _acb_vec_init(len);
    source = _acb_vec_init(len);
    acb_init(f);

    flint_printf("\n(hecke_attempt) attempt at precision %wd\n", prec);
    hecke_generate_base_points(tau, 1, prec);

    flint_printf("(hecke_attempt) evaluating covariants at base point...\n");
    hecke_source(source, tau, ctx, prec);
    for (k = 0; (k < nb_spaces) && res; k++)
    {
        acb_inv(&source[k], &source[k], prec);
        res = acb_is_finite(&source[k]);
    }

    flint_printf("(hecke_attempt) evaluating Hecke action...\n");
    for (k = 0; (k < nb) && res; k++)
    {
        if (k % 100 == 0)
        {
            flint_printf("%wd/%wd\n", k, nb);
        }
        hecke_add_term(hecke, len, tau, k, p, is_T1, ctx, prec);
    }

    for (k = 0; k < len; k++)
    {
        acb_mul(&hecke[k], &hecke[k], &source[k], prec);
    }

    /* Get traces of eigenvalue on each eigenform */
    flint_printf("(hecke_attempt) recognizing integers...\n");
    for (k = 0; (k < nb_spaces) && res; k++)
    {
        k0 = ctx->ks[pols_indices[k]];
        j0 = ctx->js[pols_indices[k]];
        hecke_rescale(f, k0, j0, p, is_T1, prec);
        _acb_vec_scalar_mul(hecke + pols_indices[k], hecke + pols_indices[k],
            dims[k], f, prec);
        res = hecke_set_eigenvalues(eigenvalues + pols_indices[k], hecke + pols_indices[k],
            &fields[k], prec);

        if (res)
        {
            flint_printf("Found traces of eigenvalue:\n");
            for (j = 0; j < dims[k]; j++)
            {
                fmpz_print(&eigenvalues[pols_indices[k] + j]);
                flint_printf("\n");
            }
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
    acb_mat_clear(tau);
    _acb_vec_clear(source, len);
    _acb_vec_clear(hecke, len);
    acb_clear(f);
    return res;
}

/* ---------- Main ---------- */

int main(int argc, const char *argv[])
{
    slong q, nb_spaces, p;
    int is_T1;
    slong* dims = NULL;
    slong prec;
    fmpz_mpoly_vec_t pols;
    fmpz_poly_struct* fields;
    slong* pols_indices;
    fmpz* eigenvalues;
    fmpz_mpoly_ctx_t ctx;
    hecke_mpoly_ctx_t hecke_ctx;
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
    for (k = 0; k < nb_spaces; k++)
    {
        dims[k]--; /* account for univariate polynomial */
    }

    fmpz_mpoly_ctx_init(ctx, ACB_THETA_G2_COV_NB, ORD_LEX);
    pols_indices = flint_malloc((nb_spaces + 1) * sizeof(slong));
    pols_indices[0] = 0;
    fields = flint_malloc(nb_spaces * sizeof(fmpz_poly_struct));

    for (k = 0; k < nb_spaces; k++)
    {
        fmpz_poly_init(&fields[k]);
        pols_indices[k + 1] = pols_indices[k] + dims[k];
    }
    fmpz_mpoly_vec_init(pols, pols_indices[nb_spaces], ctx);
    eigenvalues = _fmpz_vec_init(pols_indices[nb_spaces]);

    parse_covariants(pols, fields, nb_spaces, dims, pols_indices, argv[2], ctx);
    get_p_from_q(&p, &is_T1, q);

    flint_printf("(hecke) precomputing additions chains...\n");
    hecke_mpoly_ctx_init(hecke_ctx, pols, pols_indices[nb_spaces], ctx);
    flint_printf("(hecke) done\n");

    prec = 200;
    while (!done)
    {
        done = hecke_attempt(eigenvalues, fields, nb_spaces, dims, pols_indices,
            p, is_T1, hecke_ctx, prec);
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
        for (j = 0; j < dims[k]; j++)
        {
            fmpz_fprint(file_out, &eigenvalues[pols_indices[k] + j]);
        }
        fprintf(file_out, "\n");
    }
    fclose(file_out);

    fmpz_mpoly_vec_clear(pols, ctx);
    for (k = 0; k < nb_spaces; k++)
    {
        fmpz_poly_clear(&fields[k]);
    }
    _fmpz_vec_clear(eigenvalues, pols_indices[nb_spaces]);
    flint_free(pols_indices);
    flint_free(fields);
    flint_free(dims);
    fmpz_mpoly_ctx_clear(ctx);
    hecke_mpoly_ctx_clear(hecke_ctx);

    flint_cleanup();
    return 0;
}
