

int main(void)
{
    slong iter;
    flint_rand_t state;

    flint_printf("g2_basic_covariants_hecke....");
    fflush(stdout);

    flint_randinit(state);

    /* Test: find eigenvalue (1+p^2)(1+p^3) for E4 = -(Co20^2 - 3*Co40)/20 at p prime */
    for (iter = 0; iter < 1 * flint_test_multiplier(); iter++)
    {
        slong g = 2;
        slong nb_cov = ACB_THETA_G2_BASIC_NB;
        acb_mat_t tau;
        acb_ptr cov;
        acb_t r, s, t, u, v;
        slong prec = 100;
        slong primes[] = {2,3,5}; /*,3,5,7,11,13,17};*/
        slong nprimes = 3;
        slong k, p, l;

        acb_mat_init(tau, g, g);
        acb_init(u);
        acb_init(v);
        acb_init(r);
        acb_init(s);
        acb_init(t);

        /* Generate matrix with nice imaginary part */
        arb_urandom(acb_realref(acb_mat_entry(tau, 0, 0)), state, prec);
        arb_set_si(acb_imagref(acb_mat_entry(tau, 0, 0)), 1);
        arb_set_si(acb_imagref(acb_mat_entry(tau, 1, 1)), 1);
        arb_urandom(acb_realref(acb_mat_entry(tau, 0, 1)), state, prec);
        arb_urandom(acb_imagref(acb_mat_entry(tau, 0, 1)), state, prec);
        acb_mul_2exp_si(acb_mat_entry(tau, 0, 1), acb_mat_entry(tau, 0, 1), -2);
        acb_set(acb_mat_entry(tau, 1, 0), acb_mat_entry(tau, 0, 1));

        for (k = 0; k < nprimes; k++)
        {
            p = primes[k];
            /* flint_printf("\n\n\n*** Start p = %wd ***\n\n", p); */

            cov = _acb_vec_init(nb_cov * (acb_theta_g2_hecke_nb(p) + 1));
            acb_theta_g2_basic_covariants_hecke(cov, tau, p, prec);

            /* Get Co20 - 3*Co40 at tau */
            acb_mul_si(u, &cov[8], -3, prec);
            acb_sqr(v, &cov[1], prec);
            acb_add(s, u, v, prec);

            /* Get sum of Co20 - 3*Co40 at images */
            acb_zero(r);
            for (l = 0; l < acb_theta_g2_hecke_nb(p); l++)
            {
                acb_mul_si(u, &cov[(l + 1) * nb_cov + 8], -3, prec);
                acb_sqr(v, &cov[(l + 1) * nb_cov + 1], prec);
                acb_add(u, u, v, prec);
                acb_add(r, r, u, prec);
            }

            acb_div(r, r, s, prec);
            acb_set_si(s, n_pow(p, 5));
            acb_mul(r, r, s, prec);

            /* Get expected eigenvalue */
            if (n_is_prime(p))
            {
                acb_set_si(t, (1 + n_pow(p, 2)) * (1 + n_pow(p, 3)));
            }
            else
            {
                p = n_sqrt(p);
                acb_set_si(t, n_pow(p, 4) - n_pow(p, 2) + n_pow(p, 6)
                    + n_pow(p, 7) + p + n_pow(p, 2));
            }

            if (!acb_overlaps(r, t))
            {
                flint_printf("FAIL (p = %wd)\n", p);
                acb_printd(r, 5);
                flint_printf("\n");
                acb_printd(t, 5);
                flint_printf("\n");
                flint_abort();
            }

            _acb_vec_clear(cov, nb_cov * (acb_theta_g2_hecke_nb(p) + 1));
        }

        acb_mat_clear(tau);
        acb_clear(u);
        acb_clear(v);
        acb_clear(r);
        acb_clear(s);
        acb_clear(t);
    }

    flint_randclear(state);
    flint_cleanup();
    flint_printf("PASS\n");
    return 0;
}

int main(void)
{
    slong iter;
    flint_rand_t state;

    flint_printf("g2_covariant....");
    fflush(stdout);

    flint_randinit(state);

    /* Test: agrees with g2_psi4 using psi4 = -(Co20 - 3*Co40)/20 */
    for (iter = 0; iter < 5 * flint_test_multiplier(); iter++)
    {
        slong prec = 100 + n_randint(state, 100);
        slong g = 2;
        slong n = 1 << (2 * g);
        acb_mat_t tau;
        acb_ptr z, th2;
        acb_poly_struct* r;
        acb_poly_t u;
        fmpz_mpoly_ctx_t ctx;
        fmpz_mpoly_t pol, v;
        acb_t psi4, test;
        slong k;

        acb_mat_init(tau, g, g);
        z = _acb_vec_init(g);
        th2 = _acb_vec_init(n);
        r = flint_malloc(26 * sizeof(acb_poly_struct));
        for (k = 0; k < 26; k++)
        {
            acb_poly_init(&r[k]);
        }
        acb_poly_init(u);
        fmpz_mpoly_ctx_init(ctx, 26, ORD_LEX);
        fmpz_mpoly_init(pol, ctx);
        fmpz_mpoly_init(v, ctx);
        acb_init(psi4);
        acb_init(test);

        acb_siegel_randtest_nice(tau, state, prec);
        acb_theta_all(th2, z, tau, 1, prec);
        acb_theta_g2_psi4(psi4, th2, prec);
        acb_mul_si(psi4, psi4, -20, prec);

        acb_theta_g2_fundamental_covariant(u, tau, prec);
        acb_theta_g2_basic_covariants(r, u, prec);
        fmpz_mpoly_gen(pol, 1, ctx);
        fmpz_mpoly_mul(pol, pol, pol, ctx);
        fmpz_mpoly_gen(v, 8, ctx);
        fmpz_mpoly_scalar_mul_si(v, v, -3, ctx);
        fmpz_mpoly_add(pol, pol, v, ctx);

        acb_theta_g2_covariant(u, pol, r, ctx, prec);
        acb_poly_get_coeff_acb(test, u, 0);

        if (!acb_overlaps(psi4, test))
        {
            flint_printf("FAIL\n");
            acb_mat_printd(tau, 5);
            flint_printf("psi4, test:\n");
            acb_printd(psi4, 10);
            flint_printf("\n");
            acb_printd(test, 10);
            flint_printf("\nu:\n");
            acb_poly_printd(u, 5);
            flint_printf("\ncovariants:\n");
            for (k = 0; k < 26; k++)
            {
                acb_poly_printd(&r[k], 5);
                flint_printf("\n");
            }
            flint_abort();
        }

        acb_mat_clear(tau);
        _acb_vec_clear(z, g);
        _acb_vec_clear(th2, n);
        for (k = 0; k < 26; k++)
        {
            acb_poly_clear(&r[k]);
        }
        flint_free(r);
        acb_poly_clear(u);
        fmpz_mpoly_clear(pol, ctx);
        fmpz_mpoly_clear(v, ctx);
        fmpz_mpoly_ctx_clear(ctx);
        acb_clear(psi4);
        acb_clear(test);
    }

    flint_randclear(state);
    flint_cleanup();
    flint_printf("PASS\n");
    return 0;
}


int main(void)
{
    slong iter;
    flint_rand_t state;

    flint_printf("g2_slash_basic_covariants....");
    fflush(stdout);

    flint_randinit(state);

    /* Test: action of Sp4 */
    for (iter = 0; iter < 5 * flint_test_multiplier(); iter++)
    {
        slong prec = 100 + n_randint(state, 100);
        slong g = 2;
        slong nb = ACB_THETA_G2_BASIC_NB;
        fmpz_mat_t mat;
        acb_mat_t tau, w, c;
        acb_poly_struct *cov1, *cov2, *test;
        acb_poly_t r1, r2;
        slong k;

        fmpz_mat_init(mat, 4, 4);
        acb_mat_init(tau, g, g);
        acb_mat_init(w, g, g);
        acb_mat_init(c, g, g);
        cov1 = flint_malloc(nb * sizeof(acb_poly_struct));
        cov2 = flint_malloc(nb * sizeof(acb_poly_struct));
        test = flint_malloc(nb * sizeof(acb_poly_struct));
        for (k = 0; k < nb; k++)
        {
            acb_poly_init(&cov1[k]);
            acb_poly_init(&cov2[k]);
            acb_poly_init(&test[k]);
        }
        acb_poly_init(r1);
        acb_poly_init(r2);

        acb_siegel_randtest_nice(tau, state, prec);
        acb_mat_scalar_mul_2exp_si(tau, tau, -2);
        acb_siegel_reduce(w, mat, tau, prec);
        acb_siegel_cocycle(c, mat, tau, prec);

        acb_theta_g2_fundamental_covariant(r1, tau, prec);
        acb_theta_g2_basic_covariants(cov1, r1, prec);
        acb_theta_g2_fundamental_covariant(r2, w, prec);
        acb_theta_g2_basic_covariants(cov2, r2, prec);
        acb_theta_g2_slash_basic_covariants(test, c, cov1, prec);

        for (k = 0; k < nb; k++)
        {
            if (!acb_poly_overlaps(&test[k], &cov2[k]))
            {
                flint_printf("FAIL (k = %wd)\n", k);
                fmpz_mat_print_pretty(mat);
                flint_printf("\n");
                acb_mat_printd(c, 5);
                acb_poly_printd(&test[k], 5);
                flint_printf("\n");
                acb_poly_printd(&cov2[k], 5);
                flint_printf("\nsource:\n");
                acb_poly_printd(&cov1[k], 5);
                flint_printf("\nfundamental:\n");
                acb_poly_printd(r1, 5);
                flint_printf("\n");
                acb_poly_printd(r2, 5);
                flint_printf("\n");
                flint_abort();
            }
        }

        fmpz_mat_clear(mat);
        acb_mat_clear(tau);
        acb_mat_clear(w);
        acb_mat_clear(c);
        for (k = 0; k < nb; k++)
        {
            acb_poly_clear(&cov1[k]);
            acb_poly_clear(&cov2[k]);
            acb_poly_clear(&test[k]);
        }
        flint_free(cov1);
        flint_free(cov2);
        flint_free(test);
        acb_poly_clear(r1);
        acb_poly_clear(r2);
    }

    flint_randclear(state);
    flint_cleanup();
    flint_printf("PASS\n");
    return 0;
}


int main(void)
{
    slong iter;
    flint_rand_t state;

    flint_printf("spd_radius....");
    fflush(stdout);

    flint_randinit(state);

    /* Test: random matrix within radius is still positive definite */
    for (iter = 0; iter < 500 * flint_test_multiplier(); iter++)
    {
        slong g = 1 + n_randint(state, 10);
        slong prec = 200 + n_randint(state, 500);
        slong mag_bits = 1 + n_randint(state, 5);
        arb_mat_t A, B, cho;
        arf_t rad, c;
        slong k, j;
        int res;

        arb_mat_init(A, g, g);
        arb_mat_init(B, g, g);
        arb_mat_init(cho, g, g);
        arf_init(rad);
        arf_init(c);

        arb_mat_randtest_spd(A, state, prec, mag_bits);
        arb_mat_spd_radius(rad, A, prec);

        if (!arf_is_finite(rad) || arf_cmp_si(rad, 0) <= 0)
        {
            flint_printf("FAIL (not positive)\n");
            flint_printf("g = %wd, prec = %wd, mag_bits = %wd\n", g, prec, mag_bits);
            arb_mat_printd(A, 5);
            arf_printd(rad, 10);
            flint_printf("\n");
            flint_abort();
        }

        for (k = 0; k < g; k++)
        {
            for (j = 0; j <= k; j++)
            {
                /* Get c between -rad and rad */
                arf_urandom(c, state, prec, ARF_RND_FLOOR);
                arf_mul_2exp_si(c, c, 1);
                arf_sub_si(c, c, 1, prec, ARF_RND_DOWN);
                arf_mul(c, c, rad, prec, ARF_RND_DOWN);

                arb_add_arf(arb_mat_entry(B, k, j), arb_mat_entry(A, k, j),
                    c, prec);
                arb_set(arb_mat_entry(B, j, k), arb_mat_entry(B, k, j));
            }
        }

        res = arb_mat_cho(cho, B, prec);
        if (!res)
        {
            flint_printf("FAIL (cholesky)\n");
            flint_printf("g = %wd, prec = %wd, mag_bits = %wd\n", g, prec, mag_bits);
            arb_mat_printd(A, 5);
            flint_printf("radius: ");
            arf_printd(rad, 10);
            flint_printf("\n");
            flint_printf("Deformed matrix:\n");
            arb_mat_printd(B, 5);
            flint_abort();
        }

        arb_mat_clear(A);
        arb_mat_clear(B);
        arb_mat_clear(cho);
        arf_clear(rad);
        arf_clear(c);
    }

    flint_randclear(state);
    flint_cleanup();
    flint_printf("PASS\n");
    return 0;
}


int main(void)
{
    slong iter;
    flint_rand_t state;

    flint_printf("g2_psi4....");
    fflush(stdout);

    flint_randinit(state);

    /* Test: agrees with polynomial expression in terms of chi6m2 */
    for (iter = 0; iter < 10 * flint_test_multiplier(); iter++)
    {
        slong g = 2;
        slong n = 1 << (2 * g);
        slong nb = acb_theta_jet_nb(1, g + 1);
        slong prec = 100 + n_randint(state, 100);
        slong bits = n_randint(state, 4);
        char str[] = "1620*a6^2*a0^2 + ((300*a5^2 - 504*a4*a6)*a2 + ((-540*a1*a6 - 180*a4*a3)*a5 + (324*a3^2*a6 + 48*a4^3)))*a0 + (48*a6*a2^3 + (-12*a3*a5 + 4*a4^2)*a2^2 + (4*a4*a1*a5 - 180*a3*a1*a6)*a2 + (-80*a1^2*a5^2 + 36*a3^2*a1*a5 + (300*a4*a1^2*a6 - 12*a4^2*a3*a1)))";
        char* vars[] = {"a0", "a1", "a2", "a3", "a4", "a5", "a6"};
        fmpz_mpoly_ctx_t ctx;
        fmpz_mpoly_t pol;
        acb_mat_t tau;
        acb_ptr z, th2, dth, val;
        acb_poly_t chi;
        acb_t psi4, test;
        slong k;

        fmpz_mpoly_ctx_init(ctx, 7, ORD_LEX);
        fmpz_mpoly_init(pol, ctx);
        acb_mat_init(tau, g, g);
        z = _acb_vec_init(g);
        th2 = _acb_vec_init(n);
        dth = _acb_vec_init(n * nb);
        val = _acb_vec_init(7);
        acb_poly_init(chi);
        acb_init(psi4);
        acb_init(test);

        acb_siegel_randtest_reduced(tau, state, prec, bits);

        acb_theta_jet_all(dth, z, tau, 1, prec);
        acb_theta_all(th2, z, tau, 1, prec);
        acb_theta_g2_psi4(psi4, th2, prec);

        acb_theta_g2_chi6m2(chi, dth, prec);
        for (k = 0; k <= 6; k++)
        {
            acb_poly_get_coeff_acb(&val[k], chi, 6 - k);
        }
        fmpz_mpoly_set_str_pretty(pol, str, (const char**) vars, ctx);
        acb_eval_fmpz_mpoly(test, pol, val, ctx, prec);
        acb_mul_2exp_si(test, test, -2);

        if (!acb_overlaps(psi4, test))
        {
            flint_printf("FAIL\n");
            flint_printf("chi6m2:\n");
            _acb_vec_printd(val, 7, 5);
            flint_printf("pol:\n");
            fmpz_mpoly_print_pretty(pol, (const char**) vars, ctx);
            flint_printf("\npsi4, test:\n");
            acb_printd(psi4, 10);
            flint_printf("\n");
            acb_printd(test, 10);
            flint_printf("\n");
            flint_abort();
        }

        fmpz_mpoly_clear(pol, ctx);
        fmpz_mpoly_ctx_clear(ctx);
        acb_mat_clear(tau);
        _acb_vec_clear(z, g);
        _acb_vec_clear(th2, n);
        _acb_vec_clear(dth, n * nb);
        _acb_vec_clear(val, 7);
        acb_poly_clear(chi);
        acb_clear(psi4);
        acb_clear(test);
    }

    flint_randclear(state);
    flint_cleanup();
    flint_printf("PASS\n");
    return 0;
}
