/**
 * OptiMathSAT API usage example
 *
 * Authors: Silvia Tomasi,
 *          Patrick Trentin <patrick.trentin@unitn.it>
 *
 * This file is part of OptiMathSAT5.
 *
 * to compile: g++ api_example.cpp -I${MSAT_DIR}/include -L${MSAT_DIR}/lib
 *                -lmathsat -lgmpxx -lgmp -lstdc++ -o api_example
 */

#include "mathsat.h"
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <set>
#include <stack>
#include <assert.h>
#include <math.h>

struct Options {
    const char *filename;
    const char *local_lower;
    const char *local_upper;
    const char *objective;
    bool model;
    Options(): model(false), filename(""), local_lower(NULL), local_upper(NULL), objective(NULL) {};
};

const char *usage_str = "usage:\n\
\t-f STR: input filename with formula\n\
\t-o STR: variable to be minimized in the input formula\n\
\t-m    : if set, optimum model will be printed on stdout\n\
\t-l NUM: objective local lower bound (default: -inf)\n\
\t-u NUM: objective local upper bound (default: +inf)\n";

bool parse_options(int argc, char **argv, Options *opts)
{
    int c;
    opterr = 0;
    while ((c = getopt(argc, argv, "f:ml:o:u:")) != -1) {
        switch (c) {
        case 'f':
            opts->filename = optarg;
            break;
        case 'm':
            opts->model = true;
            break;
        case 'l':
            opts->local_lower = optarg;
            break;
        case 'o':
            opts->objective = optarg;
            break;
        case 'u':
            opts->local_upper = optarg;
            break;
        default:
            fprintf(stderr, "%s", usage_str);
            return false;
        }
    }

    if (opts->objective == NULL || opts->filename == NULL) {
        fprintf(stderr, "Please, specify an input file name and objective variable.\n");
        return false;
    }
    return true;
}

msat_term get_cost_variable(msat_env env, msat_term term, const char *cv)
{
    assert(cv);
    std::set<int> seen;
    std::stack<msat_term> to_process;
    to_process.push(term);
    while (!to_process.empty()) {
        msat_term t = to_process.top();
        to_process.pop();
        if (!seen.insert(msat_term_id(t)).second) {
            continue;
        }
        if (msat_term_is_constant(env,t) > 0) {
            char *n =  msat_decl_get_name(msat_term_get_decl(t));
            if (0 == strcmp(n, cv)) {
                return t;
            }
        }
        for (int i = 0; i < msat_term_arity(t); ++i) {
            to_process.push(msat_term_get_arg(t, i));
        }
    }
    msat_term ret;
    MSAT_MAKE_ERROR_TERM(ret);
    return ret;
}

int main(int argc, char **argv)
{
    mpf_set_default_prec(256);

    Options opts;
    if (!parse_options(argc, argv, &opts)) {
        return -1;
    }

    /* istantiate environment */
    msat_config cfg = msat_create_config();
    msat_set_option(cfg, "unsat_core_generation", "true");
    if (opts.model)
        msat_set_option(cfg, "model_generation", "true");    // NOTE: required to create model
    msat_env env = msat_create_env(cfg);

    /* read formula */
    FILE *f = stdin;
    fprintf(stdout, "Reading from %s ...\n", opts.filename);
    if (opts.filename) {
        f = fopen(opts.filename, "r");
    }
    if (!f) {
        fprintf(stderr, "Unable to open `%s'\n", opts.filename);
        return -1;
    }
    msat_term formula = msat_from_smtlib2_file(env, f);
    if (MSAT_ERROR_TERM(formula)) {
        fprintf(stderr, "Unable to parse `%s'", opts.filename);
        return -1;
    }
    if (f != stdin) {
        fclose(f);
    }

    /* create optimization term */
    // NOTE: for simplicity, we require input objective to be a variable
    // already present in the input formula and scan it to get its associated
    // term. Note that this is an arbitrary restriction, one is free to build
    // arbitrary objective functions by means of MathSAT API calls.
    msat_term cost = get_cost_variable(env, formula, opts.objective);
    if (MSAT_ERROR_TERM(cost)) {
        fprintf(stderr, "Error in detecting the cost variable.\n");
        return -1;
    }

    msat_assert_formula(env, formula);

    /* create objective */
    fprintf(stdout, "Minimizing `%s' ...\n", opts.objective);
    msat_objective o = msat_push_minimize(env, cost, opts.local_lower, opts.local_upper);

    if (MSAT_ERROR_OBJECTIVE(o)) {
        fprintf(stderr, "The objective is invalid.\n");
        return -1;
    }

    /* optimize */
    // NOTE: in multi-objective, the overall search result and the result
    // of a specific objective might differ.
    msat_result res = msat_solve(env);

    msat_opt_result optres = msat_objective_result(env, o);

    switch(optres) {
    case MSAT_OPT_UNKNOWN:
        fprintf(stderr, "Unable to decide satisfiability or optimality!\n");
        break;
    case MSAT_OPT_UNSAT:
        fprintf(stderr, "The problem is unsatisfiable!\n");
        break;
    case MSAT_OPT_SAT_PARTIAL:
    case MSAT_OPT_SAT_APPROX:
    case MSAT_OPT_SAT_OPTIMAL:
        /* Access some objective information */
        bool is_unbounded = (msat_objective_value_is_unbounded(env, o, MSAT_OPTIMUM) > 0);
        if (is_unbounded) {
            bool is_plus_inf = (msat_objective_value_is_plus_inf(env, o, MSAT_OPTIMUM) > 0);
            bool is_minus_inf = (msat_objective_value_is_minus_inf(env, o, MSAT_OPTIMUM) > 0);
            if (is_plus_inf) {
                fprintf(stderr, "Error: satisfiable solution should not be +INF when minimizing.\n");
            }
            if (is_minus_inf) {
                fprintf(stdout, "The objective is lower unbounded!\n");
            }
        } else {
            int delta;
            bool is_strict = (msat_objective_value_is_strict(env, o, MSAT_OPTIMUM, delta) > 0);
            char* obj_opt_term_repr = msat_objective_value_repr(env, o, MSAT_OPTIMUM);
            assert(obj_opt_term_repr);
            fprintf(stdout, "Found exact %s optimum value: %s\n",
                            (is_strict ? "strict" : "non-strict"),
                            obj_opt_term_repr);
            msat_free(obj_opt_term_repr);
        }
        /* print model */
        if (opts.model) {
            if (msat_set_model(env, o)) {
                fprintf(stderr, "Unable to retrieve optimum model!\n");
            } else {
                fprintf(stdout, "Associated Model:\n");
                msat_model_iterator it = msat_create_model_iterator(env);
                while (msat_model_iterator_has_next(it)) {
                    msat_term t, v;
                    msat_model_iterator_next(it, &t, &v);
                    char *s;
                    s = msat_term_repr(t);
                    fprintf(stdout, "%s = ", s);
                    free(s);
                    s = msat_term_repr(v);
                    fprintf(stdout, "%s\n", s);
                    free(s);
                }
                fprintf(stdout, "\n");
            }
        }
        /* print usual OptiMathSAT stats */
        char* search_stats = msat_objective_get_search_stats(env, o);
        if (search_stats) {
            fprintf(stdout, "%s\n", search_stats);
            msat_free(search_stats);
        }
        break;
    }
    msat_destroy_env(env);

    return 0;
}
