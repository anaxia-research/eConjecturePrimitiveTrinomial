# Exact checks in Python and C

These scripts recompute every numerical statement of the paper with exact arithmetic
(Python integers and rationals, sympy, python-flint). The two C programs are an exact maximum-clique
solver and a backtracking enumerator. Requirements: Python 3.11+, sympy, mpmath, python-flint,
networkx (not essential), gcc.

    gcc -O3 -o c/mc c/mc.c && gcc -O3 -o c/caged c/caged.c
    python3 v1_eulerian.py 60      # signed Eulerian identities (n <= 8 by brute force); real zeros, n <= 60
    python3 v1b_dominance.py 64    # numerical illustration of the dominance lemma, 50 <= n <= 64
    python3 v2_steiner.py          # 2-Steiner matrix: a_{2n-5}, peak index, n <= 60
    python3 v3_canon.py            # canon: B_k closed form, Jacobi expansion (k <= 40), real zeros (k <= 60)
    python3 v3b_canonQ.py          # Q_0..Q_24, multisum, Hankel determinants, k Q_k / 8^k
    python3 v3c_logconc.py 110 45  # Q_k(x) log-concave for k <= 110, nonreal zeros for k <= 45
    python3 v5_dumont.py           # deformed Dumont counts, n <= 8; Proposition on first letters
    python3 v6a_paths.py           # grid rank (a,b <= 24), tau rule, skeleton counts, depth formula
    python3 v6b_cliques.py rect 400; python3 v6b_cliques.py oddsq 6 1500; python3 v6b_cliques.py freeend 9 1200
    python3 v6b_cliques.py catalan 5; python3 v6b_cliques.py oddcat 4
    python3 v6b_cliques.py tworows 22; python3 v6b_cliques.py rows 3 3 13 1500; python3 v6b_cliques.py rows 4 5 10 2000
    python3 v6c_higher.py          # the table of 26 boxes in dimensions 2 to 5
    python3 v7_sigma.py            # Theorem on sigma(M): construction for n <= 8, lower bound for M_0, n <= 6
    python3 v9_misc.py             # constructions, the 23-path family, window families, meander table
    python3 v10_misc2.py           # B_k moments (numerical), caged cycles and construction, block families
    c/caged n T                    # permutations of [n] with c(pi) <= T: counts, orbits, n-cycles
