# Erdős Problem 920

A self-contained exposition of the resolution of Erdős Problem 920 using a strengthened lower bound for off-diagonal Ramsey numbers.

This repository contains:

* a complete proof of the Ramsey-to-chromatic transfer,
* quantitative consequences,
* upper and lower bounds for the relevant chromatic function,
* an equivalent minimum-order formulation,
* and a research appendix on the remaining logarithmic gap.

## Problem Statement

For fixed `k >= 3`, define `f_k(n)` to be the largest chromatic number of an `n`-vertex graph that does not contain a complete graph `K_k`.

In symbols:

```text
f_k(n) = max chromatic number among all n-vertex K_k-free graphs
```

Erdős Problem 920 asks whether, for every fixed `k >= 4`, there exists a constant `c_k > 0` such that:

```text
f_k(n) >= constant_k *
         n^(1 - 1/(k - 1)) *
         (log n)^c_k
```

The manuscript gives an affirmative answer.

## Main Result

Using Bradač's strengthened lower bound for off-diagonal Ramsey numbers, the manuscript proves that for every fixed `k >= 3`:

```text
f_k(n) >= constant_k *
         n^(1 - 1/(k - 1)) *
         (log n)^(2(k - 2)/(k - 1))
```

for all sufficiently large integers `n`.

Therefore, Erdős Problem 920 is resolved affirmatively, and one may take:

```text
c_k = 2(k - 2)/(k - 1)
```

For `k = 4`, this becomes:

```text
f_4(n) >= constant *
         n^(2/3) *
         (log n)^(4/3)
```

## Core Idea

The proof uses a direct transfer from Ramsey numbers to chromatic numbers.

Let `r(k, t)` be the smallest integer `N` such that every graph on `N` vertices contains either:

* a clique of size `k`, or
* an independent set of size `t`.

If:

```text
r(k, t) > n
```

then there exists an `n`-vertex graph `G` containing neither a `K_k` nor an independent set of size `t`.

Therefore:

```text
alpha(G) <= t - 1
```

where `alpha(G)` is the independence number of `G`.

Every color class in a proper coloring is independent, so:

```text
n <= chromatic_number(G) * alpha(G)
```

and hence:

```text
chromatic_number(G) >= ceil(n / (t - 1))
```

Since `G` is `K_k`-free:

```text
f_k(n) >= ceil(n / (t - 1))
```

The rest of the proof consists of choosing `t` by asymptotically inverting a lower bound for `r(k, t)`.

## General Transfer Theorem

Suppose that for fixed `k` there are constants `a > 0`, `d > 1`, and `A >= 0` such that:

```text
r(k, t) >= a * t^d / (log t)^A
```

for all sufficiently large `t`.

Then:

```text
f_k(n) >= C *
         n^(1 - 1/d) *
         (log n)^(A/d)
```

for some constant `C > 0` and all sufficiently large `n`.

Bradač's theorem gives:

```text
d = k - 1
A = 2k - 4
```

Substituting these values yields:

```text
f_k(n) >= constant_k *
         n^(1 - 1/(k - 1)) *
         (log n)^(2(k - 2)/(k - 1))
```

## Exact Graph Orders

The argument produces a graph on exactly `n` vertices for every sufficiently large integer `n`.

It does not require:

* restricting to a sparse sequence of graph orders,
* interpolating between special values of `n`,
* or using an unstated padding argument.

## Current Logarithmic Frontier

Define:

```text
a_k = (k - 2)/(k - 1)
```

The manuscript establishes the lower bound:

```text
f_k(n) >= constant_k *
         n^a_k *
         (log n)^(2a_k)
```

The classical Ajtai-Komlós-Szemerédi Ramsey bound gives the upper estimate:

```text
f_k(n) <= constant_k *
         n^a_k /
         (log n)^a_k
```

Equivalently, the currently known range is:

```text
constant_k *
n^a_k /
(log n)^(2a_k)

<= f_k(n) <=

constant_k *
n^a_k /
(log n)^a_k
```

In particular:

```text
f_k(n) = n^(a_k + o(1))
```

The polynomial exponent is therefore settled.

The remaining uncertainty is entirely logarithmic.

## Equivalent Minimum-Order Problem

Define `h_k(q)` as the smallest number of vertices in a `K_k`-free graph with chromatic number at least `q`.

In words:

```text
h_k(q) = minimum order of a K_k-free graph
         with chromatic number at least q
```

The known estimates imply:

```text
constant_k *
q^((k - 1)/(k - 2)) *
log q

<= h_k(q) <=

constant_k *
q^((k - 1)/(k - 2)) *
(log q)^2
```

Thus the sharper endpoint problem is equivalent to removing one logarithmic factor from the upper bound for `h_k(q)`.

## Remaining Open Problem

The original yes-or-no problem is solved.

The remaining research problem is to determine the correct logarithmic exponent.

The desired sharper bound is:

```text
f_k(n) >= constant_k *
         (n / log n)^((k - 2)/(k - 1))
```

Equivalently:

```text
h_k(q) <= constant_k *
          q^((k - 1)/(k - 2)) *
          log q
```

For `k = 4`, this asks for a `K_4`-free graph with:

```text
number of vertices = O(q^3 log q)
chromatic number   = Omega(q^2)
```

## Research Appendix

The appendix records a verification-controlled investigation of the sharper endpoint.

Each item is explicitly labelled as one of:

* proved,
* refuted,
* conditional,
* experimental,
* or open.

None of the exploratory material is required for the main theorem.

### Proved Components

* Finite Ramsey-to-chromatic transfer
* General asymptotic inversion
* Hereditary independent-set extraction
* Dyadic coloring argument
* Minimum-order inversion
* Quadratic collision certificate
* Laminar zero-rectangle identity
* Support-exact low-rank matrix construction
* Shift-graph obstruction

### Refuted Approaches

* Additive resource packing with the wrong inequality direction
* Constant-size conflict refinement of acyclic classes
* Separate treatment of container budgets
* Universal quadratic gain lower-tail estimates
* Single dominant balanced-block arguments

### Conditional or Open Directions

* Regular-spread phase model for `k = 4`
* Multi-block phase-moment estimates
* Aggregate line-energy control
* Higher-order convex certificates
* Semidefinite certificates
* Modified algebraic constructions
* Direct quadratic collision bounds

## Suggested Repository Structure

```text
.
├── README.md
├── paper/
│   └── erdos_problem_920.pdf
├── notes/
│   ├── ramsey_to_chromatic_transfer.md
│   ├── logarithmic_frontier.md
│   └── research_appendix.md
├── experiments/
│   ├── independent_set_milp/
│   ├── coloring_search/
│   └── phase_model/
├── formalization/
│   └── lean/
└── LICENSE
```

## Formalization

The elementary logical core of the proof is short:

```text
n < r(k, t)

implies that there exists a graph G such that:

|V(G)| = n
G is K_k-free
alpha(G) < t
```

Then:

```text
n <= chromatic_number(G) * alpha(G)
```

so:

```text
chromatic_number(G) > n / t
```

A Lean formalization could therefore isolate Bradač's Ramsey theorem as the only deep imported result and kernel-check the entire transfer argument.

## Trust Boundary

The manuscript carefully separates proved statements from imported and exploratory material.

* The Ramsey-to-chromatic transfer is proved in the manuscript.
* The asymptotic inversion is proved in the manuscript.
* The chromatic upper bound is derived in the manuscript.
* Bradač's off-diagonal Ramsey lower bound is imported.
* The Ajtai-Komlós-Szemerédi Ramsey upper bound is imported.
* The exploratory appendices are not used in the proof of the main result.
* Experimental observations are not presented as asymptotic theorems.
* Refuted conjectures are retained to document failed approaches.

## Citation

```bibtex
@misc{lua2026erdos920,
  author = {Moses Lua},
  title = {Erdos Problem 920 from an Off-Diagonal Ramsey Bound},
  year = {2026},
  month = {July},
  note = {A complete proof, quantitative consequences, and a research appendix on the remaining logarithmic gap}
}
```

Add the repository URL, DOI, or archival identifier once available.

## References

1. M. Ajtai, J. Komlós, and E. Szemerédi,
   *A note on Ramsey numbers*, Journal of Combinatorial Theory, Series A, 29 (1980), 354-360.

2. D. Bradač,
   *Off-diagonal Ramsey numbers*, arXiv preprint, 2026.

3. P. Erdős,
   *Problems and results in chromatic graph theory*, in *Proof Techniques in Graph Theory*, Academic Press, 1969.

4. J. E. Graver and J. Yackel,
   *Some graph theoretic results associated with Ramsey's theorem*, Journal of Combinatorial Theory, 4 (1968), 125-175.

5. S. Mattheus and J. Verstraete,
   *The asymptotics of r(4, t)*, Annals of Mathematics, 199 (2024), 919-941.

## Author

Moses Lua

## License

Choose a license based on the intended use.

For the manuscript:

```text
Creative Commons Attribution 4.0 International
```

For accompanying software or experiments:

```text
MIT License
```
