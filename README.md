# Erdős Problem 920

A self-contained exposition of the resolution of **Erdős Problem 920** using a strengthened lower bound for off-diagonal Ramsey numbers.

This repository contains the proof, quantitative consequences, and exploratory research notes related to the remaining logarithmic gap.

## Main Result

For fixed (k \ge 3), define

[
f_k(n)
======

\max\left{
\chi(G):
|V(G)|=n
\text{ and }
G \text{ is } K_k\text{-free}
\right}.
]

Erdős Problem 920 asks whether, for every fixed (k \ge 4), there exists a constant (c_k>0) such that

[
f_k(n)
\gg_k
n^{1-\frac{1}{k-1}}
(\log n)^{c_k}.
]

Using Bradač’s strengthened lower bound for off-diagonal Ramsey numbers,

[
r(k,t)
\gg_k
\frac{t^{k-1}}{(\log t)^{2k-4}},
]

the project proves that

[
\boxed{
f_k(n)
\gg_k
n^{1-\frac{1}{k-1}}
(\log n)^{\frac{2(k-2)}{k-1}}
}
]

for every fixed (k\ge 3) and all sufficiently large (n).

Therefore, Erdős Problem 920 has an affirmative answer, with

[
\boxed{
c_k=\frac{2(k-2)}{k-1}
}.
]

For (k=4), this gives

[
f_4(n)
\gg
n^{2/3}(\log n)^{4/3}.
]

---

## Core Idea

The proof uses a finite Ramsey-to-chromatic transfer.

If

[
r(k,t)>n,
]

then there exists an (n)-vertex graph (G) containing neither a (K_k) nor an independent set of size (t). Hence

[
\alpha(G)\le t-1.
]

Since every color class is independent,

[
n\le \chi(G)\alpha(G),
]

and therefore

[
\chi(G)\ge
\left\lceil
\frac{n}{t-1}
\right\rceil.
]

Thus,

[
f_k(n)\ge
\left\lceil
\frac{n}{t-1}
\right\rceil.
]

The remaining step is to choose (t) by asymptotically inverting the Ramsey lower bound.

---

## General Transfer Theorem

Suppose that, for fixed (k),

[
r(k,t)
\ge
a\frac{t^d}{(\log t)^A}
]

for sufficiently large (t), where (d>1).

Then

[
f_k(n)
\gg
n^{1-\frac1d}
(\log n)^{A/d}.
]

Applying this with

[
d=k-1,
\qquad
A=2k-4,
]

gives

[
f_k(n)
\gg_k
n^{1-\frac{1}{k-1}}
(\log n)^{\frac{2(k-2)}{k-1}}.
]

The proof works for every sufficiently large integer (n); it does not require restricting to a sparse sequence of admissible graph orders.

---

## Current Bounds

Let

[
a_k=\frac{k-2}{k-1}.
]

The established lower bound is

[
f_k(n)
\gg_k
n^{a_k}(\log n)^{2a_k}.
]

The classical Ajtai–Komlós–Szemerédi Ramsey upper bound gives the complementary estimate

[
f_k(n)
\ll_k
\frac{n^{a_k}}{(\log n)^{a_k}}.
]

Consequently,

[
\frac{n^{a_k}}{(\log n)^{2a_k}}
\ll_k
f_k(n)
\ll_k
\frac{n^{a_k}}{(\log n)^{a_k}},
]

and in particular,

[
f_k(n)=n^{a_k+o(1)}.
]

The polynomial exponent is settled. The remaining uncertainty is entirely polylogarithmic.

---

## Equivalent Minimum-Order Formulation

Define

[
h_k(q)
======

\min\left{
|V(G)|:
G \text{ is } K_k\text{-free and }
\chi(G)\ge q
\right}.
]

The known estimates imply

[
q^{\frac{k-1}{k-2}}\log q
\ll_k
h_k(q)
\ll_k
q^{\frac{k-1}{k-2}}(\log q)^2.
]

The sharp endpoint problem is therefore equivalent to removing one logarithmic factor from the upper bound for (h_k(q)).

---

## Open Problem

The original Erdős problem is resolved.

The remaining problem is to determine the optimal logarithmic exponent in the growth of (f_k(n)).

Equivalently, one seeks a bound of the form

[
f_k(n)
\gg_k
\left(\frac{n}{\log n}\right)^{\frac{k-2}{k-1}},
]

or

[
h_k(q)
\ll_k
q^{\frac{k-1}{k-2}}\log q.
]

For (k=4), this asks for a (K_4)-free graph on

[
O(q^3\log q)
]

vertices with chromatic number

[
\Omega(q^2).
]

---

## Research Directions

The accompanying research appendix investigates several possible approaches to the sharper logarithmic endpoint.

### Proved components

* Finite Ramsey-to-chromatic transfer
* General asymptotic inversion theorem
* Hereditary independent-set extraction
* Dyadic coloring upper bound
* Equivalent minimum-order formulation
* Quadratic collision certificate
* Laminar zero-rectangle identity
* Support-exact low-rank matrix construction
* Shift-graph obstruction to bounded conflict refinement

### Refuted approaches

* Additive resource packing with the incorrect inequality direction
* Constant-size conflict refinement of acyclic classes
* Independent treatment of separate container budgets
* A universal quadratic gain lower-tail estimate
* A single dominant balanced-block dichotomy

### Conditional or open approaches

* Regular-spread phase model for (k=4)
* Multi-block phase-moment estimates
* Aggregate line-energy control across disjoint color classes
* Higher-order convex or semidefinite certificates
* Modified algebraic constructions with shared exceptional choices

---

## Repository Structure

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

The exact structure may be adjusted depending on whether the repository contains only the manuscript or also includes computational experiments and formal verification files.

---

## Formalization

The elementary logical core of the proof is short:

[
n<r(k,t)
\Longrightarrow
\exists G,\quad
|V(G)|=n,\quad
K_k\nsubseteq G,\quad
\alpha(G)<t,
]

followed by

[
n\le \chi(G)\alpha(G)<\chi(G)t.
]

A Lean formalization can therefore treat Bradač’s Ramsey theorem as the only deep imported result and kernel-check the complete transfer argument.

---

## Status and Trust Boundary

The repository distinguishes carefully between established results and exploratory research.

* The Ramsey-to-chromatic transfer and asymptotic inversion are proved in the manuscript.
* The off-diagonal Ramsey lower bound is imported from Bradač’s work.
* The Ramsey upper bound is imported from Ajtai, Komlós, and Szemerédi.
* The main resolution does not depend on the exploratory appendices.
* Experimental observations are not presented as asymptotic proofs.
* Conditional constructions are explicitly labelled as conditional.
* Refuted conjectures are retained to document failed approaches and prevent their accidental reuse.

---

## Citation

When referencing this work, please cite the manuscript as:

```bibtex
@misc{lua2026erdos920,
  author       = {Moses Lua},
  title        = {Erdős Problem 920 from an Off-Diagonal Ramsey Bound},
  year         = {2026},
  month        = {July},
  note         = {A complete proof, quantitative consequences, and a research appendix on the remaining logarithmic gap}
}
```

A repository-specific URL or archival identifier can be added once available.

---

## References

1. M. Ajtai, J. Komlós, and E. Szemerédi,
   *A note on Ramsey numbers*, Journal of Combinatorial Theory, Series A, 29 (1980), 354–360.

2. D. Bradač,
   *Off-diagonal Ramsey numbers*, arXiv preprint, 2026.

3. P. Erdős,
   *Problems and results in chromatic graph theory*, in *Proof Techniques in Graph Theory*, Academic Press, 1969.

4. J. E. Graver and J. Yackel,
   *Some graph theoretic results associated with Ramsey’s theorem*, Journal of Combinatorial Theory, 4 (1968), 125–175.

5. S. Mattheus and J. Verstraete,
   *The asymptotics of (r(4,t))*, Annals of Mathematics, 199 (2024), 919–941.

---

## Author

**Moses Lua**

---

## License

Add the license appropriate for the intended use of the manuscript and source files.

For example:

```text
CC BY 4.0
```

for the manuscript, or

```text
MIT License
```

for accompanying software and computational code.
