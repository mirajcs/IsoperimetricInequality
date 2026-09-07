---
title: 'IsoperimetricInequality: A Lean 4 formalization of the planar isoperimetric inequality via Fourier series'
tags:
  - Lean 4
  - Mathlib
  - formalized mathematics
  - interactive theorem proving
  - Fourier analysis
  - isoperimetric inequality
  - differential geometry
authors:
  - name: Miraj Samarakkody
    orcid: 0000-0003-4750-4268
    affiliation: 1
affiliations:
  - name: Tougaloo College, MS, USA
    index: 1
date: 6 September 2026
bibliography: paper.bib
---

# Summary

`IsoperimetricInequality` is a formalization, in the [Lean 4](https://lean-lang.org)
proof assistant [@moura2021lean] and its mathematical library Mathlib
[@mathlib2020], of the classical planar isoperimetric inequality: among all simple
closed $C^1$ curves of a given perimeter $L$, none encloses more area than the
circle of that perimeter, so the enclosed area $A$ satisfies

$$ A \le \frac{L^2}{4\pi}. $$

The development follows the Fourier-analytic argument of Adolf Hurwitz
[@hurwitz1902; @osserman1978]. It reparametrizes a curve over $[0, 2\pi]$,
expands its coordinate functions as trigonometric (Fourier) series, and applies
Parseval's identity together with Wirtinger's inequality and the arithmetic
mean--geometric mean inequality to bound the area. Every step is checked by
Lean's kernel against Mathlib, so the result is a machine-verified theorem with no
appeal to informal reasoning.

The repository is organized into two files. `IsoperimetricInequality/Basic.lean`
builds the required real Fourier analysis from first principles: it defines the
trigonometric series $f(x) = \tfrac{a_0}{2} + \sum_{n\ge 1}(a_n\cos nx + b_n\sin
nx)$, proves the orthogonality relations for $\{\cos nx, \sin nx\}$ on
$[-\pi,\pi]$, establishes uniform convergence and term-by-term differentiability
of the series under an absolutely summable coefficient hypothesis (a Weierstrass
$M$-test argument), and derives **Parseval's theorem** (`Parsevals_thm`) and the
integral form of **Wirtinger's inequality** (`Wirtingers_inequality`).
`IsoperimetricInequality/Adolf_Hurwitz_proof.lean` defines a structure
`SimpleClosedC1Curve` for simple closed $C^1$ curves, the shoelace `area`
functional, `arcLength`/`perimeter`, and the predicate `IsArcLengthParametrized`,
and then assembles the chain of lemmas
(`area_parametrized` $\to$ `area_simplified` via integration by parts $\to$
`area_inequality` via AM--GM $\to$ `addition_ineq` via Wirtinger $\to$
`isoperimetric_inequality`) that yields the final bound `area γ 0 γ.length ≤
γ.length ^ 2 / (4 * Real.pi)`.

# Statement of need

The isoperimetric inequality is one of the oldest problems in mathematics and a
standard example in courses on the calculus of variations, Fourier analysis, and
differential geometry [@osserman1978]. Despite this prominence, and despite
several distinct classical proofs, the planar case had not been available as a
reusable, fully checked theorem in Mathlib. Formalized mathematics libraries grow
by accumulating exactly such landmark results together with the intermediate
infrastructure they require, and this project contributes both.

The reusable infrastructure is the main point of need. Mathlib's existing Fourier
material is centred on the complex exponential basis $e^{inx}$ and the
$L^2$ theory of `fourierBasis`. The present development instead works with the
real $\{\cos, \sin\}$ series as a concrete pointwise-convergent object, proves
that the series may be differentiated term by term, and gives Parseval and
Wirtinger identities in the elementary $\int_{-\pi}^{\pi}$ form that appears in
textbooks [@steinshakarchi2003]. This formulation is directly usable in
downstream arguments about periodic functions, boundary-value problems, and
inequalities of Poincaré type, independently of the isoperimetric application.

More broadly, the project serves as a worked, self-contained case study for
students and practitioners of interactive theorem proving: it shows how a
multi-step analytic proof, combining measure theory, uniform limits of
derivatives, infinite sums (`tsum`), and elementary inequalities, is structured
and discharged in Lean 4, and it can be read alongside the informal proof as a
teaching resource. The formalization is continuously integrated (the Lean build,
Mathlib cache, and API documentation are produced by GitHub Actions) and is
archived on Zenodo [@samarakkody_zenodo].

# Functionality and scope

The top-level theorem `isoperimetric_inequality` is stated for a
`SimpleClosedC1Curve 2` and concludes $A \le L^2/(4\pi)$ for the shoelace area
$A$. Its proof reduces the geometric statement to the analytic core through the
lemma chain listed above, and the Fourier facts it consumes — the Parseval and
Wirtinger integral identities for the reparametrized coordinate function, its
zero-mean (centroid) normalization, and the arc-length constraint
$(f')^2 + (g')^2 = (L/2\pi)^2$ — are provided as explicit hypotheses that are
instances of the general theorems proved in `Basic.lean`. This keeps the
geometric and analytic layers cleanly separated.

Current limitations, which also mark natural directions for future work:

- The characterization of the equality case (the bound is attained **iff** the
  curve is a circle) is not yet formalized.
- The coordinate Fourier expansion is supplied through the Parseval/Wirtinger
  hypotheses of the main theorem rather than constructed from a convergence
  theorem for the specific reparametrized curve; connecting the two would remove
  those hypotheses.
- The result is restricted to $C^1$ curves; the rectifiable / bounded-variation
  generalization is left open.

The development targets Lean `v4.27.0` and Mathlib `v4.27.0`, builds with
`lake build`, and its documentation is generated with `doc-gen4`.

# Acknowledgements

We thank the Lean community and the Mathlib maintainers for the library and
tooling that made this formalization possible. 


# References
