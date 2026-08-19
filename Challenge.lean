import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Low-rank univariate sum of squares has no spurious second-order critical points

This is the statement surface of the Palomar submission for the Lean package
`LowRankUnivariateSOS`. It formalizes the rank-2 case of Theorem 1.1 of

* Benoît Legat, Chenyang Yuan, Pablo A. Parrilo,
  *Low-Rank Univariate Sum of Squares Has No Spurious Local Minima*,
  SIAM Journal on Optimization 33(3), 2023, pp. 2041–2061,
  [doi:10.1137/22M1516208](https://doi.org/10.1137/22M1516208),
  [arXiv:2205.11466](https://arxiv.org/abs/2205.11466).

## The informal statement

Fix an inner product `⟨·,·⟩` on real univariate polynomials. For a polynomial
`p` and a vector of polynomials `u = (u₁, …, u_r)`, the paper studies the
quadratically penalized Burer–Monteiro objective (equation (1.3))

  `f_p(u) = ‖σ(u) - p‖²`,  where `σ(u) = u₁² + ⋯ + u_r²`,

whose minimizers with `f_p(u) = 0` are exactly the decompositions of `p` as a
sum of `r` squares. Writing `A_u(v) = u₁v₁ + ⋯ + u_r v_r`, the first- and
second-order derivatives of `f_p` are (equations (3.1)–(3.4))

  `¼ ∇f_p(u)(v)   = ⟨A_u(v), σ(u) - p⟩`,
  `¼ ∇²f_p(u)(v,v) = ⟨σ(v), σ(u) - p⟩ + 2‖A_u(v)‖²`,

and `u` is a *second-order critical point* (SOCP, Definition 3.1) when the first
quantity vanishes and the second is nonnegative for every direction `v`.

**Theorem 1.1.** For every nonnegative univariate polynomial `p` and every
`r ≥ 2`, if `u` is a SOCP of `f_p`, then `f_p(u) = 0`; that is, every SOCP
(in particular every local minimum) is a global minimum.

## What is formalized

The formal statement below covers the rank `r = 2` case, which is the case the
paper's proof (Sections 3–5) treats: `u = (u₁, u₂)` is a `UPair`. The
hypothesis "`p` is nonnegative" is taken in the form `IsSOS p`, i.e. `p` is
itself a sum of two squares; for univariate real polynomials these two
conditions are classically equivalent, but that equivalence is not part of
this development. The formal theorem is slightly stronger than the paper's in
two respects: it holds for an arbitrary positive-definite bilinear form `B` on
the polynomial ring (the paper's proof is independent of the inner product),
and the SOCP conditions are imposed on the full polynomial ring rather than on
polynomials of bounded degree (a stronger criticality hypothesis, since it
quantifies over more directions `v`). The conclusion `σ(u) = p` is the
algebraic form of `f_p(u) = 0`: for a positive-definite `B`, the objective
`f_p(u) = B (σ(u) - p) (σ(u) - p)` vanishes exactly when `σ(u) = p`.
-/

noncomputable section

namespace LowRankUnivariateSOS

/-- Real univariate polynomials `ℝ[x]`. -/
abbrev Poly := Polynomial ℝ

/-- `UPair` is the rank-2 factor variable `u = (u₁, u₂)` of the paper: a pair of
 real univariate polynomials. -/
structure UPair where
  fst : Poly
  snd : Poly

/-- The quadratic map `σ(u) = u₁² + u₂²` of the paper (Section 2.1), i.e. the
 sum of squares represented by the rank-2 factor `u`. -/
def sigma2 (u : UPair) : Poly :=
  u.fst ^ 2 + u.snd ^ 2

/-- The linear map `A_u(v) = u₁v₁ + u₂v₂` of the paper (Section 3.1). -/
def A (u v : UPair) : Poly :=
  u.fst * v.fst + u.snd * v.snd

/-- The residual `σ(u) - p`. -/
def residual (p : Poly) (u : UPair) : Poly :=
  sigma2 u - p

/-- `IsSOS p` says that `p` is a sum of two squares, `p = q₁² + q₂²`. This is
 the hypothesis on the target polynomial `p` in the main theorem. -/
def IsSOS (p : Poly) : Prop :=
  ∃ q₁ q₂ : Poly, p = q₁ ^ 2 + q₂ ^ 2

/-- A real bilinear form `⟨·,·⟩` on `ℝ[x]`. The main theorem assumes that it
 is positive definite, so that it is an inner product. -/
abbrev DotForm := LinearMap.BilinForm ℝ Poly

section SocpDefs

variable (B : DotForm)

/-- The objective `f_p(u) = ⟨σ(u) - p, σ(u) - p⟩` of equation (1.3). -/
def objective (p : Poly) (u : UPair) : ℝ :=
  B (residual p u) (residual p u)

/-- First-order criticality `∇f_p(u) = 0`, written as in equation (3.3):
 `⟨A_u(v), σ(u) - p⟩ = 0` for every direction `v`. -/
def IsFOCP (p : Poly) (u : UPair) : Prop :=
  ∀ v : UPair, B (A u v) (residual p u) = 0

/-- The Hessian quadratic form `¼ ∇²f_p(u)(v, v) = ⟨σ(v), σ(u) - p⟩ + 2‖A_u(v)‖²`
 of equation (3.4). -/
def hessianTerm (p : Poly) (u v : UPair) : ℝ :=
  B (sigma2 v) (residual p u) + 2 * B (A u v) (A u v)

/-- `u` is a second-order critical point (SOCP) of `f_p` in the sense of
 Definition 3.1: `∇f_p(u) = 0` and `∇²f_p(u) ⪰ 0`. -/
def IsSOCP (p : Poly) (u : UPair) : Prop :=
  IsFOCP B p u ∧ ∀ v : UPair, 0 ≤ hessianTerm B p u v

end SocpDefs

section MainTheorem

variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]

/-- **Theorem 1.1 of the paper, rank `r = 2`.** Let `⟨·,·⟩` be any inner
 product on `ℝ[x]`, let `p` be a sum of two squares, and let `u = (u₁, u₂)` be a
 second-order critical point of `f_p(u) = ‖σ(u) - p‖²`. Then `σ(u) = p`, i.e.
 `u₁² + u₂² = p`, equivalently `f_p(u) = 0`; in particular `u` is a global
 minimizer of `f_p`. -/
theorem rankTwo_no_spurious_socp
    (p : Poly) (u : UPair)
    (hp : IsSOS p) (hsocp : IsSOCP B p u) :
    sigma2 u = p := by
  sorry

end MainTheorem

end LowRankUnivariateSOS
