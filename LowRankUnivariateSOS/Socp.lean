import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import LowRankUnivariateSOS.PolynomialModel

noncomputable section

namespace LowRankUnivariateSOS

/-- The development is abstract over an arbitrary real bilinear form on
 polynomials. In the paper this corresponds to the statement that the argument
 works for any inner product used to define the penalty `f_p`. We only use
 positivity of the associated quadratic map, not any special coefficient model. -/
abbrev DotForm := LinearMap.BilinForm ℝ Poly

section BilinearLemmas

variable {B : DotForm}

/-- The next simp lemmas are the algebraic identities saying that a bilinear
 form behaves linearly in each argument. They are used repeatedly when
 expanding the gradient and Hessian expressions from Definition
 `\ref{def:socp}`. -/
@[simp] theorem dot_add_left (p q r : Poly) :
    B (p + q) r = B p r + B q r := by
  simp

@[simp] theorem dot_add_right (p q r : Poly) :
    B p (q + r) = B p q + B p r := by
  simp

@[simp] theorem dot_smul_left (a : ℝ) (p q : Poly) :
    B (a • p) q = a * B p q := by
  simp [smul_eq_mul]

@[simp] theorem dot_smul_right (a : ℝ) (p q : Poly) :
    B p (a • q) = a * B p q := by
  simp [smul_eq_mul]

@[simp] theorem dot_zero_left (p : Poly) : B 0 p = 0 := by
  simp

@[simp] theorem dot_zero_right (p : Poly) : B p 0 = 0 := by
  simp

@[simp] theorem dot_neg_left (p q : Poly) :
    B (-p) q = -B p q := by
  simp

@[simp] theorem dot_neg_right (p q : Poly) :
    B p (-q) = -B p q := by
  simp

end BilinearLemmas

section SocpDefs

variable (B : DotForm)

/-- The objective `f_p(u) = ⟨σ(u)-p, σ(u)-p⟩` from equation
 `\eqref{eq:nonconvex-obj}`. -/
def objective (p : Poly) (u : UPair) : ℝ :=
  B (residual p u) (residual p u)

/-- The first-order critical point condition written in the paper's form
 `⟨A_u(v), σ(u)-p⟩ = 0` for every direction `v`; see equation `\eqref{eq:gradA}`. -/
def IsFOCP (p : Poly) (u : UPair) : Prop :=
  ∀ v : UPair, B (A u v) (residual p u) = 0

/-- The quadratic form appearing in the Hessian condition
 `\eqref{eq:hessA}`. For a SOCP, this quantity must be nonnegative in every
 direction `v`. -/
def hessianTerm (p : Poly) (u v : UPair) : ℝ :=
  B (sigma2 v) (residual p u) + 2 * B (A u v) (A u v)

/-- Second-order criticality in exactly the sense of Definition
 `\ref{def:socp}`: the gradient vanishes and the Hessian quadratic form is
 nonnegative in every direction. -/
def IsSOCP (p : Poly) (u : UPair) : Prop :=
  IsFOCP B p u ∧ ∀ v : UPair, 0 ≤ hessianTerm B p u v

end SocpDefs

/-- Substituting `v = u` into `A_u(v)` gives `σ(u)`. This is the elementary
 identity that lets the FOCP condition immediately say something about the
 objective itself. -/
@[simp] theorem A_self_eq_sigma2 (u : UPair) : A u u = sigma2 u := by
  simp [A, sigma2, pow_two]

/-- Any FOCP satisfies `⟨σ(u), σ(u)-p⟩ = 0`. This is equation
 `\eqref{eq:gradA}` evaluated at the special direction `v = u`, and it is used
 throughout the certificate-style arguments. -/
theorem focp_sigma2_residual_eq_zero {p : Poly} {u : UPair} (h : IsFOCP B p u) :
    B (sigma2 u) (residual p u) = 0 := by
  simpa [A_self_eq_sigma2] using h u

section Positivity

variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]

/-- The objective is always nonnegative because it is the quadratic form
 associated to a positive-definite bilinear form, evaluated at the residual. -/
theorem objective_nonneg (p : Poly) (u : UPair) : 0 ≤ objective B p u := by
  simpa [objective, LinearMap.BilinMap.toQuadraticMap_apply] using
    (Fact.out : B.toQuadraticMap.PosDef).nonneg (residual p u)

/-- For a positive-definite bilinear form, the objective vanishes exactly when
 the residual vanishes. This is the formal bridge from the analytic statement
 `f_p(u)=0` to the algebraic statement `σ(u)=p`. -/
theorem objective_eq_zero_iff_residual_eq_zero {p : Poly} {u : UPair} :
    objective B p u = 0 ↔ residual p u = 0 := by
  have hani : B.toQuadraticMap.Anisotropic :=
    (Fact.out : B.toQuadraticMap.PosDef).anisotropic
  constructor
  · intro h
    exact (QuadraticMap.Anisotropic.eq_zero_iff hani).mp (by
      simpa [objective, LinearMap.BilinMap.toQuadraticMap_apply] using h)
  · intro h
    simp [objective, h]

end Positivity

end LowRankUnivariateSOS
