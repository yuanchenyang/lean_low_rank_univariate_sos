import Mathlib.Tactic.Linarith
import LowRankUnivariateSOS.Socp
import LowRankUnivariateSOS.H1Case

noncomputable section

namespace LowRankUnivariateSOS

/-- If a vector is killed by `A_{g u₀}` with `g ≠ 0`, then it is already killed
 by `A_{a u₀}` for any other scale `a`. This is the formal reason that kernel
 cone terms produced in the reduced `h = 1` model can be reused for the
 original factorization. -/
theorem inKerA_of_shared_reduced {a g : Poly} {u0 w : UPair}
    (hg : g ≠ 0) (hker : InKerA (scalePair g u0) w) :
    InKerA (scalePair a u0) w := by
  rw [InKerA, A_scalePair_left] at hker ⊢
  rcases mul_eq_zero.mp hker with h | h
  · exact (hg h).elim
  · simp [h]

/-- Converts the explicit `h = 1` decomposition `p = g q + s σ(u₀)` into the
 image-plus-cone form needed by the abstract SOCP argument, but now relative to
 the original scale `a·u₀` instead of the reduced scale `g·u₀`. -/
theorem factored_h1_decomposition_to_original
    (a g p q s : Poly) (u0 : UPair)
    (hg : g ≠ 0)
    (hcop : IsCoprime u0.fst u0.snd)
    (hs : IsSOS s)
    (hp : p = g * q + s * sigma2 u0) :
    ∃ imgPart : Poly, ∃ ws : Finset UPair,
      InImageA (scalePair g u0) imgPart ∧
        (∀ w ∈ ws, InKerA (scalePair a u0) w) ∧
        p = imgPart + ws.sum sigma2 := by
  rcases inImagePlusSigmaKerCone_of_h1_data g p q s u0 hcop hs hp with ⟨v, ws, hker, hp'⟩
  refine ⟨A (scalePair g u0) v, ws, ?_, ?_, ?_⟩
  · exact ⟨v, rfl⟩
  · intro w hw
    exact inKerA_of_shared_reduced hg (hker w hw)
  · exact hp'

section DotForm

variable {B : DotForm}

/-- The residual at `u` is orthogonal to the image of the transformed pair `uImg`. -/
def ImageOrthogonalResidual (B : DotForm) (p : Poly) (u uImg : UPair) : Prop :=
  ∀ q : Poly, InImageA uImg q → B q (residual p u) = 0

/-- Finite sums of `σ(w)` pair against the residual term-by-term. This is a
 bookkeeping lemma used when summing the Hessian inequalities over several
 kernel directions. -/
private theorem dot_sum_left (ws : Finset UPair) (p : Poly) :
    B (ws.sum sigma2) p = ws.sum (fun w => B (sigma2 w) p) := by
  classical
  refine Finset.induction_on ws ?_ ?_
  · simp
  · intro w ws hw ih
    calc
      B ((insert w ws).sum sigma2) p = B (sigma2 w + ws.sum sigma2) p := by
        simp [hw]
      _ = B (sigma2 w) p + B (ws.sum sigma2) p := by
        simp
      _ = B (sigma2 w) p + ws.sum (fun w => B (sigma2 w) p) := by
        rw [ih]
      _ = (insert w ws).sum (fun w => B (sigma2 w) p) := by
        simp [hw]

end DotForm

section DotFormPosDef

variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]

/-- This is the abstract certificate step behind condition (C2). If `p`
 decomposes as an image term for some transformed pair `uImg` plus a sum of
 kernel squares for the original pair `u`, and if the residual is orthogonal to
 `im(A_{uImg})`, then the SOCP inequalities force the objective to be zero.
 The proof is exactly the paper's image-plus-cone argument: the image part dies
 by first-order criticality, the kernel terms are nonnegative by second-order
 criticality, and `⟨σ(u),σ(u)-p⟩=0` closes the estimate. -/
theorem transformed_image_plus_cone_implies_objective_eq_zero {p : Poly} {u uImg : UPair}
    (hsocp : IsSOCP B p u)
    (himg : ImageOrthogonalResidual B p u uImg)
    (hdecomp : ∃ imgPart : Poly, ∃ ws : Finset UPair,
      InImageA uImg imgPart ∧ (∀ w ∈ ws, InKerA u w) ∧ p = imgPart + ws.sum sigma2) :
    objective B p u = 0 := by
  rcases hdecomp with ⟨imgPart, ws, himgPart, hker, hp⟩
  let r := residual p u
  have hImg : B imgPart r = 0 := himg imgPart himgPart
  have hsum_ge : 0 ≤ ws.sum (fun w => B (sigma2 w) r) := by
    refine Finset.sum_nonneg ?_
    intro w hw
    have hwker : A u w = 0 := hker w hw
    have hhess : 0 ≤ hessianTerm B p u w := hsocp.2 w
    have hAu : B (A u w) (A u w) = 0 := by
      simp [hwker]
    have hhess' : 0 ≤ B (sigma2 w) (residual p u) := by
      simpa [hessianTerm, hAu] using hhess
    exact hhess'
  have hp_ge : 0 ≤ B p r := by
    rw [hp, dot_add_left, dot_sum_left]
    linarith
  have hsigma_zero : B (sigma2 u) r = 0 := focp_sigma2_residual_eq_zero (B := B) hsocp.1
  have hobj_formula : objective B p u = -(B p r) := by
    subst r
    have hsigma_zero' : B (sigma2 u) (sigma2 u - p) = 0 := by
      simpa [residual] using hsigma_zero
    calc
      objective B p u = B (sigma2 u - p) (sigma2 u - p) := by
        simp [objective, residual]
      _ = B (sigma2 u) (sigma2 u - p) - B p (sigma2 u - p) := by
        simp only [sub_eq_add_neg, dot_add_left, dot_neg_left]
      _ = -B p (sigma2 u - p) := by
        rw [hsigma_zero', zero_sub]
      _ = -(B p (residual p u)) := by
        simp [residual]
  have hle : objective B p u ≤ 0 := by
    rw [hobj_formula]
    linarith
  have hge : 0 ≤ objective B p u := objective_nonneg (B := B) p u
  linarith

/-- This is the factor-rescaled form of the paper's `h = 1` decomposition.
 Starting from `p = g q + s σ(u₀)`, it rewrites `p` as
 `img(A_{g u₀}) + cone(σ(ker(A_{a u₀})))`, which is the form needed by the
 abstract image-plus-cone lemma above. -/
theorem factored_h1_residual_eq_zero
    (a g p q s : Poly) (u0 : UPair)
    (hg : g ≠ 0)
    (hcop : IsCoprime u0.fst u0.snd)
    (hs : IsSOS s)
    (hp : p = g * q + s * sigma2 u0)
    (himg : ImageOrthogonalResidual B p (scalePair a u0) (scalePair g u0))
    (hsocp : IsSOCP B p (scalePair a u0)) :
    residual p (scalePair a u0) = 0 := by
  exact (objective_eq_zero_iff_residual_eq_zero (B := B)).mp
    (transformed_image_plus_cone_implies_objective_eq_zero (B := B) hsocp himg
      (factored_h1_decomposition_to_original a g p q s u0 hg hcop hs hp))

end DotFormPosDef

end LowRankUnivariateSOS
