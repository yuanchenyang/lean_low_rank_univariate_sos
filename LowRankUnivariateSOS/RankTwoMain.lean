import LowRankUnivariateSOS.UnivariateAlgebra
import LowRankUnivariateSOS.UnivariateSOS

noncomputable section

namespace LowRankUnivariateSOS

section DotForm

variable {B : DotForm}

/-- If the residual already vanishes, then it is trivially orthogonal to every
 image space that appears later in the argument. This is used only in the zero
 branch above. -/
private theorem imageOrthogonalResidual_of_residual_eq_zero
    {p : Poly} {u uImg : UPair}
    (hres : residual p u = 0) :
    ImageOrthogonalResidual B p u uImg := by
  intro q hq
  simp [hres]

/-- This theorem isolates the output of the factor-peeling stage needed by the
 final proof: from a nonzero reduced factorization `u = a·u₀`, one obtains a
 new factor `g` coprime to `σ(u₀)` such that the residual is orthogonal to
 `im(A_{g u₀})`. This is the formal version of the transformed condition (C3)
 after peeling all bad factors. -/
theorem factor_peeling_certificate_step
    (p : Poly) (u : UPair) :
    IsSOS p → IsSOCP B p u →
      (data : ReducedFactorization u) → data.a ≠ 0 →
      ∃ a g : Poly, ∃ u0 : UPair,
        u = scalePair a u0 ∧ g ≠ 0 ∧ IsCoprime u0.fst u0.snd ∧
          IsCoprime g (sigma2 u0) ∧
            ImageOrthogonalResidual B p (scalePair a u0) (scalePair g u0) := by
  intro hp hsocp data ha
  rcases factor_peeling_image_orthogonal (B := B) p u hsocp data ha with
    ⟨g, hg, hcopg, himg⟩
  refine ⟨data.a, g, data.u0, data.eq_scale, hg, data.reduced_coprime, hcopg, himg⟩

end DotForm

section DotFormPosDef

variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]

/-- Degenerate zero-factor case. If `u = 0` is a SOCP for an SOS polynomial
 `p`, then the Hessian inequality in the direction of any SOS decomposition of
 `p` forces the residual to vanish. This discharges the exceptional branch
 where the common factor `a` in `u = a·u₀` is zero. -/
private theorem residual_eq_zero_of_zero_socp
    {p : Poly} (hp : IsSOS p) (hsocp : IsSOCP B p 0) :
    residual p 0 = 0 := by
  rcases hp with ⟨q₁, q₂, rfl⟩
  let v : UPair := ⟨q₁, q₂⟩
  have hhess : 0 ≤ hessianTerm B (sigma2 v) 0 v := hsocp.2 v
  have hhess' : 0 ≤ -B (sigma2 v) (sigma2 v) := by
    simpa [hessianTerm, residual, v] using hhess
  have hle : objective B (sigma2 v) 0 ≤ 0 := by
    have hobj : objective B (sigma2 v) 0 = B (sigma2 v) (sigma2 v) := by
      simp [objective, residual]
    rw [hobj]
    linarith
  have hge : 0 ≤ objective B (sigma2 v) 0 := objective_nonneg (B := B) _ _
  have hobj : objective B (sigma2 v) 0 = 0 := by
    linarith
  exact (objective_eq_zero_iff_residual_eq_zero (B := B)).mp hobj

/-- This is the final reduction to the `h = 1` case. It packages the proof's
 two main algebraic ingredients:
 1. factor peeling, which produces a coprime transformed image;
 2. the hgroup lemma, which writes `p` in the form `g q + s σ(u₀)`.
 Together they yield the decomposition required by the abstract `h = 1`
 residual-vanishing lemma. -/
theorem rankTwo_factored_h1_setup
    (p : Poly) (u : UPair) :
    IsSOS p → IsSOCP B p u →
      ∃ a g q s : Poly, ∃ u0 : UPair,
        u = scalePair a u0 ∧ g ≠ 0 ∧ IsCoprime u0.fst u0.snd ∧ IsSOS s ∧
          p = g * q + s * sigma2 u0 ∧
            ImageOrthogonalResidual B p (scalePair a u0) (scalePair g u0) := by
  intro hp hsocp
  let data := gcd_sigma_decomposition u
  by_cases ha : data.a = 0
  · have hu0 : u = 0 := by
      calc
        u = scalePair data.a data.u0 := data.eq_scale
        _ = 0 := by simp [ha]
    have hsocp0 : IsSOCP B p 0 := by
      simpa [hu0] using hsocp
    have hres0 : residual p 0 = 0 :=
      residual_eq_zero_of_zero_socp (B := B) hp hsocp0
    have hp0 : p = 0 := by
      have hp0' : -p = 0 := by
        simpa [residual, sub_eq_add_neg] using hres0
      exact neg_eq_zero.mp hp0'
    refine ⟨0, 1, 0, 0, data.u0, ?_, one_ne_zero, data.reduced_coprime, ?_, ?_, ?_⟩
    · simpa [ha] using data.eq_scale
    · exact ⟨0, 0, by simp⟩
    · simp [hp0]
    · simpa [hp0, residual] using
        (imageOrthogonalResidual_of_residual_eq_zero (B := B)
          (u := 0) (uImg := scalePair 1 data.u0) hres0)
  · rcases factor_peeling_certificate_step (B := B) p u hp hsocp data ha with
      ⟨a, g, u0, hu, hg, hcop, hcopg, himg⟩
    rcases hgroup_affine g p (sigma2 u0) hp (sigma2_isSOS u0) hcopg with ⟨s, q, hs, hpq⟩
    exact ⟨a, g, q, s, u0, hu, hg, hcop, hs, hpq, himg⟩

/-- Main theorem, corresponding to `\Cref{thm:main}` specialized to the rank-2
 formal model. Every SOCP of the quadratic penalty objective has zero residual,
 hence `σ(u) = p` and the point is globally optimal.

 Proof sketch: reduce to `rankTwo_factored_h1_setup`, then invoke the abstract
 factored `h = 1` argument from `FactoredCase`, which combines first-order
 orthogonality, second-order nonnegativity, the hgroup decomposition, and the
 factor-peeling transport. -/
theorem rankTwo_no_spurious_socp
    (p : Poly) (u : UPair)
    (hp : IsSOS p) (hsocp : IsSOCP B p u) :
    sigma2 u = p := by
  rcases rankTwo_factored_h1_setup (B := B) p u hp hsocp with
    ⟨a, g, q, s, u0, hu, hg, hcop, hs, hpq, himg⟩
  have hsocp' : IsSOCP B p (scalePair a u0) := by
    simpa [hu] using hsocp
  have hres : residual p u = 0 := by
    simpa [hu] using
      factored_h1_residual_eq_zero (B := B) a g p q s u0 hg hcop hs hpq himg hsocp'
  exact sub_eq_zero.mp (by simpa [residual] using hres)


end DotFormPosDef

end LowRankUnivariateSOS
