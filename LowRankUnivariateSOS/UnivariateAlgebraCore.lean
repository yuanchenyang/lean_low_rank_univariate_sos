import LowRankUnivariateSOS.H1Case
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.EuclideanDomain

noncomputable section

namespace LowRankUnivariateSOS

/-- `ReducedFactorization u` is the first half of the decomposition from
 `\Cref{prop:decomp}`: we split `u = a · u₀`, where `a` is the common factor and
 the reduced pair `u₀` is coprime. The later files further split `a` into the
 good factor `g` and the peelable factor `h`. -/
structure ReducedFactorization (u : UPair) where
  a : Poly
  u0 : UPair
  eq_scale : u = scalePair a u0
  reduced_coprime : IsCoprime u0.fst u0.snd

/-- Predicate expressing the paper's statement that `σ(u₀)` has no real roots;
 compare `\Cref{prop:no-real-roots}`. -/
def SigmaReducedNoRealRoots (u0 : UPair) : Prop :=
  ∀ x : ℝ, ¬ Polynomial.IsRoot (sigma2 u0) x

/-- Concrete construction of the reduced factorization `u = a·u₀` by taking
 `a = gcd(u₁,u₂)`. This is the formal version of the first decomposition step in
 `\Cref{prop:decomp}`. The proof is Bézout/gcd bookkeeping. -/
def gcd_sigma_decomposition
    (u : UPair) :
    ReducedFactorization u := by
  by_cases hsnd : u.snd = 0
  · refine
      { a := u.fst
        u0 := ⟨1, 0⟩
        eq_scale := ?_
        reduced_coprime := ?_ }
    · apply UPair.ext <;> simp [scalePair, hsnd]
    · simpa using (isCoprime_one_left : IsCoprime (1 : Poly) 0)
  · refine
      { a := gcd u.fst u.snd
        u0 := ⟨u.fst / gcd u.fst u.snd, u.snd / gcd u.fst u.snd⟩
        eq_scale := ?_
        reduced_coprime := ?_ }
    · apply UPair.ext
      · simpa [scalePair] using
          (EuclideanDomain.mul_div_cancel'
            (gcd_ne_zero_of_right hsnd) (gcd_dvd_left u.fst u.snd)).symm
      · simpa [scalePair] using
          (EuclideanDomain.mul_div_cancel'
            (gcd_ne_zero_of_right hsnd) (gcd_dvd_right u.fst u.snd)).symm
    · simpa using (isCoprime_div_gcd_div_gcd hsnd :
          IsCoprime (u.fst / gcd u.fst u.snd) (u.snd / gcd u.fst u.snd))

/-- If `u₁` and `u₂` are coprime, then `σ(u)=u₁²+u₂²` has no real root.
 This is exactly the argument in `\Cref{prop:no-real-roots}`: a real zero of a
 sum of two squares forces both coordinates to vanish at that point, hence they
 share the linear factor `X-C x`, contradicting coprimality. -/
theorem sigma2_not_isRoot_of_coprime
    (u : UPair) (hu : IsCoprime u.fst u.snd) (x : ℝ) :
    ¬ Polynomial.IsRoot (sigma2 u) x := by
  intro hsigma
  have hsum : u.fst.eval x ^ 2 + u.snd.eval x ^ 2 = 0 := by
    simpa [Polynomial.IsRoot, sigma2] using hsigma
  have hsquares : u.fst.eval x ^ 2 = 0 ∧ u.snd.eval x ^ 2 = 0 :=
    (add_eq_zero_iff_of_nonneg (sq_nonneg (u.fst.eval x)) (sq_nonneg (u.snd.eval x))).mp hsum
  have hroot_fst : Polynomial.IsRoot u.fst x := by
    simpa [Polynomial.IsRoot] using (sq_eq_zero_iff.mp hsquares.1)
  have hroot_snd : Polynomial.IsRoot u.snd x := by
    simpa [Polynomial.IsRoot] using (sq_eq_zero_iff.mp hsquares.2)
  have hdiv_fst : Polynomial.X - Polynomial.C x ∣ u.fst :=
    Polynomial.dvd_iff_isRoot.mpr hroot_fst
  have hdiv_snd : Polynomial.X - Polynomial.C x ∣ u.snd :=
    Polynomial.dvd_iff_isRoot.mpr hroot_snd
  have hunit : IsUnit (Polynomial.X - Polynomial.C x) :=
    hu.isUnit_of_dvd' hdiv_fst hdiv_snd
  exact Polynomial.not_isUnit_X_sub_C x hunit

/-- The reduced pair produced by `gcd_sigma_decomposition` satisfies the
 no-real-roots conclusion of `\Cref{prop:no-real-roots}`. This is an immediate
 corollary of the previous coprime lemma. -/
theorem no_real_roots_sigma_reduced
    (u : UPair) (data : ReducedFactorization u) :
    SigmaReducedNoRealRoots data.u0 := by
  intro x
  exact sigma2_not_isRoot_of_coprime data.u0 data.reduced_coprime x

/-- `σ(u)` is itself a sum of two squares by definition. This trivial remark is
 used as the `q ∈ Σ` input to the hgroup lemma. -/
theorem sigma2_isSOS (u : UPair) : IsSOS (sigma2 u) := by
  exact ⟨u.fst, u.snd, rfl⟩

end LowRankUnivariateSOS
