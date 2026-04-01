import LowRankUnivariateSOS.UnivariateAlgebraCore
import LowRankUnivariateSOS.PeelingStep
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.List.Prime
import Mathlib.Data.Multiset.Filter
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

noncomputable section

namespace LowRankUnivariateSOS

/-- These zero and scaling identities are basic normalization lemmas for the
 factor-peeling recursion. They keep the later proofs focused on the paper's
 algebra rather than pair-coordinate bookkeeping. -/
@[simp] theorem zero_fst : (0 : UPair).fst = 0 :=
  rfl

@[simp] theorem zero_snd : (0 : UPair).snd = 0 :=
  rfl

@[simp] theorem scalePair_zero (u : UPair) : scalePair 0 u = 0 := by
  cases u with
  | mk fst snd =>
      change UPair.mk (0 * fst) (0 * snd) = UPair.mk 0 0
      simp

@[simp] theorem sigma2_zero : sigma2 (0 : UPair) = 0 := by
  simp [sigma2]

@[simp] theorem A_zero_left (u : UPair) : A 0 u = 0 := by
  simp [A]

@[simp] theorem A_zero_right (u : UPair) : A u 0 = 0 := by
  simp [A]

/-- Replacing each peeled factor by `X²` preserves coprimality with the reduced
 sum of squares, provided both the base factor and `X²` are coprime to that
 sum. This is the inductive coprimality invariant used in the peeling process. -/
private theorem peelTerminalScale_isCoprime {gBase q : Poly} {rs : List Poly}
    (hX : IsCoprime (Polynomial.X ^ 2) q)
    (hg : IsCoprime gBase q) :
    IsCoprime (peelTerminalScale gBase rs) q := by
  induction rs generalizing gBase with
  | nil =>
      simpa [peelTerminalScale] using hg
  | cons r rs ih =>
      have hg' : IsCoprime ((Polynomial.X ^ 2) * gBase) q :=
        hX.mul_left hg
      simpa [peelTerminalScale] using ih hg'

/-- The formal reason that `X` is coprime to the reduced sum of squares
 `σ(u₀)`: if `X` divided `σ(u₀)`, then `0` would be a real root of `σ(u₀)`,
 contradicting `\Cref{prop:no-real-roots}` for the reduced pair. -/
private theorem factor_peeling_X_coprime
    (u : UPair) (data : ReducedFactorization u) :
    IsCoprime Polynomial.X (sigma2 data.u0) := by
  have hnot_dvd : ¬ Polynomial.X ∣ sigma2 data.u0 := by
    intro hX
    have hroot : Polynomial.IsRoot (sigma2 data.u0) 0 := by
      have hX' : Polynomial.X - Polynomial.C (0 : ℝ) ∣ sigma2 data.u0 := by
        simpa using hX
      exact Polynomial.dvd_iff_isRoot.mp hX'
    exact (no_real_roots_sigma_reduced u data 0) hroot
  rcases EuclideanDomain.dvd_or_coprime Polynomial.X (sigma2 data.u0) Polynomial.irreducible_X with
    hX | hcop
  · exact (hnot_dvd hX).elim
  · exact hcop

/-- This theorem extracts the factor data needed for the general-case proof.
 Starting from the common factor `a` in `u = a·u₀`, it splits `a` into:
 a base factor `gBase` coprime to `σ(u₀)`, and a list `rs` of factors dividing
 `σ(u₀)` which must be peeled one by one. The terminal factor `g` is obtained by
 replacing each peeled factor by `X²`, mirroring the passage from condition
 (C3) in `\eqref{eq:prop_factored}`.

 Proof sketch: factor `a` into irreducibles with `normalizedFactors`, partition
 the factors into those dividing `σ(u₀)` and those that do not, define `gBase`
 from the latter, and prove coprimality using the no-common-prime-factor
 criterion. -/
theorem factor_peeling_decomposition
    (u : UPair) (data : ReducedFactorization u) (ha : data.a ≠ 0) :
    ∃ gBase g : Poly, ∃ rs : List Poly,
      gBase ≠ 0 ∧
        data.a = gBase * rs.prod ∧
        g = peelTerminalScale gBase rs ∧
        IsCoprime g (sigma2 data.u0) ∧
        ∀ r ∈ rs, r ∣ sigma2 data.u0 := by
  classical
  let sig : Poly := sigma2 data.u0
  let peeled : Multiset Poly :=
    (UniqueFactorizationMonoid.normalizedFactors data.a).filter (fun r => r ∣ sig)
  let keep : Multiset Poly :=
    (UniqueFactorizationMonoid.normalizedFactors data.a).filter (fun r => ¬ r ∣ sig)
  let rs : List Poly := peeled.toList
  let gBase : Poly := Polynomial.C data.a.leadingCoeff * keep.prod
  let g : Poly := peelTerminalScale gBase rs
  have hlead : data.a.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr ha
  have hC_ne_zero : Polynomial.C data.a.leadingCoeff ≠ 0 := by
    simpa using hlead
  have hkeep_ne_zero : keep.prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro hz
    have hz' : (0 : Poly) ∈ UniqueFactorizationMonoid.normalizedFactors data.a := by
      exact (by
        simpa [keep] using hz :
          (0 : Poly) ∈ UniqueFactorizationMonoid.normalizedFactors data.a ∧ ¬ (0 : Poly) ∣ sig).1
    exact UniqueFactorizationMonoid.zero_notMem_normalizedFactors data.a hz'
  have hgBase_ne_zero : gBase ≠ 0 := by
    exact mul_ne_zero hC_ne_zero hkeep_ne_zero
  have hsplit : peeled + keep = UniqueFactorizationMonoid.normalizedFactors data.a := by
    simpa [peeled, keep] using
      (Multiset.filter_add_not (p := fun r : Poly => r ∣ sig)
        (UniqueFactorizationMonoid.normalizedFactors data.a))
  have hXcop : IsCoprime Polynomial.X sig :=
    factor_peeling_X_coprime u data
  have hcop_gBase : IsCoprime gBase sig := by
    have hrel : IsRelPrime gBase sig := by
      refine (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hgBase_ne_zero).2 ?_
      intro d hdg hds hdprime
      have hC_unit : IsUnit (Polynomial.C data.a.leadingCoeff) := by
        exact Polynomial.isUnit_C.mpr hlead.isUnit
      have hdg' : d ∣ Polynomial.C data.a.leadingCoeff * keep.prod := by
        simpa [gBase] using hdg
      rcases hdprime.dvd_or_dvd hdg' with hdC | hdkeep
      · exact hdprime.not_unit (isUnit_of_dvd_unit hdC hC_unit)
      · have hkeep_not : ¬ d ∣ keep.prod := by
          have hlist : ∀ r ∈ keep.toList, ¬ d ∣ r := by
            intro r hr hd_r
            have hr_keep : r ∈ keep := by
              simpa using hr
            have hr_factor :
                r ∈ UniqueFactorizationMonoid.normalizedFactors data.a ∧ ¬ r ∣ sig := by
              simpa [keep] using hr_keep
            have hrirr : Irreducible r :=
              UniqueFactorizationMonoid.irreducible_of_normalized_factor r hr_factor.1
            have hassoc : Associated d r :=
              hdprime.irreducible.associated_of_dvd hrirr hd_r
            have hr_sig : r ∣ sig :=
              (hassoc.dvd_iff_dvd_left).1 hds
            exact hr_factor.2 hr_sig
          exact fun hdkeep' =>
            (Prime.not_dvd_prod hdprime hlist) (by simpa using hdkeep')
        exact hkeep_not hdkeep
    exact hrel.isCoprime
  have hcop_g : IsCoprime g sig := by
    have hXsq : IsCoprime (Polynomial.X ^ 2) sig := by
      simpa using hXcop.pow_left (m := 2)
    simpa [g] using peelTerminalScale_isCoprime hXsq hcop_gBase
  refine ⟨gBase, g, rs, hgBase_ne_zero, ?_, rfl, hcop_g, ?_⟩
  · calc
      data.a =
          Polynomial.C data.a.leadingCoeff *
            (UniqueFactorizationMonoid.normalizedFactors data.a).prod := by
        symm
        exact Polynomial.leadingCoeff_mul_prod_normalizedFactors data.a
      _ = Polynomial.C data.a.leadingCoeff * (peeled + keep).prod := by
        rw [hsplit]
      _ = Polynomial.C data.a.leadingCoeff * (peeled.prod * keep.prod) := by
        simp
      _ = gBase * peeled.prod := by
        simp [gBase]
        ac_rfl
      _ = gBase * rs.prod := by
        simp [rs]
  · intro r hr
    have hr_peeled : r ∈ peeled := by
      simpa [rs] using hr
    have hr_factor :
        r ∈ UniqueFactorizationMonoid.normalizedFactors data.a ∧ r ∣ sig := by
      simpa [peeled] using hr_peeled
    exact hr_factor.2

/-- One quadratic factor step produces the witness package required by the
 analytic peeling machinery. This is the local algebraic input to the recursive
 peeling argument. -/
theorem factor_peeling_one_step
    (u : UPair) (data : ReducedFactorization u) :
      {gStart gNext : Poly} →
        QuadraticFactorStep data.u0 gStart gNext →
          HasPeelingWitness u (scalePair gStart data.u0) (scalePair gNext data.u0) := by
  intro gStart gNext hfg
  exact hasPeelingWitness_of_factor_step data.eq_scale data.reduced_coprime hfg

/-- From the decomposition of the bad common factor into peelable pieces, we
 obtain a full peeling schedule ending at some factor `g` that is coprime to
 `σ(u₀)`. This is the formal counterpart of iteratively peeling the factors of
 `h` in the proof of `\Cref{prop:second_order_property_factor}`. -/
theorem factor_peeling_schedule
    (u : UPair) (data : ReducedFactorization u) (ha : data.a ≠ 0) :
    ∃ g : Poly, g ≠ 0 ∧ IsCoprime g (sigma2 data.u0) ∧
      PeelingSchedule u data.u0 data.a g := by
  rcases factor_peeling_decomposition u data ha with
    ⟨gBase, g, rs, hgBase, hscale, hgdef, hcopg, hrs⟩
  refine ⟨g, ?_, hcopg, ?_⟩
  · rw [hgdef]
    exact peelTerminalScale_ne_zero hgBase
  rw [hscale, hgdef]
  exact peelingSchedule_of_factors hrs (fun hfg => factor_peeling_one_step u data hfg)

/-- The scalar peeling schedule induces a path of scaled pairs from the
 original factorization `u = a·u₀` to the coprime target `g·u₀`. -/
theorem factor_peeling_path
    (u : UPair) (data : ReducedFactorization u) (ha : data.a ≠ 0) :
    ∃ g : Poly, g ≠ 0 ∧ IsCoprime g (sigma2 data.u0) ∧
      PeelingPath u u (scalePair g data.u0) := by
  rcases factor_peeling_schedule u data ha with ⟨g, hg, hcopg, hsched⟩
  refine ⟨g, hg, hcopg, ?_⟩
  simpa [data.eq_scale] using hsched.toPath

section DotForm

variable {B : DotForm}

/-- This is the formal output of the whole peeling construction. At any SOCP,
 after peeling all bad factors we obtain a nonzero `g` coprime to `σ(u₀)` such
 that the residual is orthogonal to `im(A_{g u₀})`. This is exactly the
 transformed-image orthogonality promised by the paper's general-case argument
 around `\Cref{prop:second_order_property_factor}`. -/
theorem factor_peeling_image_orthogonal
    (p : Poly) (u : UPair)
    (hsocp : IsSOCP B p u)
    (data : ReducedFactorization u) (ha : data.a ≠ 0) :
    ∃ g : Poly, g ≠ 0 ∧ IsCoprime g (sigma2 data.u0) ∧
      ImageOrthogonalResidual B p (scalePair data.a data.u0) (scalePair g data.u0) := by
  have hstart : ImageOrthogonalResidual B p u u :=
    image_orthogonal_self_of_focp (B := B) hsocp.1
  rcases factor_peeling_path u data ha with ⟨g, hg, hcopg, hpath⟩
  have himg : ImageOrthogonalResidual B p u (scalePair g data.u0) :=
    image_orthogonal_of_peeling_path (B := B) hsocp hstart hpath
  refine ⟨g, hg, hcopg, ?_⟩
  simpa [data.eq_scale] using himg

end DotForm

end LowRankUnivariateSOS
