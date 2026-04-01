import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LowRankUnivariateSOS.FactoredCase

noncomputable section

namespace LowRankUnivariateSOS

/-- The first algebraic lemmas in this file simply expand the pair operations
 used in the paper's peeling identities. They let Lean normalize expressions
 such as `A_u(v_η)` and `σ(v_η)` into the polynomial formulas appearing in
 `\eqref{eq:Au-identity-factored}` and `\eqref{eq:sig-identity-factored}`. -/
@[simp] theorem add_fst (u v : UPair) : (u + v).fst = u.fst + v.fst :=
  rfl

@[simp] theorem add_snd (u v : UPair) : (u + v).snd = u.snd + v.snd :=
  rfl

@[simp] theorem A_add_right (u v w : UPair) :
    A u (v + w) = A u v + A u w := by
  simp [A]
  ring

@[simp] theorem A_smul_left (a : ℝ) (u v : UPair) :
    A (a • u) v = a • A u v := by
  simp [A, Polynomial.smul_eq_C_mul]
  ring_nf

@[simp] theorem A_perpPair_right (t : Poly) (u v : UPair) :
    A (perpPair t u) (perpPair 1 v) = t * A u v := by
  simp [A, perpPair]
  ring

@[simp] theorem A_perpPair_self (t : Poly) (u : UPair) :
    A u (perpPair t u) = 0 := by
  simp [A, perpPair]
  ring

@[simp] theorem sigma2_add (u v : UPair) :
    sigma2 (u + v) = sigma2 u + 2 * A u v + sigma2 v := by
  simp [sigma2, A, pow_two]
  ring

/-- A `PeelingStepWitness` packages one quadratic family `v_η` from the proof
 of `\Cref{prop:second_order_property_factor}`. The key data are:
 `qQuad`, whose pairing with the residual is already known to vanish from the
 previous stage; the constant `A_u(v_η)` term; and the exact quadratic expansion
 of `σ(v_η)` in the parameter `η`. -/
structure PeelingStepWitness (u uImgPrev : UPair) (q : Poly) where
  qQuad : Poly
  sigmaConst : Poly
  aConst : Poly
  quad_in_prev_image : InImageA uImgPrev qQuad
  family : ℝ → UPair
  A_const : ∀ η : ℝ, A u (family η) = aConst
  sigma_eq : ∀ η : ℝ,
    sigma2 (family η) = (η ^ 2 : ℝ) • qQuad + (2 * η : ℝ) • q + sigmaConst

/-- `RotatedPeelingData` is the paper-friendly way to build a peeling witness.
 The pair `quad` is the pure peeling direction, `const` is the correction term,
 `quad` is orthogonal to `u`, its square already lies in the previous image,
 and the mixed term is exactly the target polynomial `q`. -/
structure RotatedPeelingData (u uImgPrev : UPair) (q : Poly) where
  quad : UPair
  const : UPair
  quad_orth : InKerA u quad
  quad_in_prev_image : InImageA uImgPrev (sigma2 quad)
  cross_eq : A quad const = q

/-- `HasPeelingWitness u uImgPrev uImgNext` means that every element of the new
 image `im(A_{uImgNext})` admits one of the quadratic families required for a
 single peeling step. This is the local input used to transport orthogonality
 from one stage of the factor-peeling argument to the next. -/
def HasPeelingWitness (u uImgPrev uImgNext : UPair) : Prop :=
  ∀ q : Poly, InImageA uImgNext q → Nonempty (PeelingStepWitness u uImgPrev q)

/-- A `QuadraticFactorStep` records one peeled factor `r` from the paper's
 decomposition of the bad factor `h`. The relation `gNext * r = X^2 * gStart`
 formalizes the replacement of one complex quadratic factor by `x_1^2`
 (represented here by `X^2`). -/
structure QuadraticFactorStep (u0 : UPair) (gStart gNext : Poly) where
  r : Poly
  r_dvd_sigma : r ∣ sigma2 u0
  r_dvd_scale : r ∣ gStart
  peel_eq : gNext * r = (Polynomial.X ^ 2) * gStart

/-- If an affine linear function of `η` is nonnegative for every real `η`,
 then its slope must be zero. This is the analytic core of the peeling step:
 the SOCP inequality produces a one-parameter family whose linear coefficient is
 the pairing we want to prove vanishes. -/
private theorem linear_nonneg_all_eq_zero {a c : ℝ}
    (h : ∀ η : ℝ, 0 ≤ (2 * η) * a + c) : a = 0 := by
  by_contra ha
  have htwo : (2 : ℝ) * a ≠ 0 := mul_ne_zero two_ne_zero ha
  have hbad : 0 ≤ (2 * (-(c + 1) / (2 * a))) * a + c :=
    h (-(c + 1) / (2 * a))
  have hvalue : (2 * (-(c + 1) / (2 * a))) * a + c = -1 := by
    field_simp [htwo]
    ring
  linarith

section DotForm

variable {B : DotForm}

/-- A FOCP is automatically orthogonal to its own image: this is just the
 first-order condition `\eqref{eq:gradA}` rewritten as a statement about the
 entire image of `A_u`. -/
theorem image_orthogonal_self_of_focp {p : Poly} {u : UPair} (hfocp : IsFOCP B p u) :
    ImageOrthogonalResidual B p u u := by
  intro q hq
  rcases hq with ⟨v, rfl⟩
  exact hfocp v

/-- One peeling witness is enough to prove orthogonality to a specific target
 `q`. The proof follows the paper's Hessian-family argument: substitute the
 family `v_η` into the SOCP inequality, note that the quadratic coefficient is
 already zero by the previous stage, and conclude from nonnegativity for all
 `η` that the linear coefficient `⟨q, σ(u)-p⟩` must vanish. -/
theorem dot_eq_zero_of_peeling_step {p : Poly} {u uImgPrev : UPair} {q : Poly}
    (hsocp : IsSOCP B p u)
    (hprev : ImageOrthogonalResidual B p u uImgPrev)
    (hstep : PeelingStepWitness u uImgPrev q) :
    B q (residual p u) = 0 := by
  let r := residual p u
  have hquad : B hstep.qQuad r = 0 :=
    hprev _ hstep.quad_in_prev_image
  have hη :
      ∀ η : ℝ,
        0 ≤ (2 * η) * B q r +
          (B hstep.sigmaConst r + 2 * B hstep.aConst hstep.aConst) := by
    intro η
    have hh : 0 ≤ hessianTerm B p u (hstep.family η) := hsocp.2 _
    rw [hessianTerm, hstep.A_const η, hstep.sigma_eq η] at hh
    simpa [r, add_assoc, add_left_comm, add_comm, hquad] using hh
  have hzero := linear_nonneg_all_eq_zero hη
  simpa [r] using hzero

end DotForm

/-- The explicit one-parameter family `v_η = η·quad + const` used in the
 peeling step. This is the formal version of the `v_η` family in the proof of
 `\Cref{prop:second_order_property_factor}`. -/
def RotatedPeelingData.family {u uImgPrev : UPair} {q : Poly}
    (hdata : RotatedPeelingData u uImgPrev q) (η : ℝ) : UPair :=
  η • hdata.quad + hdata.const

/-- Any `RotatedPeelingData` yields a `PeelingStepWitness`. The proof is a
 direct expansion of `A_u(v_η)` and `σ(v_η)` using the orthogonality and mixed
 term identities recorded in the structure. -/
def RotatedPeelingData.toWitness {u uImgPrev : UPair} {q : Poly}
    (hdata : RotatedPeelingData u uImgPrev q) :
    PeelingStepWitness u uImgPrev q := by
  refine
    { qQuad := sigma2 hdata.quad
      sigmaConst := sigma2 hdata.const
      aConst := A u hdata.const
      quad_in_prev_image := hdata.quad_in_prev_image
      family := hdata.family
      A_const := ?_
      sigma_eq := ?_ }
  · intro η
    have horth : A u hdata.quad = 0 := by
      simpa [InKerA] using hdata.quad_orth
    calc
      A u (hdata.family η) = (η : ℝ) • A u hdata.quad + A u hdata.const := by
        simp [RotatedPeelingData.family, A_add_right, A_smul_right]
      _ = A u hdata.const := by simp [horth]
  · intro η
    calc
      sigma2 (hdata.family η) =
          sigma2 (η • hdata.quad) + 2 * A (η • hdata.quad) hdata.const + sigma2 hdata.const := by
            simp [RotatedPeelingData.family, sigma2_add]
      _ = (η ^ 2 : ℝ) • sigma2 hdata.quad +
            2 * ((η : ℝ) • A hdata.quad hdata.const) +
            sigma2 hdata.const := by
              simp [A_smul_left]
      _ = (η ^ 2 : ℝ) • sigma2 hdata.quad +
            ((2 * η : ℝ) • A hdata.quad hdata.const) +
            sigma2 hdata.const := by
              have hsmul :
                  2 * ((η : ℝ) • A hdata.quad hdata.const) =
                    ((2 * η : ℝ) • A hdata.quad hdata.const) := by
                simp [Polynomial.smul_eq_C_mul, two_mul]
                ring
              rw [hsmul]
      _ = (η ^ 2 : ℝ) • sigma2 hdata.quad + ((2 * η : ℝ) • q) + sigma2 hdata.const := by
              simp [hdata.cross_eq]

/-- One algebraic factor step `gStart -> gNext` produces the rotated data
 needed for the analytic peeling argument. This is where divisibility of the
 peeled factor by `σ(u₀)` is converted into the statement that the quadratic
 term already lies in the previous image. -/
theorem rotatedPeelingData_of_factor_step {u u0 : UPair} {a gStart gNext : Poly}
    (hu : u = scalePair a u0)
    (hcop : IsCoprime u0.fst u0.snd)
    (hfg : QuadraticFactorStep u0 gStart gNext)
    (q : Poly) (hq : InImageA (scalePair gNext u0) q) :
    Nonempty (RotatedPeelingData u (scalePair gStart u0) q) := by
  rcases hq with ⟨b, hb⟩
  rcases hfg.r_dvd_sigma with ⟨s, hs⟩
  refine ⟨
    { quad := perpPair 1 (scalePair gNext u0)
      const := perpPair 1 b
      quad_orth := ?_
      quad_in_prev_image := ?_
      cross_eq := ?_ }⟩
  · rw [InKerA, hu]
    simp [A, perpPair, scalePair]
    ring
  · have hquad :
      sigma2 (perpPair 1 (scalePair gNext u0)) =
        gStart * ((Polynomial.X ^ 2) * gNext * s) := by
      calc
        sigma2 (perpPair 1 (scalePair gNext u0)) = sigma2 (scalePair gNext u0) := by simp
        _ = gNext ^ 2 * sigma2 u0 := by simp
        _ = gNext ^ 2 * (hfg.r * s) := by rw [hs]
        _ = (gNext * hfg.r) * (gNext * s) := by ring
        _ = (Polynomial.X ^ 2 * gStart) * (gNext * s) := by rw [hfg.peel_eq]
        _ = gStart * ((Polynomial.X ^ 2) * gNext * s) := by ring
    have himg :
        InImageA (scalePair gStart u0) (gStart * ((Polynomial.X ^ 2) * gNext * s)) :=
      inImageA_mul_of_isCoprime gStart ((Polynomial.X ^ 2) * gNext * s) u0 hcop
    exact hquad ▸ himg
  · calc
      A (perpPair 1 (scalePair gNext u0)) (perpPair 1 b) = A (scalePair gNext u0) b := by
        simp [A_perpPair_right]
      _ = q := hb

/-- If rotated peeling data exist for every target in the next image, then we
 get a full `HasPeelingWitness` statement. This is just packaging. -/
theorem hasPeelingWitness_of_rotated {u uImgPrev uImgNext : UPair}
    (hdata :
      ∀ q : Poly, InImageA uImgNext q → Nonempty (RotatedPeelingData u uImgPrev q)) :
    HasPeelingWitness u uImgPrev uImgNext := by
  intro q hq
  rcases hdata q hq with ⟨hqData⟩
  exact ⟨hqData.toWitness⟩

/-- A single `QuadraticFactorStep` gives the witness package required for one
 peeling move. This is the local algebraic input used later by the recursive
 schedule construction. -/
theorem hasPeelingWitness_of_factor_step {u u0 : UPair} {a gStart gNext : Poly}
    (hu : u = scalePair a u0)
    (hcop : IsCoprime u0.fst u0.snd)
    (hfg : QuadraticFactorStep u0 gStart gNext) :
    HasPeelingWitness u (scalePair gStart u0) (scalePair gNext u0) := by
  exact hasPeelingWitness_of_rotated (rotatedPeelingData_of_factor_step hu hcop hfg)

section DotForm

variable {B : DotForm}

/-- Orthogonality propagates across one peeling step: if the residual is
 already orthogonal to the previous image, and every element of the next image
 has a peeling witness, then it is also orthogonal to the next image. -/
theorem image_orthogonal_of_peeling_step {p : Poly} {u uImgPrev uImgNext : UPair}
    (hsocp : IsSOCP B p u)
    (hprev : ImageOrthogonalResidual B p u uImgPrev)
    (hstep : HasPeelingWitness u uImgPrev uImgNext) :
    ImageOrthogonalResidual B p u uImgNext := by
  intro q hq
  classical
  exact dot_eq_zero_of_peeling_step (B := B) hsocp hprev (Classical.choice (hstep q hq))

end DotForm

/-- A `PeelingPath` is an iterated chain of one-step peeling moves. It mirrors
 the paper's repeated passage from
 `A_{u g}` to `A_{u X^2 / r_1}` to `A_{u X^4 /(r_1 r_2)}`, and so on. -/
inductive PeelingPath (u : UPair) : UPair → UPair → Prop
  | refl (uStart : UPair) : PeelingPath u uStart uStart
  | step {uStart uMid uEnd : UPair} :
      PeelingPath u uStart uMid →
      HasPeelingWitness u uMid uEnd →
      PeelingPath u uStart uEnd

/-- Concatenation of peeling paths. This is the formal analogue of composing
 several factor-replacement steps in the paper. -/
theorem PeelingPath.trans {u uStart uMid uEnd : UPair}
    (h₁ : PeelingPath u uStart uMid)
    (h₂ : PeelingPath u uMid uEnd) :
    PeelingPath u uStart uEnd := by
  induction h₂ with
  | refl =>
      simpa using h₁
  | step hpath hstep ih =>
      exact PeelingPath.step ih hstep

/-- A `PeelingSchedule` is the same iteration written at the level of scalar
 factors rather than scaled pairs. It records the successive updates of the
 common factor in the proof of `\Cref{prop:second_order_property_factor}`. -/
inductive PeelingSchedule (u u0 : UPair) : Poly → Poly → Prop
  | done (g : Poly) : PeelingSchedule u u0 g g
  | peel {gStart gMid gEnd : Poly} :
      HasPeelingWitness u (scalePair gStart u0) (scalePair gMid u0) →
      PeelingSchedule u u0 gMid gEnd →
      PeelingSchedule u u0 gStart gEnd

/-- After peeling a list of bad factors, the terminal scale is obtained by
 replacing each peeled factor by one copy of `X^2`. This is the Lean version of
 the paper's `x_1^k / h` replacement. -/
def peelTerminalScale (gBase : Poly) : List Poly → Poly
  | [] => gBase
  | _ :: rs => peelTerminalScale ((Polynomial.X ^ 2) * gBase) rs

/-- Every peeling schedule induces a path of scaled pairs. This simply turns
 the scalar recursion into the pair-valued recursion used by the orthogonality
 lemmas. -/
theorem PeelingSchedule.toPath {u u0 : UPair} {gStart gEnd : Poly}
    (hsched : PeelingSchedule u u0 gStart gEnd) :
    PeelingPath u (scalePair gStart u0) (scalePair gEnd u0) := by
  induction hsched with
  | done g =>
      exact PeelingPath.refl _
  | peel hstep hsched ih =>
      have hfirst := PeelingPath.step (PeelingPath.refl _) hstep
      exact hfirst.trans ih

/-- The terminal scale never becomes zero if the initial coprime scale is
 nonzero. This prevents the peeled target from degenerating during the
 iteration. -/
theorem peelTerminalScale_ne_zero {gBase : Poly} {rs : List Poly}
    (hgBase : gBase ≠ 0) :
    peelTerminalScale gBase rs ≠ 0 := by
  induction rs generalizing gBase with
  | nil =>
      simpa [peelTerminalScale] using hgBase
  | cons r rs ih =>
      apply ih
      simp [hgBase]

/-- A list of peeled factors, together with a local theorem for each factor,
 builds the full recursive peeling schedule. This is the formal implementation
 of the paper's instruction to peel the factors of `h` one at a time. -/
theorem peelingSchedule_of_factors {u u0 : UPair} {gBase : Poly} {rs : List Poly}
    (hrs : ∀ r ∈ rs, r ∣ sigma2 u0)
    (hstep :
      ∀ {gStart gNext : Poly}, QuadraticFactorStep u0 gStart gNext →
        HasPeelingWitness u (scalePair gStart u0) (scalePair gNext u0)) :
    PeelingSchedule u u0 (gBase * rs.prod) (peelTerminalScale gBase rs) := by
  revert gBase
  induction rs with
  | nil =>
      intro gBase
      simpa [peelTerminalScale] using (PeelingSchedule.done (u := u) (u0 := u0) gBase)
  | cons r rs ih =>
      intro gBase
      have hr_sigma : r ∣ sigma2 u0 := hrs r (by simp)
      have hrs_tail : ∀ r' ∈ rs, r' ∣ sigma2 u0 := by
        intro r' hr'
        exact hrs r' (by simp [hr'])
      have hfg :
          QuadraticFactorStep u0 (gBase * (r :: rs).prod)
            (((Polynomial.X ^ 2) * gBase) * rs.prod) :=
        { r := r
          r_dvd_sigma := hr_sigma
          r_dvd_scale := by
            refine ⟨gBase * rs.prod, ?_⟩
            simp [List.prod_cons, mul_left_comm]
          peel_eq := by
            simp [List.prod_cons, mul_assoc, mul_left_comm, mul_comm] }
      have hschedTail :
          PeelingSchedule u u0 (((Polynomial.X ^ 2) * gBase) * rs.prod)
            (peelTerminalScale ((Polynomial.X ^ 2) * gBase) rs) :=
        ih hrs_tail (gBase := (Polynomial.X ^ 2) * gBase)
      exact PeelingSchedule.peel (hstep hfg) hschedTail

section DotForm

variable {B : DotForm}

/-- Orthogonality propagates along an entire peeling path by iterating the
 one-step propagation lemma. This is the abstract form of the paper's repeated
 factor-peeling argument. -/
theorem image_orthogonal_of_peeling_path {p : Poly} {u uStart uEnd : UPair}
    (hsocp : IsSOCP B p u)
    (hstart : ImageOrthogonalResidual B p u uStart)
    (hpath : PeelingPath u uStart uEnd) :
    ImageOrthogonalResidual B p u uEnd := by
  induction hpath with
  | refl =>
      simpa using hstart
  | step hpath hstep ih =>
      exact image_orthogonal_of_peeling_step (B := B) hsocp ih hstep

end DotForm

end LowRankUnivariateSOS
