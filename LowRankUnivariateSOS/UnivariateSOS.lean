import LowRankUnivariateSOS.UnivariateAlgebraCore
import Mathlib.Tactic.Ring

noncomputable section

namespace LowRankUnivariateSOS

/-- The product of two binary sums of two squares is again a binary sum of two
 squares. This is the classical two-squares identity, and it is the algebraic
 engine behind the SOS multiplier constructed in the hgroup lemma. -/
theorem isSOS_mul {p q : Poly}
    (hp : IsSOS p) (hq : IsSOS q) :
    IsSOS (p * q) := by
  rcases hp with ⟨a, b, rfl⟩
  rcases hq with ⟨c, d, rfl⟩
  refine ⟨a * c - b * d, a * d + b * c, ?_⟩
  ring

/-- Affine hgroup lemma, corresponding to the affine version of
 `\Cref{lem:hgroup}` proved in the paper just before the projective statement.
 If `p` and `q` are SOS and `g` is coprime to `q`, then `p` can be written as
 `g·t + s·q` with `s` still SOS.

 Proof sketch: choose Bézout coefficients `a,b` with `a g + b q = 1`; then
 `b² p q` is SOS, and a direct algebraic identity shows that
 `g * (p * (2a - a² g)) + (b² p q) * q = p`. This is the Lean compression of
 the paper's congruence argument modulo `g`. -/
theorem hgroup_affine
    (g p q : Poly) :
    IsSOS p → IsSOS q → IsCoprime g q →
      ∃ s t : Poly, IsSOS s ∧ p = g * t + s * q := by
  intro hp hq hcop
  rcases hcop with ⟨a, b, hbez⟩
  let s : Poly := b ^ 2 * p * q
  let t : Poly := p * (2 * a - a ^ 2 * g)
  refine ⟨s, t, ?_, ?_⟩
  · have hb2 : IsSOS (b ^ 2) := ⟨b, 0, by simp [pow_two]⟩
    exact isSOS_mul (isSOS_mul hb2 hp) hq
  · apply Eq.symm
    have hbq : b * q = 1 - a * g := by
      calc
        b * q = (a * g + b * q) - a * g := by ring
        _ = 1 - a * g := by rw [hbez]
    calc
      g * t + s * q
          = p * (g * (2 * a - a ^ 2 * g) + b ^ 2 * q ^ 2) := by
              simp [s, t]
              ring
      _ = p * (a * g * (2 - a * g) + (b * q) ^ 2) := by
            ring
      _ = p * (a * g * (2 - a * g) + (1 - a * g) ^ 2) := by
            rw [hbq]
      _ = p := by
            ring

end LowRankUnivariateSOS
