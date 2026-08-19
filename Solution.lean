import LowRankUnivariateSOS

/-!
# Proved solution

This module imports the full proof development `LowRankUnivariateSOS`, which
proves the declaration advertised in `Challenge.lean`:

* `LowRankUnivariateSOS.rankTwo_no_spurious_socp`
  (`LowRankUnivariateSOS/RankTwoMain.lean`): `σ(u) = p` at every SOCP.

The statement-level definitions `Poly`, `UPair`, `sigma2`, `A`, `residual`,
`IsSOS`, `DotForm`, `objective`, `IsFOCP`, `hessianTerm` and `IsSOCP` are
declared in `LowRankUnivariateSOS/PolynomialModel.lean` and
`LowRankUnivariateSOS/Socp.lean`, verbatim as in `Challenge.lean`. Comparator
checks that the advertised theorem and every definition its statement uses
agree exactly between the two modules and that the proof uses only the
permitted axioms `propext`, `Classical.choice` and `Quot.sound`.

The `example` below restates the advertised theorem so that this file fails to
compile if the library statement ever drifts from `Challenge.lean`.

## Proof outline

The proof follows Sections 3–4 of the paper (see `README.md` and the
blueprint for a fuller account):

1. `gcd_sigma_decomposition` (`UnivariateAlgebraCore.lean`) writes `u = a·u₀`
   with `u₀ = (u₀₁, u₀₂)` coprime, as in Proposition 3.4, and
   `no_real_roots_sigma_reduced` shows that `σ(u₀)` has no real roots
   (Proposition 3.6).
2. `factor_peeling_image_orthogonal` (`UnivariateAlgebra.lean`,
   `PeelingStep.lean`) is the factor-peeling argument of Proposition 4.4: the
   quadratic factors of `a` shared with `σ(u₀)` are replaced one at a time by
   `X²`, yielding `g` coprime to `σ(u₀)` with `⟨im(A_{g u₀}), σ(u) - p⟩ = 0`.
3. `hgroup_affine` (`UnivariateSOS.lean`) is Lemma 3.9: since `g` and
   `σ(u₀)` are coprime, `p = g·q + s·σ(u₀)` with `s` a sum of squares.
4. `inImagePlusSigmaKerCone_of_h1_data` (`H1Case.lean`) and
   `factored_h1_residual_eq_zero` (`FactoredCase.lean`) run the certificate
   argument of Proposition 4.2 / condition (C3): the image term is orthogonal to
   the residual by first-order criticality, the kernel-cone term pairs
   nonnegatively with it by second-order criticality, and
   `⟨σ(u), σ(u) - p⟩ = 0` then forces `‖σ(u) - p‖² ≤ 0`.
5. `rankTwo_no_spurious_socp` (`RankTwoMain.lean`) assembles these steps,
   treating the degenerate case `a = 0` directly from the Hessian condition.
-/

namespace LowRankUnivariateSOS

variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]

example (p : Poly) (u : UPair) (hp : IsSOS p) (hsocp : IsSOCP B p u) :
    sigma2 u = p :=
  rankTwo_no_spurious_socp p u hp hsocp

end LowRankUnivariateSOS
