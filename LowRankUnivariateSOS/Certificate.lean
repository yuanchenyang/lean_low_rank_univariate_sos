import LowRankUnivariateSOS.PolynomialModel

noncomputable section

namespace LowRankUnivariateSOS

/-- This is the paper's condition (C2): a polynomial lies in
 `im(A_u) + cone(σ(ker(A_u)))`. The later files show that once `p` admits such
 a decomposition relative to `u`, the SOCP conditions force the residual to
 vanish. -/
def InImagePlusSigmaKerCone (u : UPair) (q : Poly) : Prop :=
  ∃ v : UPair, ∃ ws : Finset UPair,
    (∀ w ∈ ws, InKerA u w) ∧ q = A u v + ws.sum sigma2

end LowRankUnivariateSOS
