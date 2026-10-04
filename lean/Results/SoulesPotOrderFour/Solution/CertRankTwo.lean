import Results.SoulesPotOrderFour.Solution.KronPipe
import Results.SoulesPotOrderFour.Solution.DataRank2

/-!
# The rank-two certificate

`cert_rank2_det31`: `det K₃₁ ≥ 0` on the rank-two chart `A = V(t)ᴴ V(t)`, `V = [[1,1,1,1],[0,r,a+ib,c+id]]`.
The authors' certificate `ranktwo/soules_order4_rank2_certificate.json` writes `det M(t)` as a Gram form
`½ · scale · (S(t) + S(ι t))` with `ι (r,a,b,c,d) = (r,c,d,a,b)`; `det K₃₁ = 2 det M` is *not* needed here:
the data module `DataRank2.lean` contains the polynomial `det K₃₁` (recomputed from the pipeline of the
statement and checked against the Gram data) and both copies `S(t)`, `S(ι t)` as Gram blocks sharing `N`, `C`.
-/

open Matrix

namespace Results.SoulesPotOrderFour
open Kron

set_option maxRecDepth 100000
set_option Elab.async false

theorem cert_rank2_checkP : checkP 5 rank2D rank2BP rank2VL (fun _ => 6) rank2NP rank2Dpoly rank2Poly
    (tDet31.Φ Gi ((V2v rank2D rank2BP (-Gi.I))ᵀ * V2v rank2D rank2BP Gi.I)) = true := by decide +kernel

cert_checkS cert_rank2_checkS 8 4 5 rank2D rank2BS rank2Dm rank2Dpoly rank2Lcm rank2Wd rank2VL rank2Blocks (rank2Blocks.take 4)
      rank2Poly

theorem cert_rank2_bound :
    (∀ l, (tDet31.bd (bV2ᵀ * bV2)).d l ≤ (fun _ : Fin 5 => 6) l) ∧ (tDet31.bd (bV2ᵀ * bV2)).n ≤ rank2NP := by
  decide +kernel

/-- **Rank-two certificate**: `det K₃₁ ≥ 0` for the rank-two chart. -/
theorem cert_rank2_det31 (r a b c d : ℝ) :
    0 ≤ (Matrix.det (K31 ((chartV2 r a b c d)ᴴ * chartV2 r a b c d).permanent
      ((chartV2 r a b c d)ᴴ * chartV2 r a b c d))).re :=
  cert_V2 tDet31 cert_rank2_checkP cert_rank2_checkS cert_rank2_bound.1 cert_rank2_bound.2 r a b c d

end Results.SoulesPotOrderFour
