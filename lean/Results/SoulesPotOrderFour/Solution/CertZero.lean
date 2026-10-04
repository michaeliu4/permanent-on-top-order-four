import Results.SoulesPotOrderFour.Solution.KronPipe
import Results.SoulesPotOrderFour.Solution.DataZero

/-!
# The zero off-diagonal hook certificate

`cert_zero_det31`: `det K₃₁ ≥ 0` on the zero chart `A = V(t)ᴴ V(t)`,
`V = [[1,0,a,c+id],[0,1,b,e+if],[0,0,1,1]]`, from the exact SOS certificate
`zero/certificates/certificate_hook_zero_offdiagonal.json` (generated into `DataZero.lean`).
-/

open Matrix

namespace Results.SoulesPotOrderFour
open Kron

set_option maxRecDepth 100000
set_option Elab.async false

theorem cert_zero_checkP : checkP 6 zeroD zeroBP zeroVL (fun _ => 6) zeroNP zeroDpoly zeroPoly
    (tDet31.Φ Gi ((Vzv zeroD zeroBP (-Gi.I))ᵀ * Vzv zeroD zeroBP Gi.I)) = true := by decide +kernel

cert_checkS cert_zero_checkS 1 8 6 zeroD zeroBS zeroDm zeroDpoly zeroLcm zeroWd zeroVL zeroBlocks zeroBlocks zeroPoly

theorem cert_zero_bound :
    (∀ l, (tDet31.bd (bVzᵀ * bVz)).d l ≤ (fun _ : Fin 6 => 6) l) ∧ (tDet31.bd (bVzᵀ * bVz)).n ≤ zeroNP := by
  decide +kernel

/-- **Zero off-diagonal certificate**: `det K₃₁ ≥ 0` for the zero chart. -/
theorem cert_zero_det31 (a b c d e f : ℝ) :
    0 ≤ (Matrix.det (K31 ((chartVz a b c d e f)ᴴ * chartVz a b c d e f).permanent
      ((chartVz a b c d e f)ᴴ * chartVz a b c d e f))).re :=
  cert_Vz tDet31 cert_zero_checkP cert_zero_checkS cert_zero_bound.1 cert_zero_bound.2 a b c d e f

end Results.SoulesPotOrderFour
