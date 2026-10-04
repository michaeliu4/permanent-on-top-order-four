import Results.SoulesPotOrderFour.Solution.KronPipe
import Results.SoulesPotOrderFour.Solution.DataReal

/-!
# The real hook certificate

`cert_real_det31`: `det K₃₁ ≥ 0` on the real chart `A = V(t)ᵀ V(t)`, `V = [[1,1,1,1],[0,x,y,u],[0,0,z,v]]`.
The proof is the exact SOS certificate `real/certificates/certificate_real_hook_degree16.json` of the
authors (generated into `DataReal.lean`), checked by kernel computation (`Kron.lean`, `KronPipe.lean`).
-/

open Matrix

namespace Results.SoulesPotOrderFour
open Kron

set_option maxRecDepth 100000
set_option Elab.async false

theorem cert_real_checkP : checkP 5 realD realBP realVL (fun _ => 6) realNP realDpoly realPoly
    (tDet31.Φ Gi ((VRv realD realBP)ᵀ * VRv realD realBP)) = true := by decide +kernel

cert_checkS cert_real_checkS 2 4 5 realD realBS realDm realDpoly realLcm realWd realVL realBlocks realBlocks realPoly

theorem cert_real_bound :
    (∀ l, (tDet31.bd (bVRᵀ * bVR)).d l ≤ (fun _ : Fin 5 => 6) l) ∧ (tDet31.bd (bVRᵀ * bVR)).n ≤ realNP := by
  decide +kernel

/-- **Real hook certificate**: `det K₃₁ ≥ 0` for the real chart. -/
theorem cert_real_det31 (x y z u v : ℝ) :
    0 ≤ Matrix.det (K31 ((chartVR x y z u v)ᵀ * chartVR x y z u v).permanent
      ((chartVR x y z u v)ᵀ * chartVR x y z u v)) :=
  cert_VR tDet31 cert_real_checkP cert_real_checkS cert_real_bound.1 cert_real_bound.2 x y z u v

theorem real_hook_det_nonneg (x y z u v : ℝ) :
    0 ≤ (K31 ((chartVR x y z u v)ᵀ * chartVR x y z u v).permanent
      ((chartVR x y z u v)ᵀ * chartVR x y z u v)).det := cert_real_det31 x y z u v

end Results.SoulesPotOrderFour
