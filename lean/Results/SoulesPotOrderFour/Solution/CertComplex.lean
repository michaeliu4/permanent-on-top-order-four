import Results.SoulesPotOrderFour.Solution.KronPipe
import Results.SoulesPotOrderFour.Solution.DataC22Tr
import Results.SoulesPotOrderFour.Solution.DataC22Det
import Results.SoulesPotOrderFour.Solution.DataC31E1
import Results.SoulesPotOrderFour.Solution.DataC31E2
import Results.SoulesPotOrderFour.Solution.DataC8p5T
import Results.SoulesPotOrderFour.Solution.DataCMoment

/-!
# The complex rank-three certificates

Exact SOS certificates of the authors (`complex22/certificates`, `complex211/certificates`), generated
into the `DataC*.lean` modules and checked by kernel computation (`Kron.lean`, `KronPipe.lean`) on the
complex chart `A = V(t)ᴴ V(t)`, `V = [[1,1,1,1],[0,x,a+ib,c+id],[0,0,z,e+if]]`:

* `cert_tr22`, `cert_det22`: `tr K₂₂ ≥ 0`, `det K₂₂ ≥ 0`;
* `cert_tr31`, `cert_e2_31`: `e₁ K₃₁ ≥ 0`, `e₂ K₃₁ ≥ 0`;
* `cert_8p5T`: `8 p - 5 tr G ≥ 0`;
* `cert_moment`: `3p² - 2pT - T² + 4 e₂(G) ≥ 0`.
-/

open Matrix

namespace Results.SoulesPotOrderFour
open Kron

set_option maxRecDepth 100000
set_option Elab.async false

theorem cert_tr22_checkP : checkP 8 c22trD c22trBP c22trVL (fun _ => 2) c22trNP c22trDpoly c22trPoly
    (tTr22.Φ Gi ((V1v c22trD c22trBP (-Gi.I))ᵀ * V1v c22trD c22trBP Gi.I)) = true := by decide +kernel

cert_checkS cert_tr22_checkS 1 8 8 c22trD c22trBS c22trDm c22trDpoly c22trLcm c22trWd c22trVL c22trBlocks c22trBlocks c22trPoly

theorem cert_tr22_bound :
    (∀ l, (tTr22.bd (bV1ᵀ * bV1)).d l ≤ (fun _ : Fin 8 => 2) l) ∧ (tTr22.bd (bV1ᵀ * bV1)).n ≤ c22trNP := by
  decide +kernel

theorem cert_tr22 (x a b z c d e f : ℝ) :
    0 ≤ (Matrix.trace (K22 ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f).permanent
      ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f))).re :=
  cert_V1 tTr22 cert_tr22_checkP cert_tr22_checkS cert_tr22_bound.1 cert_tr22_bound.2 x a b z c d e f

theorem cert_det22_checkP : checkP 8 c22detD c22detBP c22detVL (fun _ => 4) c22detNP c22detDpoly c22detPoly
    (tDet22.Φ Gi ((V1v c22detD c22detBP (-Gi.I))ᵀ * V1v c22detD c22detBP Gi.I)) = true := by decide +kernel

cert_checkS cert_det22_checkS 2 8 8 c22detD c22detBS c22detDm c22detDpoly c22detLcm c22detWd c22detVL c22detBlocks c22detBlocks c22detPoly

theorem cert_det22_bound :
    (∀ l, (tDet22.bd (bV1ᵀ * bV1)).d l ≤ (fun _ : Fin 8 => 4) l) ∧ (tDet22.bd (bV1ᵀ * bV1)).n ≤ c22detNP := by
  decide +kernel

theorem cert_det22 (x a b z c d e f : ℝ) :
    0 ≤ (Matrix.det (K22 ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f).permanent
      ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f))).re :=
  cert_V1 tDet22 cert_det22_checkP cert_det22_checkS cert_det22_bound.1 cert_det22_bound.2 x a b z c d e f

theorem cert_tr31_checkP : checkP 8 c31e1D c31e1BP c31e1VL (fun _ => 2) c31e1NP c31e1Dpoly c31e1Poly
    (tTr31.Φ Gi ((V1v c31e1D c31e1BP (-Gi.I))ᵀ * V1v c31e1D c31e1BP Gi.I)) = true := by decide +kernel

cert_checkS cert_tr31_checkS 1 8 8 c31e1D c31e1BS c31e1Dm c31e1Dpoly c31e1Lcm c31e1Wd c31e1VL c31e1Blocks c31e1Blocks c31e1Poly

theorem cert_tr31_bound :
    (∀ l, (tTr31.bd (bV1ᵀ * bV1)).d l ≤ (fun _ : Fin 8 => 2) l) ∧ (tTr31.bd (bV1ᵀ * bV1)).n ≤ c31e1NP := by
  decide +kernel

theorem cert_tr31 (x a b z c d e f : ℝ) :
    0 ≤ (e1 (K31 ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f).permanent
      ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f))).re :=
  cert_V1 tTr31 cert_tr31_checkP cert_tr31_checkS cert_tr31_bound.1 cert_tr31_bound.2 x a b z c d e f

theorem cert_e2_31_checkP : checkP 8 c31e2D c31e2BP c31e2VL (fun _ => 4) c31e2NP c31e2Dpoly c31e2Poly
    (tE2.Φ Gi ((V1v c31e2D c31e2BP (-Gi.I))ᵀ * V1v c31e2D c31e2BP Gi.I)) = true := by decide +kernel

cert_checkS cert_e2_31_checkS 2 8 8 c31e2D c31e2BS c31e2Dm c31e2Dpoly c31e2Lcm c31e2Wd c31e2VL c31e2Blocks c31e2Blocks c31e2Poly

theorem cert_e2_31_bound :
    (∀ l, (tE2.bd (bV1ᵀ * bV1)).d l ≤ (fun _ : Fin 8 => 4) l) ∧ (tE2.bd (bV1ᵀ * bV1)).n ≤ c31e2NP := by
  decide +kernel

theorem cert_e2_31 (x a b z c d e f : ℝ) :
    0 ≤ (e2 (K31 ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f).permanent
      ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f))).re :=
  cert_V1 tE2 cert_e2_31_checkP cert_e2_31_checkS cert_e2_31_bound.1 cert_e2_31_bound.2 x a b z c d e f

theorem cert_8p5T_checkP : checkP 8 c8p5tD c8p5tBP c8p5tVL (fun _ => 2) c8p5tNP c8p5tDpoly c8p5tPoly
    (t8p5T.Φ Gi ((V1v c8p5tD c8p5tBP (-Gi.I))ᵀ * V1v c8p5tD c8p5tBP Gi.I)) = true := by decide +kernel

cert_checkS cert_8p5T_checkS 1 8 8 c8p5tD c8p5tBS c8p5tDm c8p5tDpoly c8p5tLcm c8p5tWd c8p5tVL c8p5tBlocks c8p5tBlocks c8p5tPoly

theorem cert_8p5T_bound :
    (∀ l, (t8p5T.bd (bV1ᵀ * bV1)).d l ≤ (fun _ : Fin 8 => 2) l) ∧ (t8p5T.bd (bV1ᵀ * bV1)).n ≤ c8p5tNP := by
  decide +kernel

theorem cert_8p5T (x a b z c d e f : ℝ) :
    0 ≤ (8 * ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f).permanent -
      5 * Matrix.trace (signCofactorMatrix ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f))).re :=
  cert_V1 t8p5T cert_8p5T_checkP cert_8p5T_checkS cert_8p5T_bound.1 cert_8p5T_bound.2 x a b z c d e f

theorem cert_moment_checkP : checkP 8 cmomD cmomBP cmomVL (fun _ => 4) cmomNP cmomDpoly cmomPoly
    (tMoment.Φ Gi ((V1v cmomD cmomBP (-Gi.I))ᵀ * V1v cmomD cmomBP Gi.I)) = true := by decide +kernel

cert_checkS cert_moment_checkS 2 8 8 cmomD cmomBS cmomDm cmomDpoly cmomLcm cmomWd cmomVL cmomBlocks cmomBlocks cmomPoly

theorem cert_moment_bound :
    (∀ l, (tMoment.bd (bV1ᵀ * bV1)).d l ≤ (fun _ : Fin 8 => 4) l) ∧ (tMoment.bd (bV1ᵀ * bV1)).n ≤ cmomNP := by
  decide +kernel

theorem cert_moment (x a b z c d e f : ℝ) :
    0 ≤ (3 * ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f).permanent ^ 2 -
      2 * ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f).permanent *
        Matrix.trace (signCofactorMatrix ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f)) -
      Matrix.trace (signCofactorMatrix ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f)) ^ 2 +
      4 * e2four (signCofactorMatrix ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f))).re :=
  cert_V1 tMoment cert_moment_checkP cert_moment_checkS cert_moment_bound.1 cert_moment_bound.2 x a b z c d e f

end Results.SoulesPotOrderFour
