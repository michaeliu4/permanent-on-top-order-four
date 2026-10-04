import Results.SoulesPotOrderFour.Solution.KronBound
import Results.SoulesPotOrderFour.Solution.DataBound

/-!
# The `19/18` bound certificate

`cert_bound1918`: for the chart `A = V(t)ᴴ V(t)` (`V = [[1,1,1,1],[0,x,a+ib,c+id],[0,0,z,e+if]]`) and every
`y = (q₀ + i q₃, q₁ + i q₄, q₂ + i q₅)` one has `0 ≤ Re (y* K₃₁((19/18) per A, A) y)`.  The quadratic form is
`Θ(t, q) = ȳᵀ Q₃ᵀ (19 p - 18 F) Q₃ y` (`18 K₃₁((19/18) p)`), a polynomial in 14 variables; its Kronecker
value is assembled from the 36 `q`-channels of the 8-variable entries of `Q₃ᵀ(19p - 18F)Q₃` (`KronBound.lean`),
and the exact certificate `bound/certificates/certificate_hook_bound_19_18_m0.json` (generated into
`DataBound.lean`) is checked by kernel computation.
-/

open Matrix

namespace Results.SoulesPotOrderFour
open Kron

set_option maxRecDepth 100000
set_option Elab.async false

theorem cert_bound_checkP :
    checkPq bndBP (fun _ => 2) bndNP bndDpoly bndPoly
      (Kb ((V1v14 3 bndBP (-Gi.I))ᵀ * V1v14 3 bndBP Gi.I)) = true := by decide +kernel

cert_checkS cert_bound_checkS 1 8 14 3 bndBS bndDm bndDpoly bndLcm bndWd 8 bndBlocks bndBlocks bndPoly

theorem cert_bound_bd :
    (∀ l, (bTheta (bKb (bV14ᵀ * bV14))).d l ≤ 2) ∧ (bTheta (bKb (bV14ᵀ * bV14))).n ≤ bndNP := by
  decide +kernel

/-- **The `19/18` chart inequality.** -/
theorem cert_bound1918 (x a b z c d e f q0 q1 q2 q3 q4 q5 : ℝ) :
    0 ≤ (star ![(q0 : ℂ) + (q3 : ℂ) * Complex.I, (q1 : ℂ) + (q4 : ℂ) * Complex.I,
        (q2 : ℂ) + (q5 : ℂ) * Complex.I] ⬝ᵥ
      (K31 ((19 / 18 : ℂ) * ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f).permanent)
        ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f) *ᵥ
        ![(q0 : ℂ) + (q3 : ℂ) * Complex.I, (q1 : ℂ) + (q4 : ℂ) * Complex.I,
          (q2 : ℂ) + (q5 : ℂ) * Complex.I])).re :=
  cert_bound_core cert_bound_checkP cert_bound_checkS cert_bound_bd.1 cert_bound_bd.2
    x a b z c d e f q0 q1 q2 q3 q4 q5

end Results.SoulesPotOrderFour
