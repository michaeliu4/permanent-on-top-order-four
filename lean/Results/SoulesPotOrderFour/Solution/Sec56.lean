import Results.SoulesPotOrderFour.Solution.Rank3
import Results.SoulesPotOrderFour.Solution.Sector
import Results.SoulesPotOrderFour.Solution.Glue

/-!
# Section 5.6: `λ_max(Π(A)) = λ_max(F_A)` for PSD `A` of order four

The full-rank sector bounds are taken as hypotheses (they are the statements `K22_psd_all`,
`K211_psd_all`, `det_le_permanent` of `FullRank.lean`, proved there from `ComplexCerts` and `Order3`).
-/

open Matrix Equiv
open scoped ComplexOrder

namespace Results.SoulesPotOrderFour

/-- **Section 5.6** (shape of `Challenge.section_5_6_lambdaMax_eq`), with the full-rank sector
bounds as hypotheses. -/
theorem section_5_6_of
    (hK22 : ∀ A : Matrix (Fin 4) (Fin 4) ℂ, A.PosSemidef → (K22 A.permanent A).PosSemidef)
    (hK211 : ∀ A : Matrix (Fin 4) (Fin 4) ℂ, A.PosSemidef → (K211 A.permanent A).PosSemidef)
    (hdetle : ∀ A : Matrix (Fin 4) (Fin 4) ℂ, A.PosSemidef → A.det ≤ A.permanent)
    (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef) :
    lambdaMax (schurPower_isHermitian hA.isHermitian) =
      lambdaMax (cofactorPermMatrix_isHermitian hA.isHermitian) := by
  have hF := cofactorPermMatrix_isHermitian hA.isHermitian
  have hP := schurPower_isHermitian hA.isHermitian
  refine le_antisymm ?_ ?_
  · -- `λ_max Π ≤ λ_max F`
    set lam := lambdaMax hF with hlam
    have hper : A.permanent ≤ (lam : ℂ) := by
      have h := le_lambdaMax_of_eigen hF (y := (1 : Fin 4 → ℂ)) one_ne_zero
        (μ := A.permanent.re)
        (by convert cofactorPermMatrix_mulVec_one A using 2; exact permanent_eq_ofReal_re hA)
      have h2 := Complex.real_le_real.2 h
      rwa [permanent_eq_ofReal_re hA] at h2
    have hFpsd := (lambdaMax_le_iff hF lam).1 le_rfl
    have h31 : (K31 (lam : ℂ) A).PosSemidef := by
      unfold K31
      rw [← Q3_conjTranspose]
      exact hFpsd.conjTranspose_mul_mul_same _
    exact (lambdaMax_le_iff hP lam).2 (schurPower_defect_posSemidef A hA.isHermitian lam hper
      ((hdetle A hA).trans hper) h31 (K211_mono hper (hK211 A hA)) (K22_mono hper (hK22 A hA)))
  · -- `λ_max F ≤ λ_max Π`
    obtain ⟨y, hy, hFy⟩ := exists_eigenvector_lambdaMax hF
    exact le_lambdaMax_of_eigen hP (liftF_ne_zero hy) (schurPower_mulVec_liftF_eigen A hFy)

end Results.SoulesPotOrderFour
