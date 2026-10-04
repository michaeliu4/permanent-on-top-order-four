import Results.SoulesPotOrderFour.Solution.Rank3
import Results.SoulesPotOrderFour.Solution.Sector

/-!
# The rank-two theorem

`rank_two_pot`: for a complex Hermitian PSD `A` of order four with `rank A ≤ 2`,
`Π(A) ⪯ per(A) I` (Theorem 3.2).  Route: `K₂₂, K₂₁₁ ⪰ 0` and `e₁, e₂ (K₃₁) ≥ 0` from the rank-three
sector theorems, `det K₃₁ ≥ 0` by `transfer_rank2_of` from the rank-two chart certificate
`RankTwoCert`, the `3 × 3` criterion, and the sector reduction.
-/

open Matrix Equiv
open scoped ComplexOrder

namespace Results.SoulesPotOrderFour

/-- The rank-two certificate: `det K₃₁ ≥ 0` on the rank-two chart `A = V(t)ᴴ V(t)`. -/
def RankTwoCert : Prop := ∀ r a b c d : ℝ,
  0 ≤ (Matrix.det (K31 ((chartV2 r a b c d)ᴴ * chartV2 r a b c d).permanent
    ((chartV2 r a b c d)ᴴ * chartV2 r a b c d))).re

section RankTwo

variable (cert : ComplexCerts) (rt : RankTwoCert)
include cert rt

/-- **(Rk1)** Theorem 3.2 (`Challenge.theorem_3_2_loewner`): `Π(A) ⪯ per(A) I` for complex
Hermitian PSD `A` of order four and rank at most two. -/
theorem rank_two_pot (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef) (hrk : A.rank ≤ 2) :
    (A.permanent • (1 : Matrix (Perm (Fin 4)) (Perm (Fin 4)) ℂ) - schurPower A).PosSemidef := by
  have hrk3 : A.rank ≤ 3 := by omega
  have hdet := transfer_rank2_of (X := fun B => Matrix.det (K31 B.permanent B)) homog_det_K31 rt
    A hA hrk
  have h31 := K31_posSemidef_of_det cert hA hrk3 hdet
  have h211 := K211_posSemidef cert hA hrk3
  have h22 := K22_posSemidef cert hA hrk3
  have hd0 : A.det = 0 := det_eq_zero_of_rank hrk3
  have hpn := permanent_nonneg hA
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, A.permanent = lam := ⟨A.permanent.re, (permanent_eq_ofReal_re hA).symm⟩
  rw [hlam] at h31 h211 h22 hpn ⊢
  exact schurPower_defect_posSemidef A hA.isHermitian lam hlam.le (by rw [hd0]; exact hpn)
    h31 h211 h22

/-- The second assertion of `Challenge.main` (complex Hermitian PSD matrices of rank `≤ 2`). -/
theorem main_ranktwo_of : ∀ (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef), A.rank ≤ 2 →
    (lambdaMax (schurPower_isHermitian hA.isHermitian) : ℂ) = A.permanent :=
  fun A hA hrk => (lambdaMax_eq_permanent_iff_complex hA.isHermitian).2 (rank_two_pot cert rt A hA hrk)

end RankTwo

end Results.SoulesPotOrderFour
