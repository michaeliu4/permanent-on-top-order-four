import Results.SoulesPotOrderFour.Solution.Rank3
import Results.SoulesPotOrderFour.Solution.Sector
import Results.SoulesPotOrderFour.Solution.Decrement
import Results.SoulesPotOrderFour.Solution.FullRank

/-!
# The real order-four theorem

For every real symmetric positive semidefinite `A` of order four, `Π(A) ⪯ per(A) I`.

* `real_rank3`: rank `≤ 3` (complex sector theorems of `Rank3`, the real hook determinant by
  `transfer_real_of`, then `Sector.schurPower_defect_posSemidef`).
* `real_pot`: all ranks (rank four via the diagonal decrement and the order-three theorem `h3`).
* `main_real_of`: the first assertion of `Challenge.main`.

The chart inequality `RealCert` (determinant of `K₃₁` on the real chart) and the order-three
theorem `h3` are hypotheses.
-/

open Matrix Equiv
open scoped ComplexOrder

namespace Results.SoulesPotOrderFour

/-- The real certificate: `det K₃₁ ≥ 0` on the real chart `A = V(t)ᵀ V(t)`. -/
def RealCert : Prop := ∀ x y z u v : ℝ,
  0 ≤ Matrix.det (K31 ((chartVR x y z u v)ᵀ * chartVR x y z u v).permanent
    ((chartVR x y z u v)ᵀ * chartVR x y z u v))

section Rank

/-- For a `4 × 4` matrix over a field, `rank ≤ 3` iff `det = 0`. -/
theorem rank_le_three_iff_det {K : Type*} [Field K] (A : Matrix (Fin 4) (Fin 4) K) :
    A.rank ≤ 3 ↔ A.det = 0 := by
  constructor
  · intro hrk
    by_contra h
    have := Matrix.rank_of_isUnit A ((Matrix.isUnit_iff_isUnit_det A).2 (IsUnit.mk0 _ h))
    simp at this
    omega
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have h1 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    have h2 : 0 < Module.finrank K (LinearMap.ker A.mulVecLin) :=
      Module.finrank_pos_iff_exists_ne_zero.2
        ⟨⟨v, LinearMap.mem_ker.2 (by rw [Matrix.mulVecLin_apply]; exact hv)⟩,
          fun h0 => hv0 (congrArg Subtype.val h0)⟩
    rw [Module.finrank_pi, Fintype.card_fin] at h1
    unfold Matrix.rank
    omega

theorem det_map_ofReal {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) :
    (M.map ((↑) : ℝ → ℂ)).det = ((M.det : ℝ) : ℂ) := by
  exact (RingHom.map_det Complex.ofRealHom M).symm

/-- The rank of a real `4 × 4` matrix is `≤ 3` iff that of its complex image is. -/
theorem rank_map_ofReal_le_three (M : Matrix (Fin 4) (Fin 4) ℝ) :
    (M.map ((↑) : ℝ → ℂ)).rank ≤ 3 ↔ M.rank ≤ 3 := by
  rw [rank_le_three_iff_det, rank_le_three_iff_det, det_map_ofReal]
  exact Complex.ofReal_eq_zero

end Rank

section Cast

/-- `K₃₁` commutes with ring homomorphisms. -/
theorem K31_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A : Matrix (Fin 4) (Fin 4) R) :
    K31 (A.map f).permanent (A.map f) = (K31 A.permanent A).map f := by
  have hF : cofactorPermMatrix (A.map f) = (cofactorPermMatrix A).map f := by
    ext i j
    have : (A.map f).submatrix i.succAbove j.succAbove =
        (A.submatrix i.succAbove j.succAbove).map f := rfl
    simp only [cofactorPermMatrix, permMinor, of_apply, map_apply, this, map_mul]
    rw [Results.SoulesPotOrderFour.permanent_map]
  have hQ : (Q3 : Matrix (Fin 4) (Fin 3) R).map f = Q3 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Q3]
  unfold K31
  rw [Results.SoulesPotOrderFour.permanent_map, hF, Matrix.map_mul, Matrix.map_mul,
    Matrix.map_sub _ (map_sub f), Matrix.map_smul' _ _ _ (map_mul f), Matrix.transpose_map, hQ,
    Matrix.map_one _ (map_zero f) (map_one f)]

theorem re_det_K31_map (B : Matrix (Fin 4) (Fin 4) ℝ) :
    (Matrix.det (K31 (B.map ((↑) : ℝ → ℂ)).permanent (B.map ((↑) : ℝ → ℂ)))).re =
      (K31 B.permanent B).det := by
  rw [show (B.map ((↑) : ℝ → ℂ)) = B.map Complex.ofRealHom from rfl, K31_map]
  change ((K31 B.permanent B).map ((↑) : ℝ → ℂ)).det.re = _
  rw [det_map_ofReal, Complex.ofReal_re]

end Cast

section Real

variable (cert : ComplexCerts) (rc : RealCert)
include rc

/-- `det K₃₁ ≥ 0` for real PSD matrices of rank `≤ 3`. -/
theorem real_det_K31_nonneg (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.PosSemidef)
    (hrk : A.rank ≤ 3) : 0 ≤ (K31 A.permanent A).det := by
  have h := transfer_real_of (X := fun B => Matrix.det (K31 B.permanent B)) homog_det_K31
    (fun x y z u v => by
      show 0 ≤ (Matrix.det (K31 (((chartVR x y z u v)ᵀ * chartVR x y z u v).map ((↑) : ℝ → ℂ)).permanent
        (((chartVR x y z u v)ᵀ * chartVR x y z u v).map ((↑) : ℝ → ℂ)))).re
      rw [re_det_K31_map]; exact rc x y z u v) A hA hrk
  have h' : 0 ≤ (Matrix.det (K31 (A.map ((↑) : ℝ → ℂ)).permanent (A.map ((↑) : ℝ → ℂ)))).re := h
  rwa [re_det_K31_map] at h'

include cert

/-- **(Re1)** The real order-four theorem in rank `≤ 3`. -/
theorem real_rank3 (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.PosSemidef) (hrk : A.rank ≤ 3) :
    (A.permanent • (1 : Matrix (Perm (Fin 4)) (Perm (Fin 4)) ℝ) - schurPower A).PosSemidef := by
  have hAc : (A.map ((↑) : ℝ → ℂ)).PosSemidef := (posSemidef_map_ofReal_iff A).2 hA
  have hrkc : (A.map ((↑) : ℝ → ℂ)).rank ≤ 3 := (rank_map_ofReal_le_three A).2 hrk
  have h31 := K31_posSemidef_of_det cert hAc hrkc
    (by rw [re_det_K31_map]; exact real_det_K31_nonneg rc A hA hrk)
  have h211 := K211_posSemidef cert hAc hrkc
  have h22 := K22_posSemidef cert hAc hrkc
  have hp : (A.map ((↑) : ℝ → ℂ)).permanent = ((A.permanent : ℝ) : ℂ) :=
    permanent_map Complex.ofRealHom A
  have hpn : (0 : ℂ) ≤ ((A.permanent : ℝ) : ℂ) := Complex.zero_le_real.2 (permanent_nonneg_real hA)
  have hd0 : (A.map ((↑) : ℝ → ℂ)).det = 0 := det_eq_zero_of_rank hrkc
  rw [hp] at h31 h211 h22
  have h := schurPower_defect_posSemidef (A.map ((↑) : ℝ → ℂ)) hAc.isHermitian A.permanent
    hp.le (by rw [hd0]; exact hpn) h31 h211 h22
  have := (pot_map_ofReal_iff A 1).1 (by rw [Complex.ofReal_one, one_mul, hp]; exact h)
  rwa [one_mul] at this

variable (h3 : Order3)
include h3

/-- **(Re2)** The real order-four theorem: `Π(A) ⪯ per(A) I` for every real PSD `A` of order four.
`h3 : Order3` is the order-three theorem
(`ZeroOrder3.order3`). -/
theorem real_pot (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.PosSemidef) :
    (A.permanent • (1 : Matrix (Perm (Fin 4)) (Perm (Fin 4)) ℝ) - schurPower A).PosSemidef := by
  by_cases hrk : A.rank ≤ 3
  · exact real_rank3 cert rc A hA hrk
  have hdet : A.det ≠ 0 := fun h => hrk ((rank_le_three_iff_det A).2 h)
  have hAc : (A.map ((↑) : ℝ → ℂ)).PosSemidef := (posSemidef_map_ofReal_iff A).2 hA
  have hAcD : (A.map ((↑) : ℝ → ℂ)).PosDef := hAc.posDef_iff_det_ne_zero.2 (by
    rw [det_map_ofReal]; exact_mod_cast hdet)
  obtain ⟨t, ht, hBP, hBr⟩ := exists_decrement (A.map ((↑) : ℝ → ℂ)) hAcD 0
  set B : Matrix (Fin 4) (Fin 4) ℝ := A - t • Matrix.single 0 0 (1 : ℝ) with hB
  have hBm : B.map ((↑) : ℝ → ℂ) = decr (A.map ((↑) : ℝ → ℂ)) 0 t := by
    ext a b
    simp [hB, decr, Matrix.single_apply]
    split_ifs <;> simp
  rw [← hBm] at hBP hBr
  have hB1 := real_rank3 cert rc B ((posSemidef_map_ofReal_iff B).1 hBP)
    ((rank_map_ofReal_le_three B).1 hBr)
  have hB2 := (pot_map_ofReal_iff B 1).2 (by rwa [one_mul])
  rw [hBm] at hB2
  have hA' := h3 ((A.map ((↑) : ℝ → ℂ)).submatrix (0 : Fin 4).succAbove (0 : Fin 4).succAbove)
    (hAc.submatrix _)
  have h := decrement_posSemidef (A.map ((↑) : ℝ → ℂ)) 0 t 1 ht.le hB2
    (by simpa only [Complex.ofReal_one, one_mul] using hA')
  have := (pot_map_ofReal_iff A 1).1 h
  rwa [one_mul] at this

/-- The first assertion of `Challenge.main` (real symmetric PSD matrices of order four). -/
theorem main_real_of : ∀ (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.PosSemidef),
    lambdaMax (schurPower_isHermitian hA.isHermitian) = A.permanent :=
  fun A hA => (lambdaMax_eq_permanent_iff_real hA.isHermitian).2 (real_pot cert rc h3 A hA)

end Real

end Results.SoulesPotOrderFour
