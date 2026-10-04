import Results.SoulesPotOrderFour.Solution.FullRank

/-!
# A zero off-diagonal entry, and order three

* `ZeroCert`: the zero-chart certificate `0 ≤ det K₃₁` on `V₀ᴴ V₀` (hypothesis, supplied later).
* `zero_rank3` (Z1): PSD, rank `≤ 3`, `a_ij = 0` (`i ≠ j`) implies `Π(A) ⪯ per(A) I`.
* `order3` (Z2): order-three permanent-on-top, proved from `zero_rank3` and the decrement.
* `zero_all` (Z3): the same for every PSD `A` of order four with a zero off-diagonal entry.
-/

open Matrix Equiv
open scoped ComplexOrder

namespace Results.SoulesPotOrderFour

/-- The zero-chart certificate: `det K₃₁ ≥ 0` on `A = V₀ᴴ V₀`, `V₀ = chartVz a b c d e f`. -/
def ZeroCert : Prop :=
  ∀ a b c d e f : ℝ,
    0 ≤ (Matrix.det (K31 ((chartVz a b c d e f)ᴴ * chartVz a b c d e f).permanent
      ((chartVz a b c d e f)ᴴ * chartVz a b c d e f))).re

theorem exists_perm_pair : ∀ i j : Fin 4, i ≠ j → ∃ π : Perm (Fin 4), π 0 = i ∧ π 1 = j := by
  decide +kernel

theorem exists_third : ∀ i j : Fin 4, i ≠ j → ∃ k : Fin 4, k ≠ i ∧ k ≠ j := by
  decide +kernel

/-! ### Z1: rank at most three -/

section Z1

variable (cert : ComplexCerts) (zc : ZeroCert)
include cert zc

theorem zero_rank3_01 {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : A.PosSemidef) (hrk : A.rank ≤ 3)
    (h01 : A 0 1 = 0) :
    (A.permanent • (1 : Matrix (Perm (Fin 4)) (Perm (Fin 4)) ℂ) - schurPower A).PosSemidef := by
  have hdet := transfer_zero_of homog_det_K31 zc A hA hrk h01
  have h31 := K31_posSemidef_of_det cert hA hrk hdet
  have h211 := K211_posSemidef cert hA hrk
  have h22 := K22_posSemidef cert hA hrk
  have hlam : ((A.permanent.re : ℝ) : ℂ) = A.permanent := permanent_eq_ofReal_re hA
  rw [← hlam] at h31 h211 h22 ⊢
  have hd0 : A.det = 0 := det_eq_zero_of_rank hrk
  exact schurPower_defect_posSemidef A hA.isHermitian _ hlam.ge (by rw [hd0, hlam]; exact permanent_nonneg hA)
    h31 h211 h22

/-- **(Z1)** -/
theorem zero_rank3 {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : A.PosSemidef) (hrk : A.rank ≤ 3)
    {i j : Fin 4} (hij : i ≠ j) (hz : A i j = 0) :
    (A.permanent • (1 : Matrix (Perm (Fin 4)) (Perm (Fin 4)) ℂ) - schurPower A).PosSemidef := by
  obtain ⟨π, h0, h1⟩ := exists_perm_pair i j hij
  have h := zero_rank3_01 cert zc (A := A.submatrix π π) (hA.submatrix _)
    ((Matrix.rank_submatrix_le _ _ _).trans hrk) (by simpa [h0, h1] using hz)
  have := (pot_submatrix_equiv 1 A π).1 (by simpa [defect_one, permanent_submatrix_perm] using h)
  simpa [defect_one] using this

end Z1

/-! ### Z2: order three -/

section ExtendOne

theorem posSemidef_extendOne {m : ℕ} {C : Matrix (Fin m) (Fin m) ℂ} (hC : C.PosSemidef) :
    (extendOne C).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext a b
    refine Fin.lastCases ?_ (fun a' => ?_) a <;> refine Fin.lastCases ?_ (fun b' => ?_) b <;>
      simp [conjTranspose_apply, hC.isHermitian.apply]
  · have e : star x ⬝ᵥ (extendOne C *ᵥ x) = star (fun a => x a.castSucc) ⬝ᵥ
        (C *ᵥ fun a => x a.castSucc) + star (x (Fin.last m)) * x (Fin.last m) := by
      simp [dotProduct, mulVec, Fin.sum_univ_castSucc]
    rw [e]
    exact add_nonneg (hC.dotProduct_mulVec_nonneg _) (star_mul_self_nonneg _)

/-- A kernel vector of `C` gives one of `C ⊕ [1]`. -/
theorem rank_extendOne_le {m : ℕ} {C : Matrix (Fin m) (Fin m) ℂ} (v : Fin m → ℂ) (hv : v ≠ 0)
    (h : C *ᵥ v = 0) : (extendOne C).rank ≤ m := by
  refine rank_le_of_mulVec_eq_zero _ (fun a => Fin.lastCases (0 : ℂ) v a) ?_ ?_
  · intro h0
    exact hv (funext fun a => by simpa using congrFun h0 a.castSucc)
  · funext a
    refine Fin.lastCases ?_ (fun a' => ?_) a
    · simp [mulVec, dotProduct, Fin.sum_univ_castSucc]
    · simpa [mulVec, dotProduct, Fin.sum_univ_castSucc] using congrFun h a'

end ExtendOne

section Z2

variable (cert : ComplexCerts) (zc : ZeroCert)
include cert zc

/-- Order three for a singular PSD matrix: `C ⊕ [1]` has rank `≤ 3` and a zero entry. -/
theorem order3_of_det_eq_zero {C : Matrix (Fin 3) (Fin 3) ℂ} (hC : C.PosSemidef)
    (hd : C.det = 0) :
    (C.permanent • (1 : Matrix (Perm (Fin 3)) (Perm (Fin 3)) ℂ) - schurPower C).PosSemidef := by
  obtain ⟨v, hv, hCv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  have h := zero_rank3 cert zc (posSemidef_extendOne hC) (rank_extendOne_le v hv hCv)
    (i := Fin.castSucc 0) (j := Fin.last 3) (Fin.castSucc_lt_last _).ne (extendOne_c_last C 0)
  have := pot_of_extendOne 1 C (by simpa [defect_one] using h)
  simpa [defect_one] using this

/-- **(Z2)** Order-three permanent-on-top (proved). -/
theorem order3 : Order3 := by
  intro C hC
  by_cases hd : C.det = 0
  · exact order3_of_det_eq_zero cert zc hC hd
  · have hpd := hC.posDef_iff_det_ne_zero.2 hd
    obtain ⟨t, ht, hB, hBr⟩ := exists_decrement C hpd 0
    have hB' := order3_of_det_eq_zero cert zc hB (det_eq_zero_of_rank_le hBr)
    have hA' := pot_two (C.submatrix (0 : Fin 3).succAbove (0 : Fin 3).succAbove)
      (hC.submatrix _).isHermitian
    have := decrement_one C 0 t ht.le (by simpa [defect_one] using hB')
      (by simpa [defect_one] using hA')
    simpa [defect_one] using this

end Z2

/-! ### Z3: zero entry at every rank -/

section Z3

variable (cert : ComplexCerts) (zc : ZeroCert)
include cert zc

theorem zero_all_of {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : A.PosSemidef) {i j : Fin 4} (hij : i ≠ j)
    (hz : A i j = 0) :
    (A.permanent • (1 : Matrix (Perm (Fin 4)) (Perm (Fin 4)) ℂ) - schurPower A).PosSemidef := by
  rcases rank_le_or_posDef hA with hrk | hpd
  · exact zero_rank3 cert zc hA hrk hij hz
  · obtain ⟨k, hki, hkj⟩ := exists_third i j hij
    obtain ⟨t, ht, hB, hBr⟩ := exists_decrement A hpd k
    have hB' := zero_rank3 cert zc hB hBr hij (by rw [decr_apply_of_ne A k t hij]; exact hz)
    have hA' := order3 cert zc _ (hA.submatrix k.succAbove)
    have := decrement_one A k t ht.le (by simpa [defect_one] using hB')
      (by simpa [defect_one] using hA')
    simpa [defect_one] using this

/-- **(Z3)** Every PSD `A` of order four with a zero off-diagonal entry satisfies
`Π(A) ⪯ per(A) I`. -/
theorem zero_all {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : A.PosSemidef)
    (hzero : ∃ i j, i ≠ j ∧ A i j = 0) :
    (A.permanent • (1 : Matrix (Perm (Fin 4)) (Perm (Fin 4)) ℂ) - schurPower A).PosSemidef := by
  obtain ⟨i, j, hij, hz⟩ := hzero
  exact zero_all_of cert zc hA hij hz

end Z3

end Results.SoulesPotOrderFour
