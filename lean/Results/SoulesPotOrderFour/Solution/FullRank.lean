import Results.SoulesPotOrderFour.Solution.Rank3
import Results.SoulesPotOrderFour.Solution.Sector
import Results.SoulesPotOrderFour.Solution.Decrement

/-!
# Passage to full rank: `K₂₂, K₂₁₁ ⪰ 0` and `det A ≤ per A` for all PSD `A` of order four

Given the order-three theorem (`Order3`, a hypothesis here) and the rank-`≤ 3` sector theorems of
`Rank3`, the diagonal decrement identity (Lemma 2.1) is applied *at the level of quadratic forms*
on the lifted test vectors `liftH`, `liftG` and on the sign vector, which gives

* `K22_psd_all`, `K211_psd_all`: `K₂₂(per A), K₂₁₁(per A) ⪰ 0` for every PSD `A : Fin 4 → Fin 4 → ℂ`;
* `det_le_permanent`: `det A ≤ per A` for every PSD `A`.

The file also contains small rank facts (`rank_le_or_posDef`, ...) used by `ZeroOrder3`.
-/

open Matrix Equiv
open scoped ComplexOrder

namespace Results.SoulesPotOrderFour

/-- **Order three** permanent-on-top: `Π(C) ⪯ per(C) I` for every PSD `3 × 3` matrix. -/
def Order3 : Prop :=
  ∀ C : Matrix (Fin 3) (Fin 3) ℂ, C.PosSemidef →
    (C.permanent • (1 : Matrix (Perm (Fin 3)) (Perm (Fin 3)) ℂ) - schurPower C).PosSemidef

/-! ### Rank versus kernel -/

theorem det_eq_zero_of_rank_le {n : ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (h : M.rank ≤ n) : M.det = 0 := by
  by_contra hd
  have := Matrix.rank_of_isUnit M ((Matrix.isUnit_iff_isUnit_det M).2 (IsUnit.mk0 _ hd))
  simp at this
  omega

/-- A square matrix with a nonzero kernel vector has rank `≤ n`. -/
theorem rank_le_of_mulVec_eq_zero {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) (h : M *ᵥ v = 0) : M.rank ≤ n := by
  have h1 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have h2 : 0 < Module.finrank ℂ (LinearMap.ker M.mulVecLin) := by
    refine Module.finrank_pos_iff_exists_ne_zero.2
      ⟨⟨v, LinearMap.mem_ker.2 (by rw [Matrix.mulVecLin_apply]; exact h)⟩, fun h0 => hv ?_⟩
    simpa using congrArg Subtype.val h0
  rw [Module.finrank_pi, Fintype.card_fin] at h1
  unfold Matrix.rank
  omega

/-- A PSD matrix of order `n + 1` has rank `≤ n` or is positive definite. -/
theorem rank_le_or_posDef {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : A.PosSemidef) :
    A.rank ≤ n ∨ A.PosDef := by
  by_cases h : A.det = 0
  · obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    exact Or.inl (rank_le_of_mulVec_eq_zero A v hv hAv)
  · exact Or.inr (hA.posDef_iff_det_ne_zero.2 h)

theorem signCofactor_isHermitian {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : A.IsHermitian) :
    (signCofactorMatrix A).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, signCofactorMatrix, of_apply, star_mul', star_pow, star_neg,
    star_one, ← det_conjTranspose, conjTranspose_submatrix, hA.eq, hA.apply i j, add_comm j.val]

/-! ### The decrement at the level of defect forms -/

/-- Lemma 2.1 with `κ = 1`. -/
theorem decrement_one {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (i : Fin (m + 1)) (t : ℝ)
    (ht : 0 ≤ t) (hB : (defect 1 (decr A i t)).PosSemidef)
    (hA' : (defect 1 (A.submatrix i.succAbove i.succAbove)).PosSemidef) :
    (defect 1 A).PosSemidef := by
  rw [defect_eq_decr 1 A i t]
  exact hB.add ((indOp_posSemidef 1 A i hA').smul (Complex.zero_le_real.2 ht))

/-- If the defect form of `A - tE₀₀` is nonnegative on `x`, so is that of `A`
(`A` PSD of order four, given the order-three theorem). -/
theorem form_nonneg_of_decr (h3 : Order3) {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : A.PosSemidef)
    (t : ℝ) (ht : 0 ≤ t) (x : Perm (Fin 4) → ℂ)
    (hB : 0 ≤ star x ⬝ᵥ (defect 1 (decr A 0 t) *ᵥ x)) : 0 ≤ star x ⬝ᵥ (defect 1 A *ᵥ x) := by
  have hI : (indOp 1 A 0).PosSemidef :=
    indOp_posSemidef 1 A 0 (by rw [defect_one]; exact h3 _ (hA.submatrix _))
  have e : star x ⬝ᵥ (defect 1 A *ᵥ x) = star x ⬝ᵥ (defect 1 (decr A 0 t) *ᵥ x) +
      (t : ℂ) * (star x ⬝ᵥ (indOp 1 A 0 *ᵥ x)) := by
    rw [defect_eq_decr 1 A 0 t, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
      smul_eq_mul]
  rw [e]
  exact add_nonneg hB (mul_nonneg (Complex.zero_le_real.2 ht) (hI.dotProduct_mulVec_nonneg x))

/-! ### Quadratic forms of the compressed matrices -/

theorem quad_compress {m n : ℕ} (Q : Matrix (Fin m) (Fin n) ℂ) (hQ : Qᴴ = Qᵀ)
    (X : Matrix (Fin m) (Fin m) ℂ) (w : Fin n → ℂ) :
    star w ⬝ᵥ ((Qᵀ * X * Q) *ᵥ w) = star (Q *ᵥ w) ⬝ᵥ (X *ᵥ (Q *ᵥ w)) := by
  rw [← hQ]
  simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem K22_defect_form (M : Matrix (Fin 4) (Fin 4) ℂ) (w : Fin 2 → ℂ) :
    star (liftH (star (Q2 *ᵥ w))) ⬝ᵥ (defect 1 M *ᵥ liftH (star (Q2 *ᵥ w))) =
      8 * (star w ⬝ᵥ (K22 M.permanent M *ᵥ w)) := by
  rw [defect_one, liftH_form', K22, quad_compress _ Q2_conjTranspose]
  simp only [star_star]

theorem K211_defect_form (M : Matrix (Fin 4) (Fin 4) ℂ) (y : Fin 3 → ℂ) :
    star (liftG (Q3 *ᵥ y)) ⬝ᵥ (defect 1 M *ᵥ liftG (Q3 *ᵥ y)) =
      6 * (star y ⬝ᵥ (K211 M.permanent M *ᵥ y)) := by
  rw [defect_one, liftG_form, K211, quad_compress _ Q3_conjTranspose]

/-- On the sign vector the defect form is `24 (per M - det M)`. -/
theorem sign_defect_form (M : Matrix (Fin 4) (Fin 4) ℂ) :
    star (fun σ : Perm (Fin 4) => ((permSgn σ : ℤ) : ℂ)) ⬝ᵥ
        (defect 1 M *ᵥ fun σ : Perm (Fin 4) => ((permSgn σ : ℤ) : ℂ)) =
      24 * (M.permanent - M.det) := by
  have h : ∀ σ : Perm (Fin 4), ((permSgn σ : ℤ) : ℂ) * ((permSgn σ : ℤ) : ℂ) = 1 := fun σ => by
    exact_mod_cast permSgn_mul_self σ
  have hn : star (fun σ : Perm (Fin 4) => ((permSgn σ : ℤ) : ℂ)) ⬝ᵥ
      (fun σ : Perm (Fin 4) => ((permSgn σ : ℤ) : ℂ)) = 24 := by
    simp only [dotProduct, Pi.star_apply, star_intCast, h, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, nsmul_eq_mul]
    norm_num [Nat.factorial]
  rw [defect_one, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
    star_sign_dotProduct_schurPower, hn, smul_eq_mul]
  ring

section Main

variable {A : Matrix (Fin 4) (Fin 4) ℂ}

/-- **(F1)** `K₂₂(per A) ⪰ 0` for every PSD `A` of order four. -/
theorem K22_psd_all (cert : ComplexCerts) (h3 : Order3) (hA : A.PosSemidef) : (K22 A.permanent A).PosSemidef := by
  rcases rank_le_or_posDef hA with hrk | hpd
  · exact K22_posSemidef cert hA hrk
  · obtain ⟨t, ht, hB, hBr⟩ := exists_decrement A hpd 0
    have hK := K22_posSemidef cert hB hBr
    refine PosSemidef.of_dotProduct_mulVec_nonneg (K22_isHermitian hA.isHermitian) fun w => ?_
    have h2 := form_nonneg_of_decr h3 hA t ht.le (liftH (star (Q2 *ᵥ w)))
      (by rw [K22_defect_form]; exact mul_nonneg (by norm_num) (hK.dotProduct_mulVec_nonneg w))
    rw [K22_defect_form] at h2
    exact le_of_mul_le_mul_left (by rwa [mul_zero]) (by norm_num : (0 : ℂ) < 8)

/-- **(F1)** `K₂₁₁(per A) ⪰ 0` for every PSD `A` of order four. -/
theorem K211_psd_all (cert : ComplexCerts) (h3 : Order3) (hA : A.PosSemidef) :
    (K211 A.permanent A).PosSemidef := by
  rcases rank_le_or_posDef hA with hrk | hpd
  · exact K211_posSemidef cert hA hrk
  · obtain ⟨t, ht, hB, hBr⟩ := exists_decrement A hpd 0
    have hK := K211_posSemidef cert hB hBr
    have hH : (K211 A.permanent A).IsHermitian := by
      unfold K211
      rw [← Q3_conjTranspose]
      exact isHermitian_conjTranspose_mul_mul _ (isHermitian_smul_one_sub
        (star_permanent_of_isHermitian hA.isHermitian) (signCofactor_isHermitian hA.isHermitian))
    refine PosSemidef.of_dotProduct_mulVec_nonneg hH fun y => ?_
    have h2 := form_nonneg_of_decr h3 hA t ht.le (liftG (Q3 *ᵥ y))
      (by rw [K211_defect_form]; exact mul_nonneg (by norm_num) (hK.dotProduct_mulVec_nonneg y))
    rw [K211_defect_form] at h2
    exact le_of_mul_le_mul_left (by rwa [mul_zero]) (by norm_num : (0 : ℂ) < 6)

/-- **(F2)** `det A ≤ per A` for every PSD `A` of order four (complex order). -/
theorem det_le_permanent (h3 : Order3) (hA : A.PosSemidef) : A.det ≤ A.permanent := by
  by_cases hd : A.det = 0
  · rw [hd]; exact permanent_nonneg hA
  · have hpd := hA.posDef_iff_det_ne_zero.2 hd
    obtain ⟨t, ht, hB, hBr⟩ := exists_decrement A hpd 0
    have h2 := form_nonneg_of_decr h3 hA t ht.le (fun σ : Perm (Fin 4) => ((permSgn σ : ℤ) : ℂ))
      (by
        rw [sign_defect_form, det_eq_zero_of_rank hBr, sub_zero]
        exact mul_nonneg (by norm_num) (permanent_nonneg hB))
    rw [sign_defect_form] at h2
    exact sub_nonneg.1 (le_of_mul_le_mul_left (by rwa [mul_zero]) (by norm_num : (0 : ℂ) < 24))

end Main

end Results.SoulesPotOrderFour
