import Results.SoulesPotOrderFour.Solution.Rank3
import Results.SoulesPotOrderFour.Solution.Decrement
import Results.SoulesPotOrderFour.Solution.Sector
import Results.SoulesPotOrderFour.Solution.Glue

/-!
# The universal `19/18` bound (Theorem 1.2, first sentence) and the zero-entry `λ_max` statement

All hypotheses that come from other modules are stated explicitly (their shapes are those of
`ComplexCerts`, `Order3`, `BoundCert`, `zero_all` of the other workers):

* `bc` : the `19/18` chart inequality (`BoundCert`).
* `h3` : the order-three theorem (`Order3`).
* `hz` : the zero-off-diagonal theorem (`zero_all`).

* `bound_rank3` (B1): `D_{19/18}(A) ⪰ 0` for PSD `A` of rank `≤ 3`.
* `bound_all` (B2): the same for every PSD `A` of order four (diagonal decrement).
* `theorem_1_2_bounds_of`, `theorem_1_2_zero_offdiag_of` (B3): the `Challenge` shapes.
-/

open Matrix Equiv
open scoped ComplexOrder

namespace Results.SoulesPotOrderFour

/-! ### Quadratic-form criteria -/

private theorem posSemidef_of_re_nonneg {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    (hM : M.IsHermitian) (h : ∀ y : n → ℂ, 0 ≤ (star y ⬝ᵥ (M *ᵥ y)).re) : M.PosSemidef :=
  .of_dotProduct_mulVec_nonneg hM fun y =>
    Complex.nonneg_iff.2 ⟨h y, by simpa using (hM.im_star_dotProduct_mulVec_self y).symm⟩

private theorem K31_isHermitian_real {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : A.IsHermitian) {lam : ℂ}
    (hl : star lam = lam) : (K31 lam A).IsHermitian := by
  unfold K31
  rw [← Q3_conjTranspose]
  exact isHermitian_conjTranspose_mul_mul _
    (isHermitian_smul_one_sub hl (cofactorPermMatrix_isHermitian hA))

/-- Every vector of `ℂ³` is `![q₀ + i q₃, q₁ + i q₄, q₂ + i q₅]` for real `q`. -/
private theorem exists_real_coords (y : Fin 3 → ℂ) : ∃ q0 q1 q2 q3 q4 q5 : ℝ,
    y = ![(q0 : ℂ) + (q3 : ℂ) * Complex.I, (q1 : ℂ) + (q4 : ℂ) * Complex.I,
      (q2 : ℂ) + (q5 : ℂ) * Complex.I] := by
  refine ⟨(y 0).re, (y 1).re, (y 2).re, (y 0).im, (y 1).im, (y 2).im, ?_⟩
  ext i
  fin_cases i <;> simp [Complex.re_add_im]

/-! ### (B1) rank at most three -/

section Rank3

variable (cert : ComplexCerts)
  (bc : ∀ (x a b z c d e f q0 q1 q2 q3 q4 q5 : ℝ),
    0 ≤ (star ![(q0 : ℂ) + (q3 : ℂ) * Complex.I, (q1 : ℂ) + (q4 : ℂ) * Complex.I,
        (q2 : ℂ) + (q5 : ℂ) * Complex.I] ⬝ᵥ
      (K31 ((19 / 18 : ℂ) * ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f).permanent)
        ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f) *ᵥ
        ![(q0 : ℂ) + (q3 : ℂ) * Complex.I, (q1 : ℂ) + (q4 : ℂ) * Complex.I,
          (q2 : ℂ) + (q5 : ℂ) * Complex.I])).re)

include bc in
/-- `K₃₁(19/18 · per A) ⪰ 0` for PSD `A` of rank `≤ 3`. -/
theorem K31_bound_posSemidef {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : A.PosSemidef)
    (hrk : A.rank ≤ 3) : (K31 ((19 / 18 : ℂ) * A.permanent) A).PosSemidef := by
  have hl : star ((19 / 18 : ℂ) * A.permanent) = (19 / 18 : ℂ) * A.permanent := by
    rw [star_mul', star_permanent_of_isHermitian hA.isHermitian]
    congr 1
    rw [Complex.star_def, map_div₀]
    simp [Complex.conj_ofNat]
  refine posSemidef_of_re_nonneg (K31_isHermitian_real hA.isHermitian hl) fun y => ?_
  obtain ⟨q0, q1, q2, q3, q4, q5, rfl⟩ := exists_real_coords y
  exact transfer_rank3_of (homog_quad_K31 (19 / 18 : ℂ) _)
    (fun x a b z c d e f => bc x a b z c d e f q0 q1 q2 q3 q4 q5) A hA hrk

include cert bc in
/-- **(B1)** `Π(A) ⪯ (19/18) per(A) I` for PSD `A` of order four and rank at most three. -/
theorem bound_rank3 {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : A.PosSemidef) (hrk : A.rank ≤ 3) :
    (defect ((19 / 18 : ℝ) : ℂ) A).PosSemidef := by
  have hp0 : 0 ≤ A.permanent := permanent_nonneg hA
  set lam : ℝ := 19 / 18 * A.permanent.re with hlam
  have hlamC : (lam : ℂ) = ((19 / 18 : ℝ) : ℂ) * A.permanent := by
    rw [hlam, Complex.ofReal_mul, permanent_eq_ofReal_re hA]
  have h19 : ((19 / 18 : ℝ) : ℂ) = (19 / 18 : ℂ) := by push_cast; rfl
  have hle : A.permanent ≤ (lam : ℂ) := by
    rw [hlamC, h19]
    have : (19 / 18 : ℂ) * A.permanent = A.permanent + (1 / 18 : ℂ) * A.permanent := by ring
    rw [this]
    have h18 : (0 : ℂ) ≤ 1 / 18 := by simp
    exact le_add_of_nonneg_right (mul_nonneg h18 hp0)
  have h31 : (K31 (lam : ℂ) A).PosSemidef := by
    rw [hlamC, h19]; exact K31_bound_posSemidef bc hA hrk
  have h211 : (K211 (lam : ℂ) A).PosSemidef := K211_mono hle (K211_posSemidef cert hA hrk)
  have h22 : (K22 (lam : ℂ) A).PosSemidef := K22_mono hle (K22_posSemidef cert hA hrk)
  have hdet : A.det ≤ (lam : ℂ) := by
    rw [det_eq_zero_of_rank hrk]; exact hp0.trans hle
  have := schurPower_defect_posSemidef A hA.isHermitian lam hle hdet h31 h211 h22
  rw [hlamC] at this
  exact this

end Rank3

/-! ### (B2) every rank -/

/-- A PSD `4 × 4` matrix that is not positive definite has rank at most `3`. -/
private theorem rank_le_three_of_not_posDef {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : A.PosSemidef)
    (h : ¬ A.PosDef) : A.rank ≤ 3 := by
  rw [hA.posDef_iff_det_ne_zero, not_not] at h
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have h1 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have h2 : 0 < Module.finrank ℂ (LinearMap.ker A.mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.2
      ⟨⟨v, LinearMap.mem_ker.2 (by rw [Matrix.mulVecLin_apply]; exact hAv)⟩,
        fun h0 => hv (congrArg Subtype.val h0)⟩
  rw [Module.finrank_pi, Fintype.card_fin] at h1
  unfold Matrix.rank
  omega

section All

variable (cert : ComplexCerts)
  (bc : ∀ (x a b z c d e f q0 q1 q2 q3 q4 q5 : ℝ),
    0 ≤ (star ![(q0 : ℂ) + (q3 : ℂ) * Complex.I, (q1 : ℂ) + (q4 : ℂ) * Complex.I,
        (q2 : ℂ) + (q5 : ℂ) * Complex.I] ⬝ᵥ
      (K31 ((19 / 18 : ℂ) * ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f).permanent)
        ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f) *ᵥ
        ![(q0 : ℂ) + (q3 : ℂ) * Complex.I, (q1 : ℂ) + (q4 : ℂ) * Complex.I,
          (q2 : ℂ) + (q5 : ℂ) * Complex.I])).re)
  (h3 : ∀ C : Matrix (Fin 3) (Fin 3) ℂ, C.PosSemidef →
    (C.permanent • (1 : Matrix (Perm (Fin 3)) (Perm (Fin 3)) ℂ) - schurPower C).PosSemidef)

include cert bc h3 in
/-- **(B2)** `Π(A) ⪯ (19/18) per(A) I` for every PSD `A` of order four. -/
theorem bound_all {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : A.PosSemidef) :
    (defect ((19 / 18 : ℝ) : ℂ) A).PosSemidef := by
  by_cases hpd : A.PosDef
  · obtain ⟨t, ht, hB, hBrk⟩ := exists_decrement A hpd (0 : Fin 4)
    have hB' := bound_rank3 cert bc hB hBrk
    have hA3 : (A.submatrix (0 : Fin 4).succAbove (0 : Fin 4).succAbove).PosSemidef :=
      hA.submatrix _
    have h1 := h3 _ hA3
    have hA' : (defect ((19 / 18 : ℝ) : ℂ)
        (A.submatrix (0 : Fin 4).succAbove (0 : Fin 4).succAbove)).PosSemidef := by
      refine defect_mono _ (κ := 1) (by norm_num) (permanent_nonneg hA3) ?_
      rw [Complex.ofReal_one, defect_one]
      exact h1
    exact decrement_posSemidef A 0 t (19 / 18) ht.le hB' hA'
  · exact bound_rank3 cert bc hA (rank_le_three_of_not_posDef hA hpd)

end All

/-! ### (B3) the Challenge shapes -/

/-- **Theorem 1.2, first sentence** (shape of `Challenge.theorem_1_2_bounds`). -/
theorem theorem_1_2_bounds_of (cert : ComplexCerts)
    (bc : ∀ (x a b z c d e f q0 q1 q2 q3 q4 q5 : ℝ),
    0 ≤ (star ![(q0 : ℂ) + (q3 : ℂ) * Complex.I, (q1 : ℂ) + (q4 : ℂ) * Complex.I,
        (q2 : ℂ) + (q5 : ℂ) * Complex.I] ⬝ᵥ
      (K31 ((19 / 18 : ℂ) * ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f).permanent)
        ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f) *ᵥ
        ![(q0 : ℂ) + (q3 : ℂ) * Complex.I, (q1 : ℂ) + (q4 : ℂ) * Complex.I,
          (q2 : ℂ) + (q5 : ℂ) * Complex.I])).re)
    (h3 : ∀ C : Matrix (Fin 3) (Fin 3) ℂ, C.PosSemidef →
      (C.permanent • (1 : Matrix (Perm (Fin 3)) (Perm (Fin 3)) ℂ) - schurPower C).PosSemidef)
    (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef) :
    A.permanent.re ≤ lambdaMax (schurPower_isHermitian hA.isHermitian) ∧
      lambdaMax (schurPower_isHermitian hA.isHermitian) ≤ (19 / 18 : ℝ) * A.permanent.re :=
  ⟨re_permanent_le_lambdaMax hA.isHermitian,
    (lambdaMax_le_mul_permanent_iff hA.isHermitian (19 / 18)).2 (bound_all cert bc h3 hA)⟩

/-- **Theorem 1.2, second sentence** (shape of `Challenge.theorem_1_2_zero_offdiag`), from the
zero-off-diagonal Loewner theorem `hz` (`zero_all`). -/
theorem theorem_1_2_zero_offdiag_of
    (hz : ∀ A : Matrix (Fin 4) (Fin 4) ℂ, A.PosSemidef → ∀ i j : Fin 4, i ≠ j → A i j = 0 →
      (A.permanent • (1 : Matrix (Perm (Fin 4)) (Perm (Fin 4)) ℂ) - schurPower A).PosSemidef)
    (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef) (hzero : ∃ i j, i ≠ j ∧ A i j = 0) :
    (lambdaMax (schurPower_isHermitian hA.isHermitian) : ℂ) = A.permanent := by
  obtain ⟨i, j, hij, h0⟩ := hzero
  exact (lambdaMax_eq_permanent_iff_complex hA.isHermitian).2 (hz A hA i j hij h0)

end Results.SoulesPotOrderFour
