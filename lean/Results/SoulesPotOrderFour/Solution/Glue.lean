import Results.SoulesPotOrderFour.Defs
import Mathlib.Analysis.Matrix.Order

/-!
# Glue: row sums of `Π(A)`, `λ_max` versus the Loewner order, real versus complex

* `schurPower_mulVec_one`: `Π(A) 1 = per(A) 1`.
* `lambdaMax_le_iff`, `exists_eigenvector_lambdaMax`, `le_lambdaMax_of_eigen`: spectral facts
  about `lambdaMax` (any `RCLike` field, in particular `ℝ` and `ℂ`).
* `re_permanent_le_lambdaMax`, `lambdaMax_le_mul_permanent_iff`, `lambdaMax_eq_permanent_iff`.
* `pot_map_ofReal_iff`: transport of the Loewner statement from a real matrix to its complex image.
-/

open Matrix Equiv
open scoped ComplexOrder MatrixOrder

namespace Results.SoulesPotOrderFour

section RowSum

variable {R : Type*} [CommSemiring R] {n : ℕ}

/-- Every row of `Π(A)` sums to `per(A)`. -/
theorem sum_schurPower_row (A : Matrix (Fin n) (Fin n) R) (σ : Perm (Fin n)) :
    ∑ τ : Perm (Fin n), schurPower A σ τ = A.permanent := by
  rw [← Matrix.permanent_transpose, Matrix.permanent]
  simp only [schurPower, of_apply, transpose_apply]
  rw [← Equiv.sum_comp (Equiv.mulRight σ⁻¹) (fun τ' : Perm (Fin n) => ∏ k, A k (τ' k))]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simpa using Equiv.prod_comp σ (fun k => A k (τ (σ⁻¹ k)))

/-- `Π(A) 1 = per(A) 1`. -/
theorem schurPower_mulVec_one (A : Matrix (Fin n) (Fin n) R) :
    schurPower A *ᵥ (1 : Perm (Fin n) → R) = A.permanent • (1 : Perm (Fin n) → R) := by
  ext σ
  simp [Matrix.mulVec, dotProduct, sum_schurPower_row]

end RowSum

section Spectral

variable {𝕜 : Type*} [RCLike 𝕜] {m : Type*} [Fintype m] [DecidableEq m]

theorem posSemidef_smul_one_sub_iff {M : Matrix m m 𝕜} (hM : M.IsHermitian) (r : ℝ) :
    ((r : 𝕜) • (1 : Matrix m m 𝕜) - M).PosSemidef ↔ ∀ i, hM.eigenvalues i ≤ r := by
  have h : (r : 𝕜) • (1 : Matrix m m 𝕜) - M = Unitary.conjStarAlgAut 𝕜 _ hM.eigenvectorUnitary
      (diagonal fun i => ((r - hM.eigenvalues i : ℝ) : 𝕜)) := by
    conv_lhs => rw [hM.spectral_theorem]
    rw [← map_one (Unitary.conjStarAlgAut 𝕜 _ hM.eigenvectorUnitary), ← map_smul, ← map_sub]
    congr 1
    ext a b
    by_cases hab : a = b
    · subst hab; simp [Matrix.diagonal_apply_eq, Algebra.algebraMap_eq_smul_one, sub_smul]
    · simp [hab]
  rw [h, Unitary.conjStarAlgAut_apply]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff Unitary.isUnit_coe]
  simp [Matrix.posSemidef_diagonal_iff, sub_nonneg]

variable [Nonempty m]

/-- `λ_max(M) ≤ r` iff `r I - M` is positive semidefinite. -/
theorem lambdaMax_le_iff {M : Matrix m m 𝕜} (hM : M.IsHermitian) (r : ℝ) :
    lambdaMax hM ≤ r ↔ ((r : 𝕜) • (1 : Matrix m m 𝕜) - M).PosSemidef := by
  rw [posSemidef_smul_one_sub_iff hM, lambdaMax, Finset.sup'_le_iff]
  simp

/-- `λ_max(M)` is attained by a nonzero eigenvector. -/
theorem exists_eigenvector_lambdaMax {M : Matrix m m 𝕜} (hM : M.IsHermitian) :
    ∃ y : m → 𝕜, y ≠ 0 ∧ M *ᵥ y = (lambdaMax hM : 𝕜) • y := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty hM.eigenvalues
  refine ⟨⇑(hM.eigenvectorBasis i), fun h0 => ?_, ?_⟩
  · have h1 := OrthonormalBasis.norm_eq_one hM.eigenvectorBasis i
    have : hM.eigenvectorBasis i = 0 := by ext j; simpa using congrFun h0 j
    rw [this] at h1
    simp at h1
  · rw [hM.mulVec_eigenvectorBasis, lambdaMax, hi, RCLike.real_smul_eq_coe_smul (K := 𝕜)]

/-- Every (real) eigenvalue is at most `λ_max`. -/
theorem le_lambdaMax_of_eigen {M : Matrix m m 𝕜} (hM : M.IsHermitian) {μ : ℝ} {y : m → 𝕜}
    (hy : y ≠ 0) (h : M *ᵥ y = (μ : 𝕜) • y) : μ ≤ lambdaMax hM := by
  have h0 := ((lambdaMax_le_iff hM (lambdaMax hM)).1 le_rfl).re_dotProduct_nonneg y
  have hyy := (RCLike.pos_iff.1 (dotProduct_star_self_pos_iff.2 hy)).1
  have : ((lambdaMax hM : 𝕜) • (1 : Matrix m m 𝕜) - M) *ᵥ y = ((lambdaMax hM - μ : ℝ) : 𝕜) • y := by
    rw [Matrix.sub_mulVec, h, Matrix.smul_mulVec, Matrix.one_mulVec]
    push_cast
    rw [sub_smul]
  rw [this, dotProduct_smul, smul_eq_mul, RCLike.re_ofReal_mul] at h0
  have := nonneg_of_mul_nonneg_left h0 hyy
  linarith

end Spectral

section PermLoewner

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- `per(A) ≤ λ_max(Π(A))` for Hermitian `A` (`per A` is an eigenvalue with eigenvector `1`). -/
theorem re_permanent_le_lambdaMax {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    RCLike.re A.permanent ≤ lambdaMax (schurPower_isHermitian hA) := by
  refine le_lambdaMax_of_eigen _ (y := 1) one_ne_zero ?_
  rw [ofReal_re_permanent_of_isHermitian hA]
  exact schurPower_mulVec_one A

/-- `λ_max(Π(A)) ≤ κ per(A)` iff `Π(A) ⪯ κ per(A) I`. -/
theorem lambdaMax_le_mul_permanent_iff {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian)
    (κ : ℝ) :
    lambdaMax (schurPower_isHermitian hA) ≤ κ * RCLike.re A.permanent ↔
      (((κ : 𝕜) * A.permanent) • (1 : Matrix (Perm (Fin n)) (Perm (Fin n)) 𝕜) -
        schurPower A).PosSemidef := by
  rw [lambdaMax_le_iff]
  have : ((κ * RCLike.re A.permanent : ℝ) : 𝕜) = κ * A.permanent := by
    rw [RCLike.ofReal_mul, ofReal_re_permanent_of_isHermitian hA]
  rw [this]

/-- `λ_max(Π(A)) = per(A)` iff `Π(A) ⪯ per(A) I`, for Hermitian `A` over `ℝ` or `ℂ`. -/
theorem lambdaMax_eq_permanent_iff {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    (lambdaMax (schurPower_isHermitian hA) : 𝕜) = A.permanent ↔
      (A.permanent • (1 : Matrix (Perm (Fin n)) (Perm (Fin n)) 𝕜) - schurPower A).PosSemidef := by
  have h1 := lambdaMax_le_mul_permanent_iff hA 1
  simp only [RCLike.ofReal_one, one_mul] at h1
  have h2 := re_permanent_le_lambdaMax hA
  rw [← h1]
  constructor
  · intro h
    have := congrArg RCLike.re h
    simp only [RCLike.ofReal_re] at this
    exact this.le
  · intro h
    have h3 : lambdaMax (schurPower_isHermitian hA) = RCLike.re A.permanent := le_antisymm h h2
    rw [h3, ofReal_re_permanent_of_isHermitian hA]

/-- The real statement of `Challenge.main` (first part), as a Loewner equivalence over `ℝ`. -/
theorem lambdaMax_eq_permanent_iff_real {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    lambdaMax (schurPower_isHermitian hA) = A.permanent ↔
      (A.permanent • (1 : Matrix (Perm (Fin n)) (Perm (Fin n)) ℝ) - schurPower A).PosSemidef := by
  simpa using lambdaMax_eq_permanent_iff hA

/-- The complex statement (`Challenge.main` second part) as a Loewner equivalence over `ℂ`. -/
theorem lambdaMax_eq_permanent_iff_complex {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (lambdaMax (schurPower_isHermitian hA) : ℂ) = A.permanent ↔
      (A.permanent • (1 : Matrix (Perm (Fin n)) (Perm (Fin n)) ℂ) - schurPower A).PosSemidef :=
  lambdaMax_eq_permanent_iff hA

end PermLoewner

section RealToComplex

variable {n : ℕ}

theorem schurPower_map {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (A : Matrix (Fin n) (Fin n) R) : schurPower (A.map f) = (schurPower A).map f := by
  ext σ τ; simp [schurPower, map_prod]

theorem permanent_map {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (A : Matrix (Fin n) (Fin n) R) : (A.map f).permanent = f A.permanent := by
  simp [Matrix.permanent, map_sum, map_prod]

/-- A real symmetric matrix is positive semidefinite over `ℝ` iff its complex image is over `ℂ`. -/
theorem posSemidef_map_ofReal_iff {m : Type*} [Fintype m] (M : Matrix m m ℝ) :
    (M.map ((↑) : ℝ → ℂ)).PosSemidef ↔ M.PosSemidef := by
  classical
  constructor
  · intro h
    have hH : M.IsHermitian := by
      ext i j
      have := congrFun (congrFun h.1.eq i) j
      simpa [conjTranspose_apply] using this
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun x => ?_
    have := h.dotProduct_mulVec_nonneg (fun i => (x i : ℂ))
    have e : star (fun i => (x i : ℂ)) ⬝ᵥ (M.map ((↑) : ℝ → ℂ) *ᵥ fun i => (x i : ℂ)) =
        ((star x ⬝ᵥ (M *ᵥ x) : ℝ) : ℂ) := by
      simp [dotProduct, mulVec]
    rw [e] at this
    exact_mod_cast this
  · intro h
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h.nonneg
    have : M.map ((↑) : ℝ → ℂ) = (B.map ((↑) : ℝ → ℂ))ᴴ * B.map ((↑) : ℝ → ℂ) := by
      rw [hB, star_eq_conjTranspose]
      ext i j
      simp [conjTranspose_apply, mul_apply]
    rw [this]
    exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Transport of the Loewner statement from a real matrix to its complex image. -/
theorem pot_map_ofReal_iff (A : Matrix (Fin n) (Fin n) ℝ) (κ : ℝ) :
    (((κ : ℂ) * (A.map ((↑) : ℝ → ℂ)).permanent) • (1 : Matrix (Perm (Fin n)) (Perm (Fin n)) ℂ) -
        schurPower (A.map ((↑) : ℝ → ℂ))).PosSemidef ↔
      (((κ * A.permanent) • (1 : Matrix (Perm (Fin n)) (Perm (Fin n)) ℝ)) - schurPower A).PosSemidef := by
  rw [← posSemidef_map_ofReal_iff]
  have h1 : schurPower (A.map ((↑) : ℝ → ℂ)) = (schurPower A).map ((↑) : ℝ → ℂ) :=
    schurPower_map Complex.ofRealHom A
  have h2 : (A.map ((↑) : ℝ → ℂ)).permanent = (A.permanent : ℂ) :=
    permanent_map Complex.ofRealHom A
  have e : ((κ : ℂ) * (A.permanent : ℂ)) • (1 : Matrix (Perm (Fin n)) (Perm (Fin n)) ℂ) -
      (schurPower A).map ((↑) : ℝ → ℂ) =
      (((κ * A.permanent) • (1 : Matrix (Perm (Fin n)) (Perm (Fin n)) ℝ)) -
        schurPower A).map ((↑) : ℝ → ℂ) := by
    ext σ τ
    by_cases h : σ = τ <;> simp [h]
  rw [h1, h2, e]

end RealToComplex

end Results.SoulesPotOrderFour
