import Results.SoulesPotOrderFour.Defs
import Mathlib.Analysis.Matrix.Order

/-!
# Diagonal decrement, low-order facts and `extendOne`

* `defect κ A = (κ per A) I - Π(A)` and the position bijection `posEquiv i`.
* `defect_eq_sub_single` (the matrix identity of Lemma 2.1) and `decrement_posSemidef`.
* `exists_decrement` (existence of `t`, rank drop), `pot_two` (order two),
  `extendOne` (direct sum with `[1]`) and `pot_of_extendOne`, `pot_three_extendOne`.
-/

open Matrix Equiv
open scoped ComplexOrder Kronecker

namespace Results.SoulesPotOrderFour

section Decrement

/-- The defect operator `D_κ(A) = κ per(A) I - Π(A)`. -/
noncomputable def defect {m : ℕ} (κ : ℂ) (A : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Perm (Fin m)) (Perm (Fin m)) ℂ :=
  (κ * A.permanent) • (1 : Matrix (Perm (Fin m)) (Perm (Fin m)) ℂ) - schurPower A

variable {n : ℕ}

/-- Extension of `ρ ∈ S_n` to a permutation of `Fin (n+1)` sending position `j` to the value `i`
and acting as `ρ` on the remaining positions (through `succAbove`). -/
def extPerm (i j : Fin (n + 1)) (ρ : Perm (Fin n)) : Perm (Fin (n + 1)) :=
  (finSuccEquiv' j).trans ((Equiv.optionCongr ρ).trans (finSuccEquiv' i).symm)

@[simp] theorem extPerm_at (i j : Fin (n + 1)) (ρ : Perm (Fin n)) : extPerm i j ρ j = i := by
  simp [extPerm]

@[simp] theorem extPerm_succAbove (i j : Fin (n + 1)) (ρ : Perm (Fin n)) (k : Fin n) :
    extPerm i j ρ (j.succAbove k) = i.succAbove (ρ k) := by
  simp [extPerm]

theorem extPerm_injective (i : Fin (n + 1)) :
    Function.Injective fun p : Fin (n + 1) × Perm (Fin n) => extPerm i p.1 p.2 := by
  rintro ⟨j, ρ⟩ ⟨j', ρ'⟩ h
  have h1 : ∀ x : Fin (n + 1), extPerm i j ρ x = extPerm i j' ρ' x := fun x => by
    simpa using congrArg (fun f : Perm (Fin (n + 1)) => f x) h
  have hj : j = j' := by
    have := h1 j
    rw [extPerm_at] at this
    by_contra hne
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hne
    rw [extPerm_succAbove] at this
    exact Fin.succAbove_ne i _ this.symm
  subst hj
  refine Prod.ext rfl (Equiv.ext fun k => ?_)
  have := h1 (j.succAbove k)
  rw [extPerm_succAbove, extPerm_succAbove] at this
  exact i.succAbove_right_injective this

/-- Position bijection: a permutation of `Fin (n+1)` is determined by the position `j` of the
value `i` and the induced permutation of the remaining `n` positions. -/
noncomputable def posEquiv (i : Fin (n + 1)) : Fin (n + 1) × Perm (Fin n) ≃ Perm (Fin (n + 1)) :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).2
    ⟨extPerm_injective i, by simp [Fintype.card_perm, Nat.factorial_succ]⟩)

theorem posEquiv_apply (i : Fin (n + 1)) (j : Fin (n + 1)) (ρ : Perm (Fin n)) :
    posEquiv i (j, ρ) = extPerm i j ρ := rfl

theorem extPerm_eq_iff {i j j' : Fin (n + 1)} {ρ : Perm (Fin n)} {ρ' : Perm (Fin n)} :
    extPerm i j ρ = extPerm i j' ρ' ↔ j = j' ∧ ρ = ρ' := by
  have := (posEquiv i).injective.eq_iff (a := (j, ρ)) (b := (j', ρ'))
  simpa [posEquiv_apply, Prod.ext_iff] using this

/-- `A` with the `(i,i)` entry decreased by `t`. -/
abbrev decr (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)) (t : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  A - (t : ℂ) • Matrix.single i i (1 : ℂ)

theorem decr_apply (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)) (t : ℝ)
    (a b : Fin (n + 1)) :
    decr A i t a b = A a b - if a = i ∧ b = i then (t : ℂ) else 0 := by
  simp only [decr, Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  by_cases h : a = i ∧ b = i
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · have h' : ¬(i = a ∧ i = b) := fun h2 => h ⟨h2.1.symm, h2.2.symm⟩
    simp [h, h']

/-- Entry of `Π(A) - Π(A - tE_ii)` in the position coordinates. -/
theorem schurPower_sub_decr (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)) (t : ℝ)
    (j j' : Fin (n + 1)) (ρ ρ' : Perm (Fin n)) :
    schurPower A (extPerm i j ρ) (extPerm i j' ρ') - schurPower (decr A i t) (extPerm i j ρ)
        (extPerm i j' ρ') =
      (t : ℂ) * if j = j' then schurPower (A.submatrix i.succAbove i.succAbove) ρ ρ' else 0 := by
  simp only [schurPower, of_apply]
  rw [Fin.prod_univ_succAbove _ j, Fin.prod_univ_succAbove _ j]
  have hB : ∀ k : Fin n, decr A i t (extPerm i j ρ (j.succAbove k)) (extPerm i j' ρ' (j.succAbove k))
      = A (i.succAbove (ρ k)) (extPerm i j' ρ' (j.succAbove k)) := fun k => by
    rw [decr_apply, extPerm_succAbove, if_neg (fun h => Fin.succAbove_ne i _ h.1), sub_zero]
  simp only [hB, extPerm_at, decr_apply, true_and]
  by_cases hj : j = j'
  · subst hj
    simp [extPerm_succAbove, Matrix.submatrix_apply, sub_mul]
  · have hne : extPerm i j' ρ' j ≠ i := fun h =>
      hj ((extPerm i j' ρ').injective (h.trans (extPerm_at i j' ρ').symm))
    simp [hj, hne]

theorem permanent_eq_sum_schurPower_one {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    A.permanent = ∑ τ : Perm (Fin m), schurPower A 1 τ := by
  rw [← Matrix.permanent_transpose, Matrix.permanent]
  simp [schurPower]

theorem extPerm_one (i : Fin (n + 1)) : extPerm i i (1 : Perm (Fin n)) = 1 := by
  ext x; simp [extPerm]

/-- `per A = per (A - tE_ii) + t per A(i,i)`. -/
theorem permanent_eq_decr (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)) (t : ℝ) :
    A.permanent = (decr A i t).permanent +
      (t : ℂ) * (A.submatrix i.succAbove i.succAbove).permanent := by
  have key : A.permanent - (decr A i t).permanent =
      (t : ℂ) * (A.submatrix i.succAbove i.succAbove).permanent := by
    rw [permanent_eq_sum_schurPower_one A, permanent_eq_sum_schurPower_one (decr A i t),
      ← Finset.sum_sub_distrib, ← (posEquiv i).sum_comp, Fintype.sum_prod_type,
      permanent_eq_sum_schurPower_one (A.submatrix i.succAbove i.succAbove), Finset.mul_sum]
    have h1 : (1 : Perm (Fin (n + 1))) = extPerm i i 1 := (extPerm_one i).symm
    simp only [posEquiv_apply]
    rw [Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [h1, schurPower_sub_decr]
      simp
    · intro j _ hj
      refine Finset.sum_eq_zero fun ρ _ => ?_
      rw [h1, schurPower_sub_decr]
      simp [Ne.symm hj]
    · simp
  rw [← key]; ring

variable (κ : ℂ)

/-- The operator induced on `ℂ^{S_{n+1}}` by the direct sum over the positions `j` of `i` of the
defect operator of the principal submatrix `A(i,i)`. -/
noncomputable def indOp (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)) :
    Matrix (Perm (Fin (n + 1))) (Perm (Fin (n + 1))) ℂ :=
  ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) ⊗ₖ defect κ (A.submatrix i.succAbove i.succAbove)).submatrix
    (posEquiv i).symm (posEquiv i).symm

theorem indOp_apply (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i j j' : Fin (n + 1))
    (ρ ρ' : Perm (Fin n)) :
    indOp κ A i (extPerm i j ρ) (extPerm i j' ρ') =
      if j = j' then defect κ (A.submatrix i.succAbove i.succAbove) ρ ρ' else 0 := by
  have h1 := (posEquiv i).symm_apply_apply (j, ρ)
  have h2 := (posEquiv i).symm_apply_apply (j', ρ')
  simp only [indOp, submatrix_apply, posEquiv_apply] at h1 h2 ⊢
  rw [h1, h2]
  by_cases h : j = j' <;> simp [h, Matrix.kroneckerMap_apply]

/-- `indOp` acts blockwise: on the block of position `j` it is `defect κ A(i,i)`, applied to the
restriction `ρ ↦ x (extPerm i j ρ)` of the vector. -/
theorem indOp_mulVec (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i j : Fin (n + 1))
    (x : Perm (Fin (n + 1)) → ℂ) (ρ : Perm (Fin n)) :
    (indOp κ A i *ᵥ x) (extPerm i j ρ) =
      (defect κ (A.submatrix i.succAbove i.succAbove) *ᵥ fun ρ' => x (extPerm i j ρ')) ρ := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← (posEquiv i).sum_comp, Fintype.sum_prod_type]
  simp [posEquiv_apply, indOp_apply, ite_mul]

theorem indOp_posSemidef (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1))
    (h : (defect κ (A.submatrix i.succAbove i.succAbove)).PosSemidef) :
    (indOp κ A i).PosSemidef :=
  (Matrix.PosSemidef.kronecker Matrix.PosSemidef.one h).submatrix _

/-- **Matrix identity of Lemma 2.1** (no positivity hypothesis):
`D_κ(A) = D_κ(A - tE_ii) + t · ⊕_j D_κ(A(i,i))`. -/
theorem defect_eq_decr (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)) (t : ℝ) :
    defect κ A = defect κ (decr A i t) + (t : ℂ) • indOp κ A i := by
  ext σ τ
  obtain ⟨⟨j, ρ⟩, rfl⟩ := (posEquiv i).surjective σ
  obtain ⟨⟨j', ρ'⟩, rfl⟩ := (posEquiv i).surjective τ
  simp only [posEquiv_apply]
  have hs := schurPower_sub_decr A i t j j' ρ ρ'
  have hp := permanent_eq_decr A i t
  have hd : (1 : Matrix (Perm (Fin (n + 1))) (Perm (Fin (n + 1))) ℂ) (extPerm i j ρ) (extPerm i j' ρ')
      = if j = j' then (1 : Matrix (Perm (Fin n)) (Perm (Fin n)) ℂ) ρ ρ' else 0 := by
    simp only [Matrix.one_apply, extPerm_eq_iff]
    by_cases h : j = j' <;> simp [h]
  simp only [defect, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, indOp_apply, smul_eq_mul]
  by_cases h : j = j'
  · simp only [h, if_true] at hd hs ⊢
    rw [hd]
    linear_combination (-1 : ℂ) * hs + (κ * (1 : Matrix (Perm (Fin n)) (Perm (Fin n)) ℂ) ρ ρ') * hp
  · simp only [h, if_false] at hd hs ⊢
    rw [hd]
    linear_combination (-1 : ℂ) * hs

/-- **Lemma 2.1 (diagonal decrement)**. -/
theorem decrement_posSemidef (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1))
    (t κ : ℝ) (ht : 0 ≤ t)
    (hB : (((κ : ℂ) * (decr A i t).permanent) •
      (1 : Matrix (Perm (Fin (n + 1))) (Perm (Fin (n + 1))) ℂ) - schurPower (decr A i t)).PosSemidef)
    (hA' : (((κ : ℂ) * (A.submatrix i.succAbove i.succAbove).permanent) •
      (1 : Matrix (Perm (Fin n)) (Perm (Fin n)) ℂ) -
        schurPower (A.submatrix i.succAbove i.succAbove)).PosSemidef) :
    (((κ : ℂ) * A.permanent) • (1 : Matrix (Perm (Fin (n + 1))) (Perm (Fin (n + 1))) ℂ) -
      schurPower A).PosSemidef := by
  have h := defect_eq_decr (κ : ℂ) A i t
  have h2 := (indOp_posSemidef (κ : ℂ) A i hA').smul (a := (t : ℂ)) (by exact_mod_cast ht)
  show (defect (κ : ℂ) A).PosSemidef
  rw [h]
  exact hB.add h2

end Decrement

section Exists

variable {n : ℕ}

theorem decr_apply_of_ne (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)) (t : ℝ)
    {a b : Fin (n + 1)} (h : a ≠ b) : decr A i t a b = A a b := by
  rw [decr_apply, if_neg (fun h' => h (h'.1.trans h'.2.symm)), sub_zero]

/-- **Lemma 2.1, last assertion.** For positive definite `A` and `t = 1 / (A⁻¹)_{ii}`,
`A - tE_ii` is positive semidefinite of rank at most `n`. -/
theorem exists_decrement (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.PosDef)
    (i : Fin (n + 1)) :
    ∃ t : ℝ, 0 < t ∧ (decr A i t).PosSemidef ∧ (decr A i t).rank ≤ n := by
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA.isUnit
  have hAS : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet
  have hSA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hdet
  have hS : (A⁻¹).PosDef := hA.inv
  have hSi := hS.diag_pos (i := i)
  obtain ⟨hs0, hs1⟩ := Complex.pos_iff.1 hSi
  set s : ℝ := (A⁻¹ i i).re with hs
  have hSii : A⁻¹ i i = (s : ℂ) := Complex.ext (by simp [hs]) (by simpa using hs1.symm)
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  refine ⟨1 / s, by positivity, ?_⟩
  set e : Fin (n + 1) → ℂ := Pi.single i 1 with he
  set v : Fin (n + 1) → ℂ := A⁻¹ *ᵥ e with hv
  have hAv : A *ᵥ v = e := by
    rw [hv, Matrix.mulVec_mulVec, hAS, Matrix.one_mulVec]
  have hvi : v i = (s : ℂ) := by
    rw [hv, he, Matrix.mulVec_single_one]; simpa using hSii
  have hvA : ∀ x : Fin (n + 1) → ℂ, star v ⬝ᵥ (A *ᵥ x) = x i := fun x => by
    rw [hv, Matrix.star_mulVec, hS.1.eq, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hSA,
      Matrix.vecMul_one, he]
    simp
  have hq : ∀ x : Fin (n + 1) → ℂ, star x ⬝ᵥ (decr A i (1 / s) *ᵥ x) =
      star x ⬝ᵥ (A *ᵥ x) - ((1 / s : ℝ) : ℂ) * (star (x i) * x i) := fun x => by
    simp only [decr, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
      Matrix.single_mulVec_eq, dotProduct_single_one]
    simp only [smul_eq_mul, one_mul, Pi.star_apply, Complex.ofReal_div, Complex.ofReal_one]
    ring
  have hpsd : (decr A i (1 / s)).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · ext a b
      rw [Matrix.conjTranspose_apply, decr_apply, decr_apply, star_sub, hA.1.apply]
      have : (star (if b = i ∧ a = i then (((1 / s : ℝ)) : ℂ) else 0)) =
          if a = i ∧ b = i then (((1 / s : ℝ)) : ℂ) else 0 := by
        by_cases h : a = i ∧ b = i
        · obtain ⟨rfl, rfl⟩ := h; simp
        · have h' : ¬(b = i ∧ a = i) := fun h2 => h ⟨h2.2, h2.1⟩
          simp [h, h']
      rw [this]
    · rw [hq]
      have h0 := hA.posSemidef.dotProduct_mulVec_nonneg (x - (x i / (s : ℂ)) • v)
      have : star (x - (x i / (s : ℂ)) • v) ⬝ᵥ (A *ᵥ (x - (x i / (s : ℂ)) • v)) =
          star x ⬝ᵥ (A *ᵥ x) - ((1 / s : ℝ) : ℂ) * (star (x i) * x i) := by
        simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, star_sub, star_smul, sub_dotProduct,
          dotProduct_sub, smul_dotProduct, dotProduct_smul, hAv, hvA, smul_eq_mul]
        have h1 : star x ⬝ᵥ e = star (x i) := by rw [he, dotProduct_single_one]; rfl
        have h2 : star v ⬝ᵥ e = (s : ℂ) := by
          rw [he, dotProduct_single_one]; simp [Pi.star_apply, hvi]
        rw [h1, h2, star_div₀, Complex.star_def, Complex.conj_ofReal]
        push_cast
        field_simp
        ring
      rwa [this] at h0
  refine ⟨hpsd, ?_⟩
  have hker : decr A i (1 / s) *ᵥ v = 0 := by
    simp only [decr, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.single_mulVec_eq, hAv, he,
      hvi, one_mul]
    ext a
    by_cases h : a = i
    · subst h; simp; field_simp; ring
    · simp [h]
  have h1 := LinearMap.finrank_range_add_finrank_ker (decr A i (1 / s)).mulVecLin
  have h2 : 0 < Module.finrank ℂ (LinearMap.ker (decr A i (1 / s)).mulVecLin) := by
    refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, LinearMap.mem_ker.2 (by rw [Matrix.mulVecLin_apply]; exact hker)⟩, ?_⟩
    intro h0
    have : v i = 0 := congrFun (congrArg Subtype.val h0) i
    rw [hvi] at this
    exact hsC (by exact_mod_cast this)
  rw [Module.finrank_pi, Fintype.card_fin] at h1
  unfold Matrix.rank
  omega

end Exists

section Reindex

variable {m : ℕ}

theorem defect_def (κ : ℂ) (A : Matrix (Fin m) (Fin m) ℂ) :
    defect κ A = (κ * A.permanent) • (1 : Matrix (Perm (Fin m)) (Perm (Fin m)) ℂ) - schurPower A :=
  rfl

theorem defect_one (A : Matrix (Fin m) (Fin m) ℂ) :
    defect 1 A = A.permanent • (1 : Matrix (Perm (Fin m)) (Perm (Fin m)) ℂ) - schurPower A := by
  rw [defect_def, one_mul]

theorem permanent_submatrix_perm (A : Matrix (Fin m) (Fin m) ℂ) (π : Perm (Fin m)) :
    (A.submatrix π π).permanent = A.permanent := by
  have : A.submatrix π π = (A.submatrix π id).submatrix id π := by ext; simp
  rw [this, Matrix.permanent_permute_rows, Matrix.permanent_permute_cols]

theorem schurPower_submatrix_perm (A : Matrix (Fin m) (Fin m) ℂ) (π : Perm (Fin m)) :
    schurPower (A.submatrix π π) =
      (schurPower A).submatrix (Equiv.mulLeft π) (Equiv.mulLeft π) := by
  ext σ τ
  simp [schurPower]

theorem defect_submatrix_perm (κ : ℂ) (A : Matrix (Fin m) (Fin m) ℂ) (π : Perm (Fin m)) :
    defect κ (A.submatrix π π) =
      (defect κ A).submatrix (Equiv.mulLeft π) (Equiv.mulLeft π) := by
  rw [defect, defect, permanent_submatrix_perm, schurPower_submatrix_perm]
  ext σ τ
  simp [Matrix.one_apply]

/-- Reindexing invariance: relabeling the indices of `A` by `π` does not affect the Loewner
inequality `Π(A) ⪯ κ per(A) I` (here with the defect operator `D_κ`). -/
theorem pot_submatrix_equiv (κ : ℂ) (A : Matrix (Fin m) (Fin m) ℂ) (π : Perm (Fin m)) :
    (defect κ (A.submatrix π π)).PosSemidef ↔ (defect κ A).PosSemidef := by
  rw [defect_submatrix_perm]
  exact Matrix.posSemidef_submatrix_equiv (Equiv.mulLeft π)

/-- Raising the factor `κ` preserves the Loewner inequality when `per A ≥ 0`. -/
theorem defect_mono (A : Matrix (Fin m) (Fin m) ℂ) {κ κ' : ℝ} (hκ : κ ≤ κ')
    (hp : 0 ≤ A.permanent) (h : (defect (κ : ℂ) A).PosSemidef) :
    (defect (κ' : ℂ) A).PosSemidef := by
  have h2 : defect (κ' : ℂ) A = defect (κ : ℂ) A +
      (((κ' - κ : ℝ) : ℂ) * A.permanent) • (1 : Matrix (Perm (Fin m)) (Perm (Fin m)) ℂ) := by
    simp only [defect]; push_cast; module
  rw [h2]
  refine h.add (Matrix.PosSemidef.one.smul ?_)
  exact mul_nonneg (by exact_mod_cast sub_nonneg.2 hκ) hp

end Reindex

section OrderTwo

theorem perm_fin_two (σ : Perm (Fin 2)) : σ = 1 ∨ σ = swap 0 1 := by revert σ; decide

theorem permanent_fin_two (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A.permanent = A 0 0 * A 1 1 + A 1 0 * A 0 1 := by
  have hu : (Finset.univ : Finset (Perm (Fin 2))) = {1, swap 0 1} := by
    ext σ; simp [perm_fin_two σ]
  rw [Matrix.permanent, hu, Finset.sum_pair (by decide)]
  simp [Fin.prod_univ_two]

/-- **Order two**: `Π(A) ⪯ per(A) I` for every Hermitian `A` of order two. -/
theorem pot_two (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian) :
    (A.permanent • (1 : Matrix (Perm (Fin 2)) (Perm (Fin 2)) ℂ) - schurPower A).PosSemidef := by
  set sg : Perm (Fin 2) → ℂ := fun σ => if σ = 1 then 1 else -1 with hsg
  have h1 : (1 : Perm (Fin 2)) ≠ swap 0 1 := by decide
  have h2 : swap 0 1 ≠ (1 : Perm (Fin 2)) := by decide
  have hb : A 1 0 = star (A 0 1) := (hA.apply 1 0).symm
  have key : A.permanent • (1 : Matrix (Perm (Fin 2)) (Perm (Fin 2)) ℂ) - schurPower A =
      (A 0 1 * A 1 0) • Matrix.vecMulVec sg (star sg) := by
    ext σ τ
    rw [permanent_fin_two]
    rcases perm_fin_two σ with rfl | rfl <;> rcases perm_fin_two τ with rfl | rfl <;>
      simp [schurPower, Matrix.vecMulVec_apply, hsg, Fin.prod_univ_two,
        h1, h2] <;> ring
  rw [key]
  refine (Matrix.posSemidef_vecMulVec_self_star sg).smul ?_
  rw [hb, Complex.star_def, Complex.mul_conj]
  exact Complex.zero_le_real.2 (Complex.normSq_nonneg _)

end OrderTwo

section ExtendOne

variable {m : ℕ}

/-- The direct sum `C ⊕ [1]` as a matrix of order `m + 1` (the new index is `Fin.last m`). -/
def extendOne (C : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Matrix.of fun a b => Fin.lastCases (Fin.lastCases (1 : ℂ) (fun _ => 0) b)
    (fun a' => Fin.lastCases 0 (fun b' => C a' b') b) a

@[simp] theorem extendOne_cc (C : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m) :
    extendOne C a.castSucc b.castSucc = C a b := by simp [extendOne]

@[simp] theorem extendOne_last_last (C : Matrix (Fin m) (Fin m) ℂ) :
    extendOne C (Fin.last m) (Fin.last m) = 1 := by simp [extendOne]

@[simp] theorem extendOne_last_c (C : Matrix (Fin m) (Fin m) ℂ) (b : Fin m) :
    extendOne C (Fin.last m) b.castSucc = 0 := by simp [extendOne]

@[simp] theorem extendOne_c_last (C : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) :
    extendOne C a.castSucc (Fin.last m) = 0 := by simp [extendOne]

theorem submatrix_extendOne (C : Matrix (Fin m) (Fin m) ℂ) :
    (extendOne C).submatrix (Fin.last m).succAbove (Fin.last m).succAbove = C := by
  ext a b; simp [Fin.succAbove_last]

/-- Decrementing the new index of `C ⊕ [1]` by `1` produces a matrix with vanishing last
row and column. -/
theorem decr_extendOne_row (C : Matrix (Fin m) (Fin m) ℂ) (b : Fin (m + 1)) :
    decr (extendOne C) (Fin.last m) 1 (Fin.last m) b = 0 := by
  rw [decr_apply]
  by_cases h : b = Fin.last m
  · subst h; simp
  · obtain ⟨b', rfl⟩ := Fin.exists_castSucc_eq.2 h
    simp [h]

theorem decr_extendOne_col (C : Matrix (Fin m) (Fin m) ℂ) (a : Fin (m + 1)) :
    decr (extendOne C) (Fin.last m) 1 a (Fin.last m) = 0 := by
  rw [decr_apply]
  by_cases h : a = Fin.last m
  · subst h; simp
  · obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.2 h
    simp [h]

theorem permanent_decr_extendOne (C : Matrix (Fin m) (Fin m) ℂ) :
    (decr (extendOne C) (Fin.last m) 1).permanent = 0 := by
  refine Finset.sum_eq_zero fun σ _ => Finset.prod_eq_zero (Finset.mem_univ (σ.symm (Fin.last m))) ?_
  simpa using decr_extendOne_row C (σ.symm (Fin.last m))

theorem schurPower_decr_extendOne (C : Matrix (Fin m) (Fin m) ℂ) :
    schurPower (decr (extendOne C) (Fin.last m) 1) = 0 := by
  ext σ τ
  refine Finset.prod_eq_zero (Finset.mem_univ (σ.symm (Fin.last m))) ?_
  simpa using decr_extendOne_row C (τ (σ.symm (Fin.last m)))

theorem permanent_extendOne (C : Matrix (Fin m) (Fin m) ℂ) :
    (extendOne C).permanent = C.permanent := by
  have := permanent_eq_decr (extendOne C) (Fin.last m) 1
  rw [permanent_decr_extendOne, submatrix_extendOne] at this
  simpa using this

theorem schurPower_extendOne (C : Matrix (Fin m) (Fin m) ℂ) (ρ ρ' : Perm (Fin m)) :
    schurPower (extendOne C) (extPerm (Fin.last m) (Fin.last m) ρ)
      (extPerm (Fin.last m) (Fin.last m) ρ') = schurPower C ρ ρ' := by
  have := schurPower_sub_decr (extendOne C) (Fin.last m) 1 (Fin.last m) (Fin.last m) ρ ρ'
  rw [schurPower_decr_extendOne, submatrix_extendOne] at this
  simpa using this

/-- If `C ⊕ [1]` satisfies the Loewner inequality with factor `κ`, so does `C`. -/
theorem pot_of_extendOne (κ : ℂ) (C : Matrix (Fin m) (Fin m) ℂ)
    (h : (defect κ (extendOne C)).PosSemidef) : (defect κ C).PosSemidef := by
  have : defect κ C = (defect κ (extendOne C)).submatrix
      (fun ρ => extPerm (Fin.last m) (Fin.last m) ρ) (fun ρ => extPerm (Fin.last m) (Fin.last m) ρ) := by
    ext ρ ρ'
    simp only [defect, permanent_extendOne, Matrix.sub_apply, Matrix.smul_apply, submatrix_apply,
      schurPower_extendOne, Matrix.one_apply, extPerm_eq_iff, true_and]
  rw [this]
  exact h.submatrix _

/-- **Order three, `C ⊕ [1]` case**: for `C` Hermitian of order two, `C ⊕ [1]` satisfies
`Π ⪯ per I` (decrement at the new index plus order two). -/
theorem pot_three_extendOne (C : Matrix (Fin 2) (Fin 2) ℂ) (hC : C.IsHermitian) :
    ((extendOne C).permanent • (1 : Matrix (Perm (Fin 3)) (Perm (Fin 3)) ℂ) -
      schurPower (extendOne C)).PosSemidef := by
  have h := decrement_posSemidef (extendOne C) (Fin.last 2) 1 1 zero_le_one
  rw [permanent_decr_extendOne, schurPower_decr_extendOne, submatrix_extendOne] at h
  simpa using h (by simpa using Matrix.PosSemidef.zero) (by simpa using pot_two C hC)

end ExtendOne

end Results.SoulesPotOrderFour
