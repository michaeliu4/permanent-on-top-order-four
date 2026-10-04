import Results.SoulesPotOrderFour.Solution.Basic
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Sector reduction for the Schur power `Π(A)` of order four

`Π(A)_{σ,τ} = φ(τσ⁻¹)` is the group matrix of `φ(g) = ∏ᵢ a_{i,g(i)}` on `S₄`.  Everything is
reduced to the finite character identity
`24·δ_h = (1+sgn h)(1 + 3(fix h − 1)) + 2(fixP h − 1)` (`Sector.char_id`, checked in the kernel).

Public results (all over `ℂ`/commutative rings as indicated):
* Laplace/fiber identities `F_ab = ∑_{g a = b} φ g`, `G_ab = ∑_{g a = b} sgn g · φ g`,
  `(Hᵀ)_{ab} = ∑_{pact g a = b} φ g` (`cofactorPermMatrix_fiber`, `signCofactorMatrix_fiber`,
  `pairingMatrix_transpose_fiber`) and `(Π c)_σ = ∑_g φ g · c(gσ)` (`schurPower_mulVec_apply`).
* Lifts: `Π *ᵥ liftF y = liftF (F *ᵥ y)`, `Π *ᵥ liftG y = liftG (G *ᵥ y)`,
  `Π *ᵥ liftH z = liftH (Hᵀ *ᵥ z)` (note the transpose for the pair block).
* Gram identities (`6`, `6`, `8`) and the quadratic-form consequences `liftF_form`, ...
* `schurPower_defect_posSemidef`: `K₃₁, K₂₁₁, K₂₂ ⪰ 0`, `per A, det A ≤ λ` imply `λ I − Π(A) ⪰ 0`.
-/

open Matrix Equiv Finset
open scoped ComplexOrder

namespace Results.SoulesPotOrderFour

section Algebra

variable {R : Type*} [CommRing R]

/-- `Σ_{g(i)=j} ∏_k a_{k,g(k)} = a_ij per A(i,j)` (Laplace expansion of the permanent, fiberwise). -/
theorem sum_fiber_perm {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i j : Fin (n + 1)) :
    ∑ g : Perm (Fin (n + 1)), (if g i = j then ∏ k, A k (g k) else 0) =
      A i j * (A.submatrix i.succAbove j.succAbove).permanent := by
  let Θ : Perm (Fin (n + 1)) ≃ Perm (Option (Fin n)) :=
    Equiv.equivCongr (finSuccEquiv' i) (finSuccEquiv' j)
  have hΘ : ∀ (g : Perm (Option (Fin n))) (k : Fin (n + 1)),
      Θ.symm g k = (finSuccEquiv' j).symm (g (finSuccEquiv' i k)) := fun g k => rfl
  rw [← Θ.symm.sum_comp, ← Perm.decomposeOption.symm.sum_comp, Fintype.sum_prod_type,
    Fintype.sum_option]
  simp only [hΘ]
  have h2 : ∀ (x : Fin n) (e : Perm (Fin n)),
      (finSuccEquiv' j).symm ((Perm.decomposeOption.symm (some x, e)) ((finSuccEquiv' i) i)) ≠ j := by
    intro x e
    simp [Perm.decomposeOption_symm_apply]
  rw [Finset.sum_eq_zero (s := (univ : Finset (Fin n)))
    (fun x _ => Finset.sum_eq_zero fun e _ => if_neg (h2 x e)), add_zero]
  rw [← permanent_transpose, permanent, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  have h1 : (finSuccEquiv' j).symm ((Perm.decomposeOption.symm (none, e)) ((finSuccEquiv' i) i)) = j := by
    simp [Perm.decomposeOption_symm_apply]
  rw [if_pos h1, Fin.prod_univ_succAbove _ i, h1]
  congr 1
  refine Finset.prod_congr rfl fun x _ => ?_
  simp [Perm.decomposeOption_symm_apply]

/-- Signed version: `Σ_{g(i)=j} sgn g ∏_k a_{k,g(k)} = a_ij (-1)^(i+j) det A(i,j)`. -/
theorem sum_fiber_sign {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i j : Fin (n + 1)) :
    ∑ g : Perm (Fin (n + 1)),
        (if g i = j then (((Perm.sign g : ℤˣ) : ℤ) : R) * ∏ k, A k (g k) else 0) =
      A i j * ((-1) ^ (i.val + j.val) * (A.submatrix i.succAbove j.succAbove).det) := by
  have h1 : A.adjugate j i = (A.updateRow i (Pi.single j 1)).det := adjugate_apply A j i
  rw [adjugate_fin_succ_eq_det_submatrix] at h1
  rw [h1, det_apply', Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun g => ?_
  have hp : ∏ k, (A.updateRow i (Pi.single j 1)) (g⁻¹ k) k =
      ∏ m, (A.updateRow i (Pi.single j 1)) m (g m) := by
    rw [← Equiv.prod_comp g (fun k => (A.updateRow i (Pi.single j 1)) (g⁻¹ k) k)]
    simp
  simp only [Equiv.inv_apply, hp, Perm.sign_inv]
  have hne : ∀ m ∈ univ.erase i, (A.updateRow i (Pi.single j 1)) m (g m) = A m (g m) :=
    fun m hm => by rw [updateRow_ne (Finset.ne_of_mem_erase hm)]
  have hs : ∏ m, (A.updateRow i (Pi.single j 1)) m (g m) =
      (if g i = j then ∏ m ∈ univ.erase i, A m (g m) else 0) := by
    rw [← Finset.mul_prod_erase univ _ (mem_univ i), Finset.prod_congr rfl hne, updateRow_self]
    by_cases h : g i = j <;> simp [h]
  rw [hs, ← Finset.mul_prod_erase univ (fun k => A k (g k)) (mem_univ i)]
  by_cases h : g i = j
  · subst h; simp [mul_left_comm]
  · simp [h]

/-- `Σ_g φ(g) = per A`. -/
theorem sum_phi_eq_permanent (A : Matrix (Fin 4) (Fin 4) R) :
    ∑ g : Perm (Fin 4), phi A g = A.permanent := by
  rw [permanent]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun g => ?_
  simp only [phi, Equiv.inv_apply]
  rw [← Equiv.prod_comp g (fun k => A (g⁻¹ k) k)]
  simp

/-- `Σ_g sgn(g) φ(g) = det A`. -/
theorem sum_sign_phi_eq_det (A : Matrix (Fin 4) (Fin 4) R) :
    ∑ g : Perm (Fin 4), (((Perm.sign g : ℤˣ) : ℤ) : R) * phi A g = A.det := by
  rw [det_apply']
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun g => ?_
  simp only [phi, Equiv.inv_apply, Perm.sign_inv]
  rw [← Equiv.prod_comp g (fun k => A (g⁻¹ k) k)]
  simp


/-- The sign of a permutation as an integer. -/
abbrev permSgn (g : Perm (Fin 4)) : ℤ := ((Perm.sign g : ℤˣ) : ℤ)

theorem permSgn_one : permSgn 1 = 1 := by simp [permSgn]
theorem permSgn_mul (g h : Perm (Fin 4)) : permSgn (g * h) = permSgn g * permSgn h := by simp [permSgn]
theorem permSgn_mul_self (g : Perm (Fin 4)) : permSgn g * permSgn g = 1 := by
  simp only [permSgn, ← Units.val_mul, Int.units_mul_self, Units.val_one]

/-- Action of `S₄` on the three pair partitions `P_0, P_1, P_2` of `Basic.pairRel`:
`pact g j` is the index `i` with `g(P_j) = P_i`. -/
def pact (g : Perm (Fin 4)) (j : Fin 3) : Fin 3 :=
  if ∀ x y, pairRel j x y = pairRel 0 (g x) (g y) then 0
  else if ∀ x y, pairRel j x y = pairRel 1 (g x) (g y) then 1 else 2

theorem pact_spec : ∀ (g : Perm (Fin 4)) (j i : Fin 3),
    (∀ x y, pairRel j x y = pairRel i (g x) (g y)) ↔ pact g j = i := by decide +kernel

theorem pact_mul (g h : Perm (Fin 4)) (j : Fin 3) : pact (g * h) j = pact g (pact h j) := by
  rw [← pact_spec]
  intro x y
  rw [Perm.mul_apply, Perm.mul_apply, (pact_spec h j _).2 rfl x y, (pact_spec g _ _).2 rfl]

theorem pact_one (j : Fin 3) : pact 1 j = j := by
  rw [← pact_spec]; intro x y; rfl

theorem card_pact (k : Fin 3) : (univ.filter fun σ : Perm (Fin 4) => pact σ 0 = k).card = 8 := by
  revert k; decide +kernel

theorem card_fix (a : Fin 4) : (univ.filter fun σ : Perm (Fin 4) => σ 0 = a).card = 6 := by
  revert a; decide +kernel

theorem card_pact_pre (g : Perm (Fin 4)) (a : Fin 3) :
    (univ.filter fun b : Fin 3 => pact g b = a).card = 1 := by
  revert g a; decide +kernel

/-- A matrix described by "fibers": `(N *ᵥ y) a = ∑_g w g * y (act g a)`. -/
theorem mulVec_fiber {ι : Type*} [Fintype ι] [DecidableEq ι] (act : Perm (Fin 4) → ι → ι)
    (w : Perm (Fin 4) → R) (N : Matrix ι ι R)
    (hN : ∀ a b, N a b = ∑ g, if act g a = b then w g else 0) (y : ι → R) (a : ι) :
    (N *ᵥ y) a = ∑ g, w g * y (act g a) := by
  simp only [mulVec, dotProduct, hN, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp [ite_mul]

theorem cofactorPermMatrix_fiber (A : Matrix (Fin 4) (Fin 4) R) (a b : Fin 4) :
    cofactorPermMatrix A a b = ∑ g : Perm (Fin 4), if g a = b then phi A g else 0 :=
  (sum_fiber_perm A a b).symm

theorem signCofactorMatrix_fiber (A : Matrix (Fin 4) (Fin 4) R) (a b : Fin 4) :
    signCofactorMatrix A a b =
      ∑ g : Perm (Fin 4), if g a = b then ((permSgn g : ℤ) : R) * phi A g else 0 :=
  (sum_fiber_sign A a b).symm

theorem pairingMatrix_fiber (A : Matrix (Fin 4) (Fin 4) R) (i j : Fin 3) :
    pairingMatrix A i j = ∑ g : Perm (Fin 4), if pact g j = i then phi A g else 0 := by
  rw [pairingMatrix, of_apply, Finset.sum_filter]
  exact Finset.sum_congr rfl fun g _ => if_congr (pact_spec g j i) rfl rfl

theorem pairingMatrix_transpose_fiber (A : Matrix (Fin 4) (Fin 4) R) (a b : Fin 3) :
    (pairingMatrix A)ᵀ a b = ∑ g : Perm (Fin 4), if pact g a = b then phi A g else 0 :=
  pairingMatrix_fiber A b a

theorem schurPower_mulVec_apply (A : Matrix (Fin 4) (Fin 4) R) (c : Perm (Fin 4) → R)
    (σ : Perm (Fin 4)) :
    (schurPower A *ᵥ c) σ = ∑ g : Perm (Fin 4), phi A g * c (g * σ) := by
  rw [mulVec, dotProduct, ← Equiv.sum_comp (Equiv.mulRight σ)]
  refine Finset.sum_congr rfl fun g _ => ?_
  congr 1
  simp only [schurPower, of_apply, phi, Equiv.coe_mulRight, Perm.mul_apply]
  exact Equiv.prod_comp σ (fun i => A i (g i))

section Lifts

/-- `liftF y σ = y (σ 0)`. -/
def liftF (y : Fin 4 → R) : Perm (Fin 4) → R := fun σ => y (σ 0)
/-- `liftG y σ = sgn σ * y (σ 0)`. -/
def liftG (y : Fin 4 → R) : Perm (Fin 4) → R := fun σ => ((permSgn σ : ℤ) : R) * y (σ 0)
/-- The index `k` with `σ(P_0) = P_k`. -/
def pairIdx (σ : Perm (Fin 4)) : Fin 3 := pact σ 0
/-- `liftH z σ = z (pairIdx σ)`. -/
def liftH (z : Fin 3 → R) : Perm (Fin 4) → R := fun σ => z (pairIdx σ)

theorem schurPower_mulVec_liftF (A : Matrix (Fin 4) (Fin 4) R) (y : Fin 4 → R) :
    schurPower A *ᵥ liftF y = liftF (cofactorPermMatrix A *ᵥ y) := by
  funext σ
  rw [schurPower_mulVec_apply, liftF,
    mulVec_fiber (fun g a => g a) (phi A) _ (cofactorPermMatrix_fiber A) y]
  rfl

theorem schurPower_mulVec_liftG (A : Matrix (Fin 4) (Fin 4) R) (y : Fin 4 → R) :
    schurPower A *ᵥ liftG y = liftG (signCofactorMatrix A *ᵥ y) := by
  funext σ
  rw [schurPower_mulVec_apply, liftG,
    mulVec_fiber (fun g a => g a) (fun g => ((permSgn g : ℤ) : R) * phi A g) _
      (signCofactorMatrix_fiber A) y, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [liftG, Perm.mul_apply, permSgn_mul, Int.cast_mul]
  ring

theorem schurPower_mulVec_liftH (A : Matrix (Fin 4) (Fin 4) R) (z : Fin 3 → R) :
    schurPower A *ᵥ liftH z = liftH ((pairingMatrix A)ᵀ *ᵥ z) := by
  funext σ
  rw [schurPower_mulVec_apply, liftH, pairIdx,
    mulVec_fiber pact (phi A) _ (pairingMatrix_transpose_fiber A) z]
  exact Finset.sum_congr rfl fun g _ => by simp [liftH, pairIdx, pact_mul]

theorem cofactorPermMatrix_mulVec_one (A : Matrix (Fin 4) (Fin 4) R) :
    cofactorPermMatrix A *ᵥ (1 : Fin 4 → R) = A.permanent • (1 : Fin 4 → R) := by
  funext a
  rw [mulVec_fiber (fun g a => g a) (phi A) _ (cofactorPermMatrix_fiber A)]
  simp [sum_phi_eq_permanent]

theorem signCofactorMatrix_mulVec_one (A : Matrix (Fin 4) (Fin 4) R) :
    signCofactorMatrix A *ᵥ (1 : Fin 4 → R) = A.det • (1 : Fin 4 → R) := by
  funext a
  rw [mulVec_fiber (fun g a => g a) (fun g => ((permSgn g : ℤ) : R) * phi A g) _
    (signCofactorMatrix_fiber A)]
  simp [sum_sign_phi_eq_det]

theorem pairingMatrix_transpose_mulVec_one (A : Matrix (Fin 4) (Fin 4) R) :
    (pairingMatrix A)ᵀ *ᵥ (1 : Fin 3 → R) = A.permanent • (1 : Fin 3 → R) := by
  funext a
  rw [mulVec_fiber pact (phi A) _ (pairingMatrix_transpose_fiber A)]
  simp [sum_phi_eq_permanent]

theorem pairingMatrix_mulVec_one (A : Matrix (Fin 4) (Fin 4) R) :
    pairingMatrix A *ᵥ (1 : Fin 3 → R) = A.permanent • (1 : Fin 3 → R) := by
  funext a
  simp only [mulVec, dotProduct, pairingMatrix_fiber, Pi.one_apply, mul_one, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_comm, ← sum_phi_eq_permanent]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, card_pact_pre, one_smul]

theorem schurPower_mulVec_const (A : Matrix (Fin 4) (Fin 4) R) :
    schurPower A *ᵥ (fun _ => (1 : R)) = A.permanent • (fun _ => (1 : R)) := by
  funext σ
  rw [schurPower_mulVec_apply]
  simp [sum_phi_eq_permanent]

theorem schurPower_mulVec_sign (A : Matrix (Fin 4) (Fin 4) R) :
    schurPower A *ᵥ (fun σ => ((permSgn σ : ℤ) : R)) = A.det • (fun σ => ((permSgn σ : ℤ) : R)) := by
  funext σ
  rw [schurPower_mulVec_apply, ← sum_sign_phi_eq_det]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [permSgn_mul, Int.cast_mul]
  ring

theorem schurPower_mulVec_liftF_eigen (A : Matrix (Fin 4) (Fin 4) R) {y : Fin 4 → R} {μ : R}
    (h : cofactorPermMatrix A *ᵥ y = μ • y) : schurPower A *ᵥ liftF y = μ • liftF y := by
  rw [schurPower_mulVec_liftF, h]; rfl

theorem liftF_ne_zero {y : Fin 4 → R} (hy : y ≠ 0) : liftF y ≠ 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hy
  intro h
  have := congrFun h (Equiv.swap 0 a)
  simp [liftF] at this
  exact ha this

end Lifts

end Algebra

section Gram

theorem sum_perm_fix (f : Fin 4 → ℂ) : ∑ σ : Perm (Fin 4), f (σ 0) = 6 * ∑ a, f a := by
  rw [← Finset.sum_fiberwise univ (fun σ : Perm (Fin 4) => σ 0), Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_congr rfl (fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2]),
    Finset.sum_const, card_fix, nsmul_eq_mul]
  norm_num

theorem sum_perm_pair (f : Fin 3 → ℂ) : ∑ σ : Perm (Fin 4), f (pairIdx σ) = 8 * ∑ a, f a := by
  rw [← Finset.sum_fiberwise univ (fun σ : Perm (Fin 4) => pairIdx σ), Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_congr rfl (fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2]),
    Finset.sum_const, show (univ.filter fun σ : Perm (Fin 4) => pairIdx σ = a).card = 8 from
      card_pact a, nsmul_eq_mul]
  norm_num

theorem star_liftF_dotProduct (y w : Fin 4 → ℂ) :
    star (liftF y) ⬝ᵥ liftF w = 6 * (star y ⬝ᵥ w) := by
  simp only [dotProduct, liftF, Pi.star_apply]
  exact sum_perm_fix (fun a => star (y a) * w a)

theorem star_liftG_dotProduct (y w : Fin 4 → ℂ) :
    star (liftG y) ⬝ᵥ liftG w = 6 * (star y ⬝ᵥ w) := by
  have : ∀ σ : Perm (Fin 4), star (liftG y σ) * liftG w σ = star (y (σ 0)) * w (σ 0) := by
    intro σ
    have h : ((permSgn σ : ℤ) : ℂ) * ((permSgn σ : ℤ) : ℂ) = 1 := by exact_mod_cast permSgn_mul_self σ
    simp only [liftG, star_mul', star_intCast]
    linear_combination (star (y (σ 0)) * w (σ 0)) * h
  simp only [dotProduct, Pi.star_apply, this]
  exact sum_perm_fix (fun a => star (y a) * w a)

theorem star_liftH_dotProduct (z w : Fin 3 → ℂ) :
    star (liftH z) ⬝ᵥ liftH w = 8 * (star z ⬝ᵥ w) := by
  simp only [dotProduct, liftH, Pi.star_apply]
  exact sum_perm_pair (fun a => star (z a) * w a)

/-- The quadratic form of `lam I - Π(A)` on `liftF y` is `6` times that of `lam I - F` on `y`. -/
theorem liftF_form (A : Matrix (Fin 4) (Fin 4) ℂ) (lam : ℂ) (y : Fin 4 → ℂ) :
    star (liftF y) ⬝ᵥ ((lam • (1 : Matrix (Perm (Fin 4)) (Perm (Fin 4)) ℂ) - schurPower A) *ᵥ
        liftF y) =
      6 * (star y ⬝ᵥ ((lam • (1 : Matrix (Fin 4) (Fin 4) ℂ) - cofactorPermMatrix A) *ᵥ y)) := by
  rw [sub_mulVec, smul_mulVec, one_mulVec, schurPower_mulVec_liftF, sub_mulVec, smul_mulVec,
    one_mulVec]
  have : lam • liftF y - liftF (cofactorPermMatrix A *ᵥ y) =
      liftF (lam • y - cofactorPermMatrix A *ᵥ y) := rfl
  rw [this, star_liftF_dotProduct]

theorem liftG_form (A : Matrix (Fin 4) (Fin 4) ℂ) (lam : ℂ) (y : Fin 4 → ℂ) :
    star (liftG y) ⬝ᵥ ((lam • (1 : Matrix (Perm (Fin 4)) (Perm (Fin 4)) ℂ) - schurPower A) *ᵥ
        liftG y) =
      6 * (star y ⬝ᵥ ((lam • (1 : Matrix (Fin 4) (Fin 4) ℂ) - signCofactorMatrix A) *ᵥ y)) := by
  rw [sub_mulVec, smul_mulVec, one_mulVec, schurPower_mulVec_liftG, sub_mulVec, smul_mulVec,
    one_mulVec]
  have : lam • liftG y - liftG (signCofactorMatrix A *ᵥ y) =
      liftG (lam • y - signCofactorMatrix A *ᵥ y) := by
    funext σ; simp [liftG]; ring
  rw [this, star_liftG_dotProduct]

/-- The quadratic form of `lam I - Π(A)` on `liftH z` is `8` times that of `lam I - Hᵀ` on `z`. -/
theorem liftH_form (A : Matrix (Fin 4) (Fin 4) ℂ) (lam : ℂ) (z : Fin 3 → ℂ) :
    star (liftH z) ⬝ᵥ ((lam • (1 : Matrix (Perm (Fin 4)) (Perm (Fin 4)) ℂ) - schurPower A) *ᵥ
        liftH z) =
      8 * (star z ⬝ᵥ ((lam • (1 : Matrix (Fin 3) (Fin 3) ℂ) - (pairingMatrix A)ᵀ) *ᵥ z)) := by
  rw [sub_mulVec, smul_mulVec, one_mulVec, schurPower_mulVec_liftH, sub_mulVec, smul_mulVec,
    one_mulVec]
  have : lam • liftH z - liftH ((pairingMatrix A)ᵀ *ᵥ z) =
      liftH (lam • z - (pairingMatrix A)ᵀ *ᵥ z) := rfl
  rw [this, star_liftH_dotProduct]

/-- Transposition is conjugation of the test vector. -/
theorem dotProduct_transpose_mulVec {n : Type*} [Fintype n] (M : Matrix n n ℂ) (z : n → ℂ) :
    star z ⬝ᵥ (Mᵀ *ᵥ z) = star (star z) ⬝ᵥ (M *ᵥ star z) := by
  simp only [dotProduct, mulVec, Pi.star_apply, star_star, transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Same as `liftH_form`, with `H = pairingMatrix A` itself and the conjugated vector. -/
theorem liftH_form' (A : Matrix (Fin 4) (Fin 4) ℂ) (lam : ℂ) (z : Fin 3 → ℂ) :
    star (liftH z) ⬝ᵥ ((lam • (1 : Matrix (Perm (Fin 4)) (Perm (Fin 4)) ℂ) - schurPower A) *ᵥ
        liftH z) =
      8 * (star (star z) ⬝ᵥ ((lam • (1 : Matrix (Fin 3) (Fin 3) ℂ) - pairingMatrix A) *ᵥ star z)) := by
  rw [liftH_form]
  congr 1
  have := dotProduct_transpose_mulVec (lam • (1 : Matrix (Fin 3) (Fin 3) ℂ) - pairingMatrix A) z
  simpa [transpose_sub, transpose_smul] using this

theorem star_const_dotProduct_schurPower (A : Matrix (Fin 4) (Fin 4) ℂ) :
    star (fun _ : Perm (Fin 4) => (1 : ℂ)) ⬝ᵥ (schurPower A *ᵥ fun _ => (1 : ℂ)) =
      24 * A.permanent := by
  rw [schurPower_mulVec_const]
  simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_one, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]
  norm_num [Nat.factorial]

theorem star_sign_dotProduct_schurPower (A : Matrix (Fin 4) (Fin 4) ℂ) :
    star (fun σ : Perm (Fin 4) => ((permSgn σ : ℤ) : ℂ)) ⬝ᵥ
        (schurPower A *ᵥ fun σ => ((permSgn σ : ℤ) : ℂ)) = 24 * A.det := by
  rw [schurPower_mulVec_sign]
  have h : ∀ σ : Perm (Fin 4), ((permSgn σ : ℤ) : ℂ) * ((permSgn σ : ℤ) : ℂ) = 1 := fun σ => by
    exact_mod_cast permSgn_mul_self σ
  simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_intCast]
  have : ∀ σ : Perm (Fin 4), ((permSgn σ : ℤ) : ℂ) * (A.det * ((permSgn σ : ℤ) : ℂ)) = A.det := fun σ => by
    linear_combination A.det * h σ
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]
  norm_num

end Gram

namespace Sector

structure PAct (ι : Type) [Fintype ι] [DecidableEq ι] where
  act : Perm (Fin 4) → ι → ι
  mul : ∀ g h a, act (g * h) a = act g (act h a)
  one : ∀ a, act 1 a = a

structure Twist where
  ε : Perm (Fin 4) → ℤ
  one : ε 1 = 1
  mul : ∀ g h, ε (g * h) = ε g * ε h
  sq : ∀ g, ε g * ε g = 1

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def PAct.equiv (P : PAct ι) (σ : Perm (Fin 4)) : ι ≃ ι where
  toFun := P.act σ
  invFun := P.act σ⁻¹
  left_inv a := by rw [← P.mul, inv_mul_cancel, P.one]
  right_inv a := by rw [← P.mul, mul_inv_cancel, P.one]

def blockVec (P : PAct ι) (T : Twist) (v : ι → ℤ) (x : Perm (Fin 4) → ℂ) : ι → ℂ :=
  fun a => ∑ σ, (T.ε σ : ℂ) * (v (P.act σ⁻¹ a) : ℂ) * x σ

def bchar (P : PAct ι) (T : Twist) (v : ι → ℤ) (h : Perm (Fin 4)) : ℤ :=
  T.ε h * ∑ a, v a * v (P.act h a)

def Ulin (x : Perm (Fin 4) → ℂ) (g : Perm (Fin 4)) : (Perm (Fin 4) → ℂ) →ₗ[ℂ] ℂ :=
  ∑ σ, ∑ τ, (star (x σ) * x τ) • LinearMap.proj (τ⁻¹ * g * σ)

theorem Ulin_apply (x : Perm (Fin 4) → ℂ) (g : Perm (Fin 4)) (c : Perm (Fin 4) → ℂ) :
    Ulin x g c = ∑ σ, ∑ τ, star (x σ) * x τ * c (τ⁻¹ * g * σ) := by
  simp [Ulin, LinearMap.sum_apply]

theorem Twist.inv (T : Twist) (g : Perm (Fin 4)) : T.ε g⁻¹ = T.ε g := by
  have h1 := T.mul g g⁻¹
  rw [mul_inv_cancel, T.one] at h1
  calc T.ε g⁻¹ = (T.ε g * T.ε g) * T.ε g⁻¹ := by rw [T.sq, one_mul]
    _ = T.ε g * (T.ε g * T.ε g⁻¹) := by ring
    _ = T.ε g := by rw [← h1, mul_one]

theorem bchar_key (P : PAct ι) (T : Twist) (v : ι → ℤ) (σ τ g : Perm (Fin 4)) :
    T.ε g * T.ε σ * T.ε τ * ∑ a, v (P.act σ⁻¹ a) * v (P.act τ⁻¹ (P.act g a)) =
      bchar P T v (τ⁻¹ * g * σ) := by
  rw [bchar, T.mul, T.mul, T.inv]
  have : ∑ a, v (P.act σ⁻¹ a) * v (P.act τ⁻¹ (P.act g a)) =
      ∑ b, v b * v (P.act (τ⁻¹ * g * σ) b) := by
    rw [← Equiv.sum_comp (P.equiv σ)]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [PAct.equiv, Equiv.coe_fn_mk]
    rw [← P.mul, inv_mul_cancel, P.one, ← P.mul, ← P.mul, mul_assoc]
  rw [this]; ring

theorem block_D (P : PAct ι) (T : Twist) (v : ι → ℤ) (x : Perm (Fin 4) → ℂ) (g : Perm (Fin 4)) :
    (T.ε g : ℂ) * ∑ a, star (blockVec P T v x a) * blockVec P T v x (P.act g a) =
      ∑ σ, ∑ τ, star (x σ) * x τ * (bchar P T v (τ⁻¹ * g * σ) : ℂ) := by
  simp only [blockVec, star_sum, star_mul', star_intCast]
  simp_rw [Finset.sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← bchar_key P T v σ τ g]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem block_form (P : PAct ι) (T : Twist) (v : ι → ℤ) (w : Perm (Fin 4) → ℂ) (lam : ℂ)
    (N : Matrix ι ι ℂ)
    (hN : ∀ a b, N a b = ∑ g, if P.act g a = b then (T.ε g : ℂ) * w g else 0)
    (x : Perm (Fin 4) → ℂ) :
    star (blockVec P T v x) ⬝ᵥ ((lam • (1 : Matrix ι ι ℂ) - N) *ᵥ blockVec P T v x) =
      lam * Ulin x 1 (fun h => (bchar P T v h : ℂ)) -
        ∑ g, w g * Ulin x g (fun h => (bchar P T v h : ℂ)) := by
  set y := blockVec P T v x with hy
  have h1 : star y ⬝ᵥ ((lam • (1 : Matrix ι ι ℂ) - N) *ᵥ y) =
      lam * (star y ⬝ᵥ y) - star y ⬝ᵥ (N *ᵥ y) := by
    rw [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have h2 : star y ⬝ᵥ (N *ᵥ y) =
      ∑ g, w g * ((T.ε g : ℂ) * ∑ a, star (y a) * y (P.act g a)) := by
    simp only [dotProduct, mulVec_fiber P.act _ N hN y, Pi.star_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun a _ => by ring
  have h3 : star y ⬝ᵥ y = (T.ε 1 : ℂ) * ∑ a, star (y a) * y (P.act 1 a) := by
    simp [P.one, T.one, dotProduct]
  rw [h1, h2, h3]
  simp only [hy, block_D, Ulin_apply]


def PAct.pt : PAct (Fin 4) := ⟨fun g a => g a, fun _ _ _ => rfl, fun _ => rfl⟩
def PAct.pair : PAct (Fin 3) := ⟨pact, pact_mul, pact_one⟩
def PAct.unit : PAct Unit := ⟨fun _ a => a, fun _ _ _ => rfl, fun _ => rfl⟩
def Twist.triv : Twist := ⟨fun _ => 1, rfl, fun _ _ => by simp, fun _ => by simp⟩
def Twist.sign : Twist := ⟨permSgn, permSgn_one, permSgn_mul, permSgn_mul_self⟩

/-- Orthogonal basis of `1^⊥ ⊆ ℚ^4`. -/
def vv : Fin 3 → Fin 4 → ℤ := ![![1, -1, 0, 0], ![1, 1, -2, 0], ![1, 1, 1, -3]]
/-- Orthogonal basis of `1^⊥ ⊆ ℚ^3`. -/
def ww : Fin 2 → Fin 3 → ℤ := ![![1, -1, 0], ![1, 1, -2]]
def vu : Unit → ℤ := fun _ => 1
def n31 : Fin 3 → ℤ := ![18, 6, 3]
def n22 : Fin 2 → ℤ := ![12, 4]

/-- Character identity: `24 · (sum of d_ρ χ_ρ)` as the regular representation. -/
theorem char_id (h : Perm (Fin 4)) :
    12 * bchar PAct.unit Twist.triv vu h + 12 * bchar PAct.unit Twist.sign vu h +
      ∑ k, n31 k * bchar PAct.pt Twist.triv (vv k) h +
      ∑ k, n31 k * bchar PAct.pt Twist.sign (vv k) h +
      ∑ l, n22 l * bchar PAct.pair Twist.triv (ww l) h = if h = 1 then 288 else 0 := by
  revert h; decide +kernel

theorem perp_Q3 (M : Matrix (Fin 4) (Fin 4) ℂ)
    (hM : ((Q3 : Matrix (Fin 4) (Fin 3) ℂ)ᵀ * M * Q3).PosSemidef) (y : Fin 4 → ℂ)
    (hy : ∑ a, y a = 0) : 0 ≤ star y ⬝ᵥ (M *ᵥ y) := by
  have hQ : (Q3 : Matrix (Fin 4) (Fin 3) ℂ)ᴴ = (Q3 : Matrix (Fin 4) (Fin 3) ℂ)ᵀ := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Q3]
  have hy3 : y 3 = -(y 0 + y 1 + y 2) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hy
    simp at hy
    linear_combination hy
  have hy' : y = (Q3 : Matrix (Fin 4) (Fin 3) ℂ) *ᵥ (fun a => y a.castSucc) := by
    funext a
    fin_cases a <;> simp [Q3, mulVec, dotProduct, Fin.sum_univ_succ, hy3]
    ring
  rw [hy']
  have := hM.dotProduct_mulVec_nonneg (fun a => y a.castSucc)
  rw [hQ.symm] at this
  simpa [star_mulVec, dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul,
    Matrix.mul_assoc] using this

theorem perp_Q2 (M : Matrix (Fin 3) (Fin 3) ℂ)
    (hM : ((Q2 : Matrix (Fin 3) (Fin 2) ℂ)ᵀ * M * Q2).PosSemidef) (y : Fin 3 → ℂ)
    (hy : ∑ a, y a = 0) : 0 ≤ star y ⬝ᵥ (M *ᵥ y) := by
  have hQ : (Q2 : Matrix (Fin 3) (Fin 2) ℂ)ᴴ = (Q2 : Matrix (Fin 3) (Fin 2) ℂ)ᵀ := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Q2]
  have hy3 : y 2 = -(y 0 + y 1) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hy
    simp at hy
    linear_combination hy
  have hy' : y = (Q2 : Matrix (Fin 3) (Fin 2) ℂ) *ᵥ (fun a => y a.castSucc) := by
    funext a
    fin_cases a <;> simp [Q2, mulVec, dotProduct, Fin.sum_univ_succ, hy3]
    ring
  rw [hy']
  have := hM.dotProduct_mulVec_nonneg (fun a => y a.castSucc)
  rw [hQ.symm] at this
  simpa [star_mulVec, dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul,
    Matrix.mul_assoc] using this

theorem blockVec_sum (P : PAct ι) (T : Twist) (v : ι → ℤ) (hv : ∑ a, v a = 0)
    (x : Perm (Fin 4) → ℂ) : ∑ a, blockVec P T v x a = 0 := by
  simp only [blockVec]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun σ _ => ?_
  have e : ∑ a, v (P.act σ⁻¹ a) = ∑ a, v a := Equiv.sum_comp (P.equiv σ⁻¹) v
  have : ∑ a, (v (P.act σ⁻¹ a) : ℂ) = 0 := by rw [← Int.cast_sum, e, hv]; simp
  calc ∑ a, (T.ε σ : ℂ) * (v (P.act σ⁻¹ a) : ℂ) * x σ
      = ((T.ε σ : ℂ) * x σ) * ∑ a, (v (P.act σ⁻¹ a) : ℂ) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
    _ = 0 := by rw [this, mul_zero]

theorem unit_nonneg (N : Matrix Unit Unit ℂ) (lam : ℂ) (h : N () () ≤ lam) (y : Unit → ℂ) :
    0 ≤ star y ⬝ᵥ ((lam • (1 : Matrix Unit Unit ℂ) - N) *ᵥ y) := by
  have e : star y ⬝ᵥ ((lam • (1 : Matrix Unit Unit ℂ) - N) *ᵥ y) =
      (lam - N () ()) * (star (y ()) * y ()) := by
    simp [dotProduct, mulVec]; ring
  rw [e]
  exact mul_nonneg (sub_nonneg.2 h) (star_mul_self_nonneg _)

def blk (P : PAct ι) (T : Twist) (v : ι → ℤ) (N : Matrix ι ι ℂ) (lam : ℂ)
    (x : Perm (Fin 4) → ℂ) : ℂ :=
  star (blockVec P T v x) ⬝ᵥ ((lam • (1 : Matrix ι ι ℂ) - N) *ᵥ blockVec P T v x)

def Phi (x w : Perm (Fin 4) → ℂ) (lam : ℂ) : (Perm (Fin 4) → ℂ) →ₗ[ℂ] ℂ :=
  lam • Ulin x 1 - ∑ g, w g • Ulin x g

theorem Phi_apply (x w : Perm (Fin 4) → ℂ) (lam : ℂ) (c : Perm (Fin 4) → ℂ) :
    Phi x w lam c = lam * Ulin x 1 c - ∑ g, w g * Ulin x g c := by
  simp [Phi, LinearMap.sum_apply]

theorem blk_eq (P : PAct ι) (T : Twist) (v : ι → ℤ) (w : Perm (Fin 4) → ℂ) (lam : ℂ)
    (N : Matrix ι ι ℂ)
    (hN : ∀ a b, N a b = ∑ g, if P.act g a = b then (T.ε g : ℂ) * w g else 0)
    (x : Perm (Fin 4) → ℂ) :
    blk P T v N lam x = Phi x w lam (fun h => (bchar P T v h : ℂ)) := by
  rw [blk, block_form P T v w lam N hN x, Phi_apply]

theorem Ulin_delta (x : Perm (Fin 4) → ℂ) (g : Perm (Fin 4)) :
    Ulin x g (fun h => if h = 1 then (288 : ℂ) else 0) = 288 * ∑ σ, star (x σ) * x (g * σ) := by
  rw [Ulin_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have : ∀ τ : Perm (Fin 4), (if τ⁻¹ * g * σ = 1 then (288 : ℂ) else 0) =
      if g * σ = τ then 288 else 0 := fun τ =>
    if_congr (by rw [mul_assoc, inv_mul_eq_one]; exact eq_comm) rfl rfl
  simp only [this, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem qf_eq (A : Matrix (Fin 4) (Fin 4) ℂ) (lam : ℂ) (x : Perm (Fin 4) → ℂ) :
    star x ⬝ᵥ ((lam • (1 : Matrix (Perm (Fin 4)) (Perm (Fin 4)) ℂ) - schurPower A) *ᵥ x) =
      lam * ∑ σ, star (x σ) * x σ - ∑ g, phi A g * ∑ σ, star (x σ) * x (g * σ) := by
  rw [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  congr 1
  simp only [dotProduct, Pi.star_apply, schurPower_mulVec_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun σ _ => by ring

def N0 (A : Matrix (Fin 4) (Fin 4) ℂ) : Matrix Unit Unit ℂ := Matrix.of fun _ _ => A.permanent
def N1 (A : Matrix (Fin 4) (Fin 4) ℂ) : Matrix Unit Unit ℂ := Matrix.of fun _ _ => A.det

theorem sector_identity (A : Matrix (Fin 4) (Fin 4) ℂ) (lam : ℂ) (x : Perm (Fin 4) → ℂ) :
    288 * (star x ⬝ᵥ ((lam • (1 : Matrix (Perm (Fin 4)) (Perm (Fin 4)) ℂ) - schurPower A) *ᵥ x)) =
      12 * blk PAct.unit Twist.triv vu (N0 A) lam x +
      12 * blk PAct.unit Twist.sign vu (N1 A) lam x +
      ∑ k, (n31 k : ℂ) * blk PAct.pt Twist.triv (vv k) (cofactorPermMatrix A) lam x +
      ∑ k, (n31 k : ℂ) * blk PAct.pt Twist.sign (vv k) (signCofactorMatrix A) lam x +
      ∑ l, (n22 l : ℂ) * blk PAct.pair Twist.triv (ww l) (pairingMatrix A)ᵀ lam x := by
  have hN0 : ∀ a b : Unit, N0 A a b =
      ∑ g, if PAct.unit.act g a = b then (Twist.triv.ε g : ℂ) * phi A g else 0 := by
    intro a b
    simp [N0, PAct.unit, Twist.triv, sum_phi_eq_permanent]
  have hN1 : ∀ a b : Unit, N1 A a b =
      ∑ g, if PAct.unit.act g a = b then (Twist.sign.ε g : ℂ) * phi A g else 0 := by
    intro a b
    simp [N1, PAct.unit, Twist.sign, ← sum_sign_phi_eq_det A]
  have hNF : ∀ a b : Fin 4, cofactorPermMatrix A a b =
      ∑ g, if PAct.pt.act g a = b then (Twist.triv.ε g : ℂ) * phi A g else 0 := by
    intro a b
    simp [PAct.pt, Twist.triv, cofactorPermMatrix_fiber]
  have hNG : ∀ a b : Fin 4, signCofactorMatrix A a b =
      ∑ g, if PAct.pt.act g a = b then (Twist.sign.ε g : ℂ) * phi A g else 0 := by
    intro a b
    simp [PAct.pt, Twist.sign, signCofactorMatrix_fiber]
  have hNH : ∀ a b : Fin 3, (pairingMatrix A)ᵀ a b =
      ∑ g, if PAct.pair.act g a = b then (Twist.triv.ε g : ℂ) * phi A g else 0 := by
    intro a b
    simp [PAct.pair, Twist.triv, pairingMatrix_fiber]
  simp only [blk_eq PAct.unit Twist.triv vu (phi A) lam _ hN0,
    blk_eq PAct.unit Twist.sign vu (phi A) lam _ hN1,
    blk_eq PAct.pt Twist.triv _ (phi A) lam _ hNF,
    blk_eq PAct.pt Twist.sign _ (phi A) lam _ hNG,
    blk_eq PAct.pair Twist.triv _ (phi A) lam _ hNH]
  have hcomb : (12 : ℂ) • (fun h => (bchar PAct.unit Twist.triv vu h : ℂ)) +
      (12 : ℂ) • (fun h => (bchar PAct.unit Twist.sign vu h : ℂ)) +
      ∑ k, (n31 k : ℂ) • (fun h => (bchar PAct.pt Twist.triv (vv k) h : ℂ)) +
      ∑ k, (n31 k : ℂ) • (fun h => (bchar PAct.pt Twist.sign (vv k) h : ℂ)) +
      ∑ l, (n22 l : ℂ) • (fun h => (bchar PAct.pair Twist.triv (ww l) h : ℂ)) =
      fun h => if h = 1 then (288 : ℂ) else 0 := by
    funext h
    simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    have := char_id h
    exact_mod_cast this
  have h2 := congrArg (Phi x (phi A) lam) hcomb
  simp only [map_add, map_sum, map_smul, smul_eq_mul] at h2
  rw [h2, qf_eq, Phi_apply]
  simp only [Ulin_delta, one_mul]
  have e1 : (288 : ℂ) * ∑ g, phi A g * ∑ σ, star (x σ) * x (g * σ) =
      ∑ g, phi A g * (288 * ∑ σ, star (x σ) * x (g * σ)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun g _ => by ring
  rw [mul_sub, e1]; ring

end Sector

open Sector in
/-- **Sector reduction.**  If `K₃₁, K₂₁₁, K₂₂ ⪰ 0` at level `lam` and `per A, det A ≤ lam`, then
`lam I - Π(A) ⪰ 0`. -/
theorem schurPower_defect_posSemidef (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.IsHermitian)
    (lam : ℝ) (hp : A.permanent ≤ (lam : ℂ)) (hdet : A.det ≤ (lam : ℂ))
    (h31 : (K31 (lam : ℂ) A).PosSemidef) (h211 : (K211 (lam : ℂ) A).PosSemidef)
    (h22 : (K22 (lam : ℂ) A).PosSemidef) :
    ((lam : ℂ) • (1 : Matrix (Perm (Fin 4)) (Perm (Fin 4)) ℂ) - schurPower A).PosSemidef := by
  have hherm : ((lam : ℂ) • (1 : Matrix (Perm (Fin 4)) (Perm (Fin 4)) ℂ) - schurPower A).IsHermitian := by
    simp [Matrix.IsHermitian, conjTranspose_sub, conjTranspose_smul, (schurPower_isHermitian hA).eq]
  refine PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => ?_
  have h288 := sector_identity A (lam : ℂ) x
  have hn31 : ∀ k, (0 : ℂ) ≤ (n31 k : ℂ) := fun k => by fin_cases k <;> simp [n31]
  have hn22 : ∀ l, (0 : ℂ) ≤ (n22 l : ℂ) := fun l => by fin_cases l <;> simp [n22]
  have hvv : ∀ k, ∑ a, vv k a = 0 := fun k => by fin_cases k <;> simp [vv, Fin.sum_univ_succ]
  have hww : ∀ l, ∑ a, ww l a = 0 := fun l => by fin_cases l <;> simp [ww, Fin.sum_univ_succ]
  have hK22 : ((Q2 : Matrix (Fin 3) (Fin 2) ℂ)ᵀ *
      ((lam : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) - (pairingMatrix A)ᵀ) * Q2).PosSemidef := by
    have : ((Q2 : Matrix (Fin 3) (Fin 2) ℂ)ᵀ *
      ((lam : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) - (pairingMatrix A)ᵀ) * Q2) = (K22 (lam : ℂ) A)ᵀ := by
      simp [K22, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this]; exact h22.transpose
  have hnn : 0 ≤ 12 * blk PAct.unit Twist.triv vu (N0 A) (lam : ℂ) x +
      12 * blk PAct.unit Twist.sign vu (N1 A) (lam : ℂ) x +
      ∑ k, (n31 k : ℂ) * blk PAct.pt Twist.triv (vv k) (cofactorPermMatrix A) (lam : ℂ) x +
      ∑ k, (n31 k : ℂ) * blk PAct.pt Twist.sign (vv k) (signCofactorMatrix A) (lam : ℂ) x +
      ∑ l, (n22 l : ℂ) * blk PAct.pair Twist.triv (ww l) (pairingMatrix A)ᵀ (lam : ℂ) x := by
    refine add_nonneg (add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_) ?_
    · exact mul_nonneg (by norm_num) (unit_nonneg (N0 A) _ hp _)
    · exact mul_nonneg (by norm_num) (unit_nonneg (N1 A) _ hdet _)
    · exact Finset.sum_nonneg fun k _ => mul_nonneg (hn31 k)
        (perp_Q3 _ h31 _ (blockVec_sum _ _ _ (hvv k) x))
    · exact Finset.sum_nonneg fun k _ => mul_nonneg (hn31 k)
        (perp_Q3 _ h211 _ (blockVec_sum _ _ _ (hvv k) x))
    · exact Finset.sum_nonneg fun l _ => mul_nonneg (hn22 l)
        (perp_Q2 _ hK22 _ (blockVec_sum _ _ _ (hww l) x))
  rw [← h288] at hnn
  exact le_of_mul_le_mul_left (by rwa [mul_zero]) (by norm_num : (0 : ℂ) < 288)


end Results.SoulesPotOrderFour
