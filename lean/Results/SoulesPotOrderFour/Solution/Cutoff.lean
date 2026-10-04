import Results.SoulesPotOrderFour.Defs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Logic.Equiv.Fintype

/-!
# The order cutoff: counterexamples of rank two in every order `n ≥ 5`

`not_pot_of_five_le n` : for `n ≥ 5` there is a complex Hermitian PSD `A` of order `n` and
rank `≤ 2` with `¬ (per A • 1 - Π(A)).PosSemidef`.

Route (elementary, no representation theory).  Write `A = Vᴴ V` with `V : Matrix (Fin 2) (Fin n) ℂ`.
Then `Π(A) = Wᴴ W` with `W x σ = ∏ j, V (x j) (σ j)` (`x : Fin n → Fin 2`).  For a test vector `u`
on the `2^n` basis states, `c = Wᴴ u` satisfies `cᴴ Π c ≥ ‖c‖⁴/‖u‖²` (Cauchy–Schwarz), so
`‖Wᴴ u‖² > per(A) ‖u‖²` contradicts `Π(A) ⪯ per(A) I` (`not_psd_of_test`).

* for a basis state the quantity `‖Wᴴ u‖²` is a permanent with two column types (`perm_two_colors`),
* `per(Vᴴ V)` is `∑ k! (n-k)! |c_k|²` (`permanent_gram`), `∑ c_k X^k = ∏ (α_i + β_i X)`.

The families have lacunary `∏ (α_i + β_i X)`, so `per` has two terms while the "incoherent"
polynomial `∏ (|α_i|² + |β_i|² X)` is a binomial power.
-/

open Matrix Equiv Finset
open scoped ComplexOrder

namespace Results.SoulesPotOrderFour

namespace Cutoff

open Polynomial

variable {n : ℕ}

/-- The tensor vector `w_σ(x) = ∏_j V_{x_j, σ(j)}`, `x ∈ {0,1}ⁿ`. -/
def wv (V : Matrix (Fin 2) (Fin n) ℂ) (σ : Perm (Fin n)) (x : Fin n → Fin 2) : ℂ :=
  ∏ j, V (x j) (σ j)

/-- `Π(VᴴV) = WᴴW`. -/
lemma schurPower_gram (V : Matrix (Fin 2) (Fin n) ℂ) (σ τ : Perm (Fin n)) :
    schurPower (Vᴴ * V) σ τ = ∑ x : Fin n → Fin 2, star (wv V σ x) * wv V τ x := by
  simp only [schurPower, of_apply, mul_apply, conjTranspose_apply, wv]
  rw [Finset.prod_univ_sum (fun _ => (univ : Finset (Fin 2)))
    (fun j s => star (V s (σ j)) * V s (τ j)), Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [star_prod, ← Finset.prod_mul_distrib]

lemma posSemidef_gram (V : Matrix (Fin 2) (Fin n) ℂ) : (Vᴴ * V).PosSemidef :=
  posSemidef_conjTranspose_mul_self V

lemma rank_gram_le (V : Matrix (Fin 2) (Fin n) ℂ) : (Vᴴ * V).rank ≤ 2 :=
  (rank_mul_le_right _ _).trans (rank_le_height V)

lemma star_mul_self_real (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_mul']; push_cast; ring

/-- **Test-vector criterion.**  If `c_σ = ∑_k a_k conj(w_σ(x_k))` has `∑_σ |c_σ|² > per(A) ∑_k |a_k|²`
(distinct basis states `x_k`), then `per(A) I - Π(A)` is not positive semidefinite. -/
theorem not_psd_of_test {κ : Type*} [Fintype κ] (V : Matrix (Fin 2) (Fin n) ℂ)
    (x : κ → (Fin n → Fin 2)) (hx : Function.Injective x) (a : κ → ℂ)
    (hp : 0 ≤ (permanent (Vᴴ * V)).re)
    (h : (permanent (Vᴴ * V)).re * ∑ k, ‖a k‖ ^ 2 <
      ∑ σ : Perm (Fin n), ‖∑ k, a k * star (wv V σ (x k))‖ ^ 2) :
    ¬ ((permanent (Vᴴ * V)) • (1 : Matrix (Perm (Fin n)) (Perm (Fin n)) ℂ) -
        schurPower (Vᴴ * V)).PosSemidef := by
  intro hPSD
  classical
  set p := permanent (Vᴴ * V) with hpdef
  set c : Perm (Fin n) → ℂ := fun σ => ∑ k, a k * star (wv V σ (x k)) with hc
  set z : (Fin n → Fin 2) → ℂ := fun y => ∑ σ, wv V σ y * c σ with hz
  set Q : ℝ := ∑ σ, ‖c σ‖ ^ 2 with hQ
  set R : ℝ := ∑ y, ‖z y‖ ^ 2 with hR
  set A : ℝ := ∑ k, ‖a k‖ ^ 2 with hA
  have hz_star : ∀ y, star (z y) = ∑ σ, star (c σ) * star (wv V σ y) := by
    intro y
    simp only [hz, star_sum, star_mul]
  have hfact : ∀ σ, ∑ τ, schurPower (Vᴴ * V) σ τ * c τ = ∑ y, star (wv V σ y) * z y := by
    intro σ
    simp only [schurPower_gram, Finset.sum_mul, hz, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun τ _ => ?_
    ring
  have hRq : star c ⬝ᵥ (schurPower (Vᴴ * V) *ᵥ c) = (R : ℂ) := by
    have e1 : star c ⬝ᵥ (schurPower (Vᴴ * V) *ᵥ c) = ∑ y, star (z y) * z y := by
      simp only [dotProduct, mulVec, hfact, Pi.star_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hz_star, Finset.sum_mul]
      exact Finset.sum_congr rfl fun σ _ => by ring
    rw [e1, hR, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun y _ => star_mul_self_real _
  have hQq : star c ⬝ᵥ c = (Q : ℂ) := by
    simp only [dotProduct, Pi.star_apply]
    rw [hQ, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun σ _ => star_mul_self_real _
  have h1 := hPSD.dotProduct_mulVec_nonneg c
  have h2 : star c ⬝ᵥ ((p • (1 : Matrix (Perm (Fin n)) (Perm (Fin n)) ℂ) -
      schurPower (Vᴴ * V)) *ᵥ c) = p * (Q : ℂ) - R := by
    rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, hQq, hRq,
      smul_eq_mul]
  rw [h2] at h1
  have hRle : R ≤ p.re * Q := by
    have := h1.1
    simpa using this
  have hQnn : 0 ≤ Q := Finset.sum_nonneg fun σ _ => sq_nonneg _
  have hAnn : 0 ≤ A := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hcσ : ∀ σ, star (c σ) = ∑ k, star (a k) * wv V σ (x k) := by
    intro σ
    simp only [hc, star_sum, star_mul, star_star]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hcs1 : ∑ k, star (a k) * z (x k) = (Q : ℂ) := by
    simp only [hz, Finset.mul_sum]
    rw [Finset.sum_comm, hQ, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← star_mul_self_real, hcσ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hcs2 : Q ^ 2 ≤ A * R := by
    have h3 : ‖∑ k, star (a k) * z (x k)‖ = Q := by
      rw [hcs1]; simp [abs_of_nonneg hQnn]
    have h4 : ‖∑ k, star (a k) * z (x k)‖ ≤ ∑ k, ‖a k‖ * ‖z (x k)‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun k _ => by simp
    have h5 : (∑ k, ‖a k‖ * ‖z (x k)‖) ^ 2 ≤ A * ∑ k, ‖z (x k)‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h6 : ∑ k, ‖z (x k)‖ ^ 2 ≤ R := by
      classical
      rw [hR, ← Finset.sum_image (f := fun y => ‖z y‖ ^ 2) (s := (univ : Finset κ))
        (hx.injOn)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => sq_nonneg _)
    calc Q ^ 2 = ‖∑ k, star (a k) * z (x k)‖ ^ 2 := by rw [h3]
      _ ≤ (∑ k, ‖a k‖ * ‖z (x k)‖) ^ 2 := by
        gcongr
      _ ≤ A * ∑ k, ‖z (x k)‖ ^ 2 := h5
      _ ≤ A * R := by gcongr
  have hpos : 0 < Q := by
    have : 0 ≤ p.re * A := mul_nonneg hp hAnn
    linarith
  have : Q * Q ≤ (A * p.re) * Q := by
    calc Q * Q = Q ^ 2 := by ring
      _ ≤ A * R := hcs2
      _ ≤ A * (p.re * Q) := by gcongr
      _ = (A * p.re) * Q := by ring
  have := le_of_mul_le_mul_right this hpos
  linarith
/-! ### Two column types: the permanent of a matrix with two kinds of columns -/

/-- number of ones of `x : Fin n → Fin 2` -/
def wt (x : Fin n → Fin 2) : ℕ := ∑ i, (x i : ℕ)

lemma fin2_val (a : Fin 2) : (a : ℕ) = if a = 1 then 1 else 0 := by
  fin_cases a <;> rfl

lemma wt_eq_card (x : Fin n → Fin 2) : wt x = (univ.filter fun i => x i = 1).card := by
  rw [wt, Finset.card_filter]
  exact Finset.sum_congr rfl fun i _ => fin2_val _

lemma wt_le (x : Fin n → Fin 2) : wt x ≤ n := by
  rw [wt_eq_card]; exact (Finset.card_le_univ _).trans (by simp)

lemma wt_comp (f : Fin n → Fin 2) (σ : Perm (Fin n)) : wt (f ∘ σ) = wt f := by
  unfold wt
  exact Equiv.sum_comp σ (fun j => (f j : ℕ))

lemma fin2_eq_iff (a b : Fin 2) : a = b ↔ (a = 1 ↔ b = 1) := by
  fin_cases a <;> fin_cases b <;> simp

/-- permutation built from equivalences of the two colour classes -/
lemma subtypeCongr_apply_pos {p q : Fin n → Prop} [DecidablePred p] [DecidablePred q]
    (e1 : {i // p i} ≃ {j // q j}) (e0 : {i // ¬ p i} ≃ {j // ¬ q j}) (i : Fin n) (hi : p i) :
    Equiv.subtypeCongr e1 e0 i = (e1 ⟨i, hi⟩ : Fin n) := by
  simp [Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_pos hi]

lemma subtypeCongr_apply_neg {p q : Fin n → Prop} [DecidablePred p] [DecidablePred q]
    (e1 : {i // p i} ≃ {j // q j}) (e0 : {i // ¬ p i} ≃ {j // ¬ q j}) (i : Fin n) (hi : ¬ p i) :
    Equiv.subtypeCongr e1 e0 i = (e0 ⟨i, hi⟩ : Fin n) := by
  simp [Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_neg hi]

/-- The permutations `σ` with `f ∘ σ = h` are `(#ones)! (#zeros)!` many (when `h` and `f` have the
same number of ones): `σ` is a pair of bijections between the colour classes. -/
lemma card_fib (f h : Fin n → Fin 2) (hw : wt h = wt f) :
    (univ.filter fun σ : Perm (Fin n) => f ∘ σ = h).card = (wt f).factorial * (n - wt f).factorial := by
  classical
  have hcp : Fintype.card {i // h i = 1} = wt f := by
    rw [Fintype.card_subtype, ← wt_eq_card, hw]
  have hcq : Fintype.card {j // f j = 1} = wt f := by
    rw [Fintype.card_subtype, ← wt_eq_card]
  have hcp' : Fintype.card {i // ¬ h i = 1} = n - wt f := by
    rw [Fintype.card_subtype_compl, hcp]; simp
  have hcq' : Fintype.card {j // ¬ f j = 1} = n - wt f := by
    rw [Fintype.card_subtype_compl, hcq]; simp
  let e1 : {i // h i = 1} ≃ {j // f j = 1} := Fintype.equivOfCardEq (hcp.trans hcq.symm)
  let e0 : {i // ¬ h i = 1} ≃ {j // ¬ f j = 1} := Fintype.equivOfCardEq (hcp'.trans hcq'.symm)
  let Φ : ({i // h i = 1} ≃ {j // f j = 1}) × ({i // ¬ h i = 1} ≃ {j // ¬ f j = 1}) → Perm (Fin n) :=
    fun e => Equiv.subtypeCongr e.1 e.2
  have hΦinj : Function.Injective Φ := by
    intro e e' hee
    have h1 : ∀ i, Equiv.subtypeCongr e.1 e.2 i = Equiv.subtypeCongr e'.1 e'.2 i :=
      fun i => by simpa [Φ] using congrArg (fun σ : Perm (Fin n) => σ i) hee
    refine Prod.ext (Equiv.ext fun i => Subtype.ext ?_) (Equiv.ext fun i => Subtype.ext ?_)
    · have := h1 i.1
      rw [subtypeCongr_apply_pos (p := fun i => h i = 1) (q := fun j => f j = 1) e.1 e.2 i.1 i.2,
        subtypeCongr_apply_pos (p := fun i => h i = 1) (q := fun j => f j = 1) e'.1 e'.2 i.1 i.2]
        at this
      exact this
    · have := h1 i.1
      rw [subtypeCongr_apply_neg (p := fun i => h i = 1) (q := fun j => f j = 1) e.1 e.2 i.1 i.2,
        subtypeCongr_apply_neg (p := fun i => h i = 1) (q := fun j => f j = 1) e'.1 e'.2 i.1 i.2]
        at this
      exact this
  have himg : (univ.filter fun σ : Perm (Fin n) => f ∘ σ = h) = univ.image Φ := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hσ
      have hp : ∀ a, h a = 1 ↔ f (σ a) = 1 := fun a => by rw [← hσ]; rfl
      refine ⟨(σ.subtypeEquiv hp, σ.subtypeEquiv fun a => not_congr (hp a)), ?_⟩
      refine Equiv.ext fun i => ?_
      show Equiv.subtypeCongr _ _ i = σ i
      by_cases hi : h i = 1
      · rw [subtypeCongr_apply_pos (p := fun i => h i = 1) (q := fun j => f j = 1) _ _ i hi]
        rfl
      · rw [subtypeCongr_apply_neg (p := fun i => h i = 1) (q := fun j => f j = 1) _ _ i hi]
        rfl
    · rintro ⟨e, rfl⟩
      funext i
      show f (Equiv.subtypeCongr e.1 e.2 i) = h i
      by_cases hi : h i = 1
      · rw [subtypeCongr_apply_pos (p := fun i => h i = 1) (q := fun j => f j = 1) e.1 e.2 i hi,
          fin2_eq_iff]
        exact ⟨fun _ => hi, fun _ => (e.1 ⟨i, hi⟩).2⟩
      · rw [subtypeCongr_apply_neg (p := fun i => h i = 1) (q := fun j => f j = 1) e.1 e.2 i hi,
          fin2_eq_iff]
        exact ⟨fun h' => absurd h' (e.2 ⟨i, hi⟩).2, fun h' => absurd h' hi⟩
  rw [himg, Finset.card_image_of_injective _ hΦinj, Finset.card_univ, Fintype.card_prod,
    Fintype.card_equiv e1, Fintype.card_equiv e0, hcp, hcp']

/-- The orbit of `f` under `σ ↦ f ∘ σ` is the set of `h` with the same number of ones. -/
lemma image_comp_eq (f : Fin n → Fin 2) :
    (univ.image fun σ : Perm (Fin n) => f ∘ σ) = univ.filter fun h : Fin n → Fin 2 => wt h = wt f := by
  classical
  ext h
  simp only [mem_image, mem_univ, true_and, mem_filter]
  constructor
  · rintro ⟨σ, rfl⟩
    exact wt_comp f σ
  · intro hw
    have hcp : Fintype.card {i // h i = 1} = Fintype.card {j // f j = 1} := by
      rw [Fintype.card_subtype, Fintype.card_subtype, ← wt_eq_card, ← wt_eq_card, hw]
    let e1 : {i // h i = 1} ≃ {j // f j = 1} := Fintype.equivOfCardEq hcp
    refine ⟨e1.extendSubtype, funext fun i => ?_⟩
    show f (e1.extendSubtype i) = h i
    by_cases hi : h i = 1
    · rw [fin2_eq_iff]
      exact ⟨fun _ => hi, fun _ => Equiv.extendSubtype_mem e1 i hi⟩
    · rw [fin2_eq_iff]
      exact ⟨fun h' => absurd h' (Equiv.extendSubtype_not_mem e1 i hi), fun h' => absurd h' hi⟩

/-- **Permanent with two column types.**  The columns `j` of `(M (σ j) (f j))` take two values;
the sum over `σ` is `(#ones)! (#zeros)!` times the sum over all rows-to-colour assignments `h` with
the same number of ones. -/
theorem perm_two_colors {R : Type*} [CommRing R] (M : Fin n → Fin 2 → R) (f : Fin n → Fin 2) :
    ∑ σ : Perm (Fin n), ∏ j, M (σ j) (f j) =
      (((wt f).factorial * (n - wt f).factorial : ℕ) : R) *
        ∑ h ∈ univ.filter (fun h : Fin n → Fin 2 => wt h = wt f), ∏ i, M i (h i) := by
  classical
  set G : (Fin n → Fin 2) → R := fun h => ∏ i, M i (h i) with hG
  have h1 : ∀ σ : Perm (Fin n), ∏ j, M (σ j) (f j) = G (f ∘ σ.symm) := by
    intro σ
    simp only [hG, Function.comp_apply]
    rw [← Equiv.prod_comp σ (fun i => M i (f (σ.symm i)))]
    simp
  simp_rw [h1]
  have h2 : ∑ σ : Perm (Fin n), G (f ∘ σ.symm) = ∑ σ : Perm (Fin n), G (f ∘ σ) :=
    Equiv.sum_comp (Equiv.inv (Perm (Fin n))) (fun σ => G (f ∘ σ))
  rw [h2, Finset.sum_comp G (fun σ : Perm (Fin n) => f ∘ σ), image_comp_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [mem_filter] at hh
  rw [show (univ.filter fun σ : Perm (Fin n) => f ∘ σ = h) = _ from rfl, card_fib f h hh.2,
    nsmul_eq_mul]

/-- coefficients of `∏ (M i 0 + M i 1 X)` are sums over colourings with a given number of ones -/
lemma poly_coeff {R : Type*} [CommRing R] (M : Fin n → Fin 2 → R) (k : ℕ) :
    (∏ i, (C (M i 0) + C (M i 1) * X : R[X])).coeff k =
      ∑ h ∈ univ.filter (fun h : Fin n → Fin 2 => wt h = k), ∏ i, M i (h i) := by
  classical
  have h1 : ∏ i, (C (M i 0) + C (M i 1) * X : R[X]) =
      ∑ h : Fin n → Fin 2, C (∏ i, M i (h i)) * X ^ wt h := by
    have : ∀ i, (C (M i 0) + C (M i 1) * X : R[X]) = ∑ s : Fin 2, C (M i s) * X ^ (s : ℕ) := by
      intro i; simp [Fin.sum_univ_two]
    simp_rw [this]
    rw [Finset.prod_univ_sum (fun _ => (univ : Finset (Fin 2)))
      (fun i s => C (M i s) * X ^ (s : ℕ)), Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
    rfl
  rw [h1, Polynomial.finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun h _ => by simp [eq_comm]

lemma wv_one (V : Matrix (Fin 2) (Fin n) ℂ) (x : Fin n → Fin 2) :
    wv V 1 x = ∏ i, V (x i) i := by simp [wv]

/-- `∑_σ w_σ(x) = (#ones)! (#zeros)! c_{#ones}`, `c_k` the coefficients of `∏ (α_i + β_i X)`. -/
lemma sum_wv (V : Matrix (Fin 2) (Fin n) ℂ) (x : Fin n → Fin 2) :
    ∑ σ : Perm (Fin n), wv V σ x = (((wt x).factorial * (n - wt x).factorial : ℕ) : ℂ) *
      (∏ i, (C (V 0 i) + C (V 1 i) * X : ℂ[X])).coeff (wt x) := by
  rw [poly_coeff (fun i s => V s i)]
  exact perm_two_colors (fun r s => V s r) x

/-- `per(VᴴV) = ∑_k k!(n-k)! |c_k|²`, `∑ c_k X^k = ∏ (α_i + β_i X)` (as an identity in `ℂ`). -/
theorem permanent_gram (V : Matrix (Fin 2) (Fin n) ℂ) :
    permanent (Vᴴ * V) = ∑ k ∈ range (n + 1), (((k.factorial * (n - k).factorial : ℕ) : ℂ) *
      (star ((∏ i, (C (V 0 i) + C (V 1 i) * X : ℂ[X])).coeff k) *
        (∏ i, (C (V 0 i) + C (V 1 i) * X : ℂ[X])).coeff k)) := by
  classical
  set cc : ℕ → ℂ := fun k => (∏ i, (C (V 0 i) + C (V 1 i) * X : ℂ[X])).coeff k with hcc
  have hcc' : ∀ k, cc k = ∑ h ∈ univ.filter (fun h : Fin n → Fin 2 => wt h = k), wv V 1 h := by
    intro k
    simp only [hcc, wv_one]
    exact poly_coeff (fun i s => V s i) k
  have h1 : ∀ σ : Perm (Fin n), ∏ i, (Vᴴ * V) (σ i) i =
      ∑ x : Fin n → Fin 2, star (wv V σ x) * wv V 1 x := by
    intro σ
    simp only [mul_apply, conjTranspose_apply, wv]
    rw [Finset.prod_univ_sum (fun _ => (univ : Finset (Fin 2)))
      (fun i s => star (V s (σ i)) * V s i), Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [star_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => rfl
  rw [permanent]
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ x : Fin n → Fin 2, ∑ σ : Perm (Fin n), star (wv V σ x) * wv V 1 x =
      (((wt x).factorial * (n - wt x).factorial : ℕ) : ℂ) * (star (cc (wt x)) * wv V 1 x) := by
    intro x
    rw [← Finset.sum_mul, ← star_sum, sum_wv, star_mul', mul_assoc]
    congr 1
    simp
  simp_rw [h2]
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := range (n + 1)) (g := wt)
    (fun x _ => Finset.mem_range.2 (Nat.lt_succ_of_le (wt_le x)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_congr rfl (g := fun x => (((k.factorial * (n - k).factorial : ℕ) : ℂ) *
      (star (cc k) * wv V 1 x))) (fun x hx => by rw [(mem_filter.1 hx).2])]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← hcc']

/-- polynomial `∏ (α_i + β_i X)` of the columns `(α_i, β_i)` of `V` -/
noncomputable def cpoly (V : Matrix (Fin 2) (Fin n) ℂ) : ℂ[X] :=
  ∏ i, (C (V 0 i) + C (V 1 i) * X)

/-- the "incoherent" polynomial `∏ (|α_i|² + |β_i|² X)` -/
noncomputable def qpoly (V : Matrix (Fin 2) (Fin n) ℂ) : ℝ[X] :=
  ∏ i, (C (‖V 0 i‖ ^ 2) + C (‖V 1 i‖ ^ 2) * X)

lemma sum_norm_wv (V : Matrix (Fin 2) (Fin n) ℂ) (x : Fin n → Fin 2) :
    ∑ σ : Perm (Fin n), ‖wv V σ x‖ ^ 2 =
      (((wt x).factorial * (n - wt x).factorial : ℕ) : ℝ) * (qpoly V).coeff (wt x) := by
  rw [qpoly, poly_coeff (fun i s => ‖V s i‖ ^ 2)]
  have := perm_two_colors (R := ℝ) (fun r s => ‖V s r‖ ^ 2) x
  rw [← this]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [wv, norm_prod, Finset.prod_pow]

lemma permanent_gram_re (V : Matrix (Fin 2) (Fin n) ℂ) :
    (permanent (Vᴴ * V)).re = ∑ k ∈ range (n + 1),
      (((k.factorial * (n - k).factorial : ℕ) : ℝ) * ‖(cpoly V).coeff k‖ ^ 2) := by
  rw [permanent_gram, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cpoly, star_mul_self_real, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- **Basis-state criterion.**  If `a! (n-a)! [X^a] ∏ (|α_i|² + |β_i|² X)` exceeds
`∑_k k!(n-k)! |c_k|²` (`= per(VᴴV)`) for a basis state `x` with `a` ones, then `per I - Π`
is not positive semidefinite. -/
theorem not_psd_of_basis (V : Matrix (Fin 2) (Fin n) ℂ) (x : Fin n → Fin 2)
    (h : ∑ k ∈ range (n + 1), (((k.factorial * (n - k).factorial : ℕ) : ℝ) *
        ‖(cpoly V).coeff k‖ ^ 2) <
      (((wt x).factorial * (n - wt x).factorial : ℕ) : ℝ) * (qpoly V).coeff (wt x)) :
    ¬ ((permanent (Vᴴ * V)) • (1 : Matrix (Perm (Fin n)) (Perm (Fin n)) ℂ) -
        schurPower (Vᴴ * V)).PosSemidef := by
  have hre := permanent_gram_re V
  refine not_psd_of_test V (fun _ : Unit => x) (fun a b _ => Subsingleton.elim a b) (fun _ => 1) ?_ ?_
  · rw [hre]
    exact Finset.sum_nonneg fun k _ => by positivity
  · rw [hre]
    simpa [sum_norm_wv] using h

lemma exists_wt {a : ℕ} (ha : a ≤ n) : ∃ x : Fin n → Fin 2, wt x = a := by
  classical
  obtain ⟨F, -, hF⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (Fin n))) (n := a)
    (by simpa using ha)
  refine ⟨fun i => if i ∈ F then 1 else 0, ?_⟩
  rw [wt_eq_card, ← hF]
  congr 1
  ext i
  simp

/-- columns `(lacA i, lacB i)`: `p` poles `e₀ = (1,0)`, `q` poles `e₁ = (0,1)`, then the ring
`(1, l i^k)`, `k < 4`. -/
def lacA (p q : ℕ) (i : ℕ) : ℂ := if p ≤ i ∧ i < p + q then 0 else 1
def lacB (p q : ℕ) (l : ℂ) (i : ℕ) : ℂ :=
  if i < p then 0 else if i < p + q then 1 else l * Complex.I ^ (i - p - q)

def lacV (n p q : ℕ) (l : ℂ) : Matrix (Fin 2) (Fin n) ℂ :=
  Matrix.of fun s i => if s = 0 then lacA p q i else lacB p q l i

lemma ring_block (l : ℂ) :
    ∏ x ∈ range 4, (C (1 : ℂ) + C (l * Complex.I ^ x) * X) = 1 - C (l ^ 4) * X ^ 4 := by
  have hJ : (C Complex.I : ℂ[X]) * C Complex.I = -1 := by
    rw [← C_mul, Complex.I_mul_I]; simp
  have h2 : (C (l * Complex.I ^ 2) : ℂ[X]) = - C l := by
    rw [Complex.I_sq]; simp
  have h3 : (C (l * Complex.I ^ 3) : ℂ[X]) = - (C l * C Complex.I) := by
    rw [Complex.I_pow_three]; simp
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, pow_zero, pow_one, mul_one,
    h2, h3, map_one]
  rw [map_mul]
  simp only [map_pow]
  linear_combination (-(1 - (C l) ^ 2 * X ^ 2) * (C l) ^ 2 * X ^ 2) * hJ

lemma ring_block_q (r : ℝ) :
    ∏ _x ∈ range 4, (C (1 : ℝ) + C r * X) = (1 + C r * X) ^ 4 := by
  simp [Finset.prod_const]

lemma cpoly_lac (p q : ℕ) (l : ℂ) :
    cpoly (lacV (p + q + 4) p q l) = X ^ q * (1 - C (l ^ 4) * X ^ 4) := by
  have key : ∀ i : Fin (p + q + 4), (C ((lacV (p + q + 4) p q l) 0 i) +
      C ((lacV (p + q + 4) p q l) 1 i) * X : ℂ[X]) = C (lacA p q i) + C (lacB p q l i) * X :=
    fun i => by simp [lacV]
  unfold cpoly
  simp_rw [key]
  rw [Fin.prod_univ_eq_prod_range (fun i => (C (lacA p q i) + C (lacB p q l i) * X : ℂ[X]))
    (p + q + 4), Finset.prod_range_add, Finset.prod_range_add]
  have hb1 : ∏ i ∈ range p, (C (lacA p q i) + C (lacB p q l i) * X : ℂ[X]) = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    simp [lacA, lacB, hi', not_le.2 hi']
  have hb2 : ∏ x ∈ range q, (C (lacA p q (p + x)) + C (lacB p q l (p + x)) * X : ℂ[X]) =
      X ^ q := by
    rw [Finset.prod_congr rfl (g := fun _ => X) ?_]
    · simp
    intro x hx
    have hx' := Finset.mem_range.1 hx
    have h1 : p ≤ p + x ∧ p + x < p + q := ⟨by omega, by omega⟩
    have h2 : ¬ (p + x < p) := by omega
    simp [lacA, lacB, h1, h2]
  have hb3 : ∏ x ∈ range 4, (C (lacA p q (p + q + x)) + C (lacB p q l (p + q + x)) * X : ℂ[X]) =
      ∏ x ∈ range 4, (C (1 : ℂ) + C (l * Complex.I ^ x) * X) := by
    refine Finset.prod_congr rfl fun x _ => ?_
    have h1 : ¬ (p ≤ p + q + x ∧ p + q + x < p + q) := by omega
    have h2 : ¬ (p + q + x < p) := by omega
    have h3 : ¬ (p + q + x < p + q) := by omega
    have h4 : p + q + x - p - q = x := by omega
    simp [lacA, lacB, h2, h3, h4]
  rw [hb1, hb2, hb3, ring_block, one_mul]

lemma qpoly_lac (p q : ℕ) (l : ℂ) :
    qpoly (lacV (p + q + 4) p q l) = X ^ q * (1 + C (‖l‖ ^ 2) * X) ^ 4 := by
  have key : ∀ i : Fin (p + q + 4), (C (‖(lacV (p + q + 4) p q l) 0 i‖ ^ 2) +
      C (‖(lacV (p + q + 4) p q l) 1 i‖ ^ 2) * X : ℝ[X]) =
      C (‖lacA p q i‖ ^ 2) + C (‖lacB p q l i‖ ^ 2) * X :=
    fun i => by simp [lacV]
  unfold qpoly
  simp_rw [key]
  rw [Fin.prod_univ_eq_prod_range (fun i => (C (‖lacA p q i‖ ^ 2) + C (‖lacB p q l i‖ ^ 2) * X : ℝ[X]))
    (p + q + 4), Finset.prod_range_add, Finset.prod_range_add]
  have hb1 : ∏ i ∈ range p, (C (‖lacA p q i‖ ^ 2) + C (‖lacB p q l i‖ ^ 2) * X : ℝ[X]) = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    simp [lacA, lacB, hi', not_le.2 hi']
  have hb2 : ∏ x ∈ range q, (C (‖lacA p q (p + x)‖ ^ 2) + C (‖lacB p q l (p + x)‖ ^ 2) * X : ℝ[X]) =
      X ^ q := by
    rw [Finset.prod_congr rfl (g := fun _ => X) ?_]
    · simp
    intro x hx
    have hx' := Finset.mem_range.1 hx
    have h1 : p ≤ p + x ∧ p + x < p + q := ⟨by omega, by omega⟩
    have h2 : ¬ (p + x < p) := by omega
    simp [lacA, lacB, h1, h2]
  have hb3 : ∏ x ∈ range 4, (C (‖lacA p q (p + q + x)‖ ^ 2) +
      C (‖lacB p q l (p + q + x)‖ ^ 2) * X : ℝ[X]) = (1 + C (‖l‖ ^ 2) * X) ^ 4 := by
    rw [← ring_block_q (‖l‖ ^ 2)]
    refine Finset.prod_congr rfl fun x _ => ?_
    have h1 : ¬ (p ≤ p + q + x ∧ p + q + x < p + q) := by omega
    have h2 : ¬ (p + q + x < p) := by omega
    have h3 : ¬ (p + q + x < p + q) := by omega
    have h4 : p + q + x - p - q = x := by omega
    simp [lacA, lacB, h2, h3, h4]
  rw [hb1, hb2, hb3, one_mul]

lemma coeff_two_terms (q k : ℕ) (a : ℂ) :
    ((X ^ q * (1 - C a * X ^ 4) : ℂ[X]).coeff k) =
      (if k = q then 1 else 0) - (if k = q + 4 then a else 0) := by
  have : (X ^ q * (1 - C a * X ^ 4) : ℂ[X]) = X ^ q - C a * X ^ (q + 4) := by ring
  rw [this, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X_pow]
  simp [mul_ite]

lemma sum_two_terms (q n : ℕ) (a : ℂ) (hq : q + 4 ≤ n) :
    ∑ k ∈ range (n + 1), (((k.factorial * (n - k).factorial : ℕ) : ℝ) *
      ‖(X ^ q * (1 - C a * X ^ 4) : ℂ[X]).coeff k‖ ^ 2) =
    ((q.factorial * (n - q).factorial : ℕ) : ℝ) +
      (((q + 4).factorial * (n - (q + 4)).factorial : ℕ) : ℝ) * ‖a‖ ^ 2 := by
  classical
  have hs : ({q, q + 4} : Finset ℕ) ⊆ range (n + 1) := by
    intro k hk
    simp only [mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl <;> simp <;> omega
  rw [← Finset.sum_subset hs ?_, Finset.sum_pair (by omega)]
  · simp [coeff_two_terms]
  · intro k _ hk
    simp only [mem_insert, mem_singleton, not_or] at hk
    simp [coeff_two_terms, hk.1, hk.2]

lemma coeff_binom4 (r : ℝ) : ((1 + C r * X : ℝ[X]) ^ 4).coeff 2 = 6 * r ^ 2 := by
  have : (1 + C r * X : ℝ[X]) ^ 4 = 1 + C (4 * r) * X + C (6 * r ^ 2) * X ^ 2 + C (4 * r ^ 3) * X ^ 3 +
      C (r ^ 4) * X ^ 4 := by
    simp only [map_mul, map_pow, map_ofNat]; ring
  rw [this]
  simp only [coeff_add, coeff_one, coeff_C_mul, coeff_X_pow, coeff_X]
  norm_num

lemma norm_real_pow8 (l : ℝ) : ‖((l : ℂ) ^ 4)‖ ^ 2 = l ^ 8 := by
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, ← pow_mul]
  have : (|l| ^ (4 * 2)) = l ^ 8 := by
    rw [show 4 * 2 = 2 * 4 by norm_num, pow_mul, sq_abs, ← pow_mul]
  exact this

lemma norm_real_sq (l : ℝ) : ‖(l : ℂ)‖ ^ 2 = l ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Lacunary family** (`p` poles `e₀`, `q` poles `e₁`, a ring `(1, l i^k)`): `per = q!(p+4)! +
l⁸ (q+4)! p!` and the basis state with `q+2` ones has weight `6 l⁴ (q+2)! (p+2)!`. -/
theorem lac_violation (p q : ℕ) (l : ℝ)
    (h : ((q.factorial * (p + 4).factorial : ℕ) : ℝ) +
        l ^ 8 * (((q + 4).factorial * p.factorial : ℕ) : ℝ) <
      6 * l ^ 4 * (((q + 2).factorial * (p + 2).factorial : ℕ) : ℝ)) :
    ∃ A : Matrix (Fin (p + q + 4)) (Fin (p + q + 4)) ℂ, A.PosSemidef ∧ A.rank ≤ 2 ∧
      ¬ ((A.permanent) • (1 : Matrix (Perm (Fin (p + q + 4))) (Perm (Fin (p + q + 4))) ℂ) -
        schurPower A).PosSemidef := by
  set V := lacV (p + q + 4) p q (l : ℂ) with hV
  refine ⟨Vᴴ * V, posSemidef_gram V, rank_gram_le V, ?_⟩
  obtain ⟨x, hx⟩ := exists_wt (n := p + q + 4) (a := q + 2) (by omega)
  refine not_psd_of_basis V x ?_
  rw [hV, cpoly_lac, sum_two_terms _ _ _ (by omega), qpoly_lac, hx,
    coeff_X_pow_mul', if_pos (by omega), show q + 2 - q = 2 by omega, coeff_binom4,
    norm_real_pow8, norm_real_sq,
    show p + q + 4 - q = p + 4 by omega, show p + q + 4 - (q + 4) = p by omega,
    show p + q + 4 - (q + 2) = p + 2 by omega]
  have : (6 * (l ^ 2) ^ 2 : ℝ) = 6 * l ^ 4 := by ring
  rw [this]
  linarith

/-! ### The arithmetic for `n ≥ 8` -/

lemma ineq_core (q : ℕ) (hq : 2 ≤ q) : 2 * (q + 3) * (q + 4) < 6 * (q + 1) * (q + 2) := by
  nlinarith

lemma ineq_even (q : ℕ) (hq : 2 ≤ q) :
    q.factorial * (q + 4).factorial + (q + 4).factorial * q.factorial <
      6 * ((q + 2).factorial * (q + 2).factorial) := by
  have h1 : (q + 2).factorial = (q + 2) * (q + 1) * q.factorial := by
    simp [Nat.factorial_succ]; ring
  have h2 : (q + 4).factorial = (q + 4) * (q + 3) * ((q + 2) * (q + 1)) * q.factorial := by
    simp [Nat.factorial_succ]; ring
  have hF : 0 < q.factorial := Nat.factorial_pos q
  have hc := ineq_core q hq
  rw [h1, h2]
  have h3 : 0 < (q + 2) * (q + 1) * q.factorial * q.factorial := by positivity
  nlinarith [mul_lt_mul_of_pos_left hc h3]

lemma ineq_odd (q : ℕ) (hq : 2 ≤ q) :
    q.factorial * (q + 1 + 4).factorial + (q + 4).factorial * (q + 1).factorial <
      6 * ((q + 2).factorial * (q + 1 + 2).factorial) := by
  have h0 : (q + 1).factorial = (q + 1) * q.factorial := by simp [Nat.factorial_succ]
  have h1 : (q + 2).factorial = (q + 2) * (q + 1) * q.factorial := by
    simp [Nat.factorial_succ]; ring
  have h3' : (q + 1 + 2).factorial = (q + 3) * (q + 2) * (q + 1) * q.factorial := by
    simp [Nat.factorial_succ]; ring
  have h2 : (q + 4).factorial = (q + 4) * (q + 3) * ((q + 2) * (q + 1)) * q.factorial := by
    simp [Nat.factorial_succ]; ring
  have h5 : (q + 1 + 4).factorial =
      (q + 5) * (q + 4) * (q + 3) * ((q + 2) * (q + 1)) * q.factorial := by
    simp [Nat.factorial_succ]; ring
  have hF : 0 < q.factorial := Nat.factorial_pos q
  have hc := ineq_core q hq
  rw [h0, h1, h2, h3', h5]
  have h3 : 0 < (q + 1) * (q + 2) * (q + 3) * (q.factorial * q.factorial) := by positivity
  nlinarith [mul_lt_mul_of_pos_left hc h3]

theorem exists_violation_of_eight_le (n : ℕ) (hn : 8 ≤ n) :
    ∃ A : Matrix (Fin n) (Fin n) ℂ, A.PosSemidef ∧ A.rank ≤ 2 ∧
      ¬ ((A.permanent) • (1 : Matrix (Perm (Fin n)) (Perm (Fin n)) ℂ) -
        schurPower A).PosSemidef := by
  obtain ⟨p, q, hpq, rfl, hq⟩ : ∃ p q : ℕ, (p = q ∨ p = q + 1) ∧ n = p + q + 4 ∧ 2 ≤ q :=
    ⟨n - 4 - (n - 4) / 2, (n - 4) / 2, by omega, by omega, by omega⟩
  apply lac_violation p q 1
  have key : q.factorial * (p + 4).factorial + (q + 4).factorial * p.factorial <
      6 * ((q + 2).factorial * (p + 2).factorial) := by
    rcases hpq with h | h
    · rw [h]; exact ineq_even q hq
    · rw [h]; exact ineq_odd q hq
  have h' : ((q.factorial * (p + 4).factorial + (q + 4).factorial * p.factorial : ℕ) : ℝ) <
      ((6 * ((q + 2).factorial * (p + 2).factorial) : ℕ) : ℝ) := Nat.cast_lt.2 key
  push_cast at h' ⊢
  linarith

theorem exists_violation_seven :
    ∃ A : Matrix (Fin 7) (Fin 7) ℂ, A.PosSemidef ∧ A.rank ≤ 2 ∧
      ¬ ((A.permanent) • (1 : Matrix (Perm (Fin 7)) (Perm (Fin 7)) ℂ) -
        schurPower A).PosSemidef :=
  lac_violation 2 1 (8 / 7) (by norm_num [Nat.factorial])

/-! ### `n = 6`: ring plus a real pair -/

def V6 (l μ : ℂ) : Matrix (Fin 2) (Fin 6) ℂ :=
  !![1, 1, 1, 1, 1, 1; l, l * Complex.I, -l, -(l * Complex.I), μ, -μ]

lemma cpoly_V6 (l μ : ℂ) :
    cpoly (V6 l μ) = (1 - C (l ^ 4) * X ^ 4) * (1 - C (μ ^ 2) * X ^ 2) := by
  have hJ : (C Complex.I : ℂ[X]) * C Complex.I = -1 := by
    rw [← C_mul, Complex.I_mul_I]; simp
  unfold cpoly
  simp only [V6, Fin.prod_univ_succ, Fin.prod_univ_zero]
  simp
  linear_combination ((1 - (C μ) ^ 2 * X ^ 2) * ((C l) ^ 4 * X ^ 4 - (C l) ^ 2 * X ^ 2)) * hJ

lemma qpoly_V6 (l μ : ℂ) :
    qpoly (V6 l μ) = (1 + C (‖l‖ ^ 2) * X) ^ 4 * (1 + C (‖μ‖ ^ 2) * X) ^ 2 := by
  unfold qpoly
  simp only [V6, Fin.prod_univ_succ, Fin.prod_univ_zero]
  simp
  ring

lemma coeff_P6 (A B : ℝ) (k : ℕ) :
    (((1 - C (A : ℂ) * X ^ 4) * (1 - C (B : ℂ) * X ^ 2) : ℂ[X])).coeff k =
      (if k = 0 then 1 else 0) - (if k = 2 then (B : ℂ) else 0) - (if k = 4 then (A : ℂ) else 0) +
        (if k = 6 then (A : ℂ) * B else 0) := by
  have : (((1 - C (A : ℂ) * X ^ 4) * (1 - C (B : ℂ) * X ^ 2) : ℂ[X])) =
      1 - C (B : ℂ) * X ^ 2 - C (A : ℂ) * X ^ 4 + C ((A : ℂ) * B) * X ^ 6 := by
    simp only [map_mul]; ring
  rw [this]
  simp only [coeff_sub, coeff_add, coeff_one, coeff_C_mul, coeff_X_pow]
  simp [mul_ite]

lemma sum_P6 (A B : ℝ) :
    ∑ k ∈ range (6 + 1), (((k.factorial * (6 - k).factorial : ℕ) : ℝ) *
      ‖(((1 - C (A : ℂ) * X ^ 4) * (1 - C (B : ℂ) * X ^ 2) : ℂ[X])).coeff k‖ ^ 2) =
    720 + 48 * B ^ 2 + 48 * A ^ 2 + 720 * (A * B) ^ 2 := by
  simp only [coeff_P6, Finset.sum_range_succ, Finset.sum_range_zero]
  simp [Nat.factorial]
  rw [← abs_mul, sq_abs]

lemma coeff4_prod (α β : ℝ) :
    (((1 + C α * X) ^ 4 * (1 + C β * X) ^ 2 : ℝ[X])).coeff 4 =
      α ^ 4 + 8 * α ^ 3 * β + 6 * α ^ 2 * β ^ 2 := by
  have : ((1 + C α * X) ^ 4 * (1 + C β * X) ^ 2 : ℝ[X]) =
      1 + C (2 * (2 * α + β)) * X + C (6 * α ^ 2 + 8 * α * β + β ^ 2) * X ^ 2 +
        C (4 * α * (α ^ 2 + 3 * α * β + β ^ 2)) * X ^ 3 +
        C (α ^ 2 * (α ^ 2 + 8 * α * β + 6 * β ^ 2)) * X ^ 4 +
        C (2 * α ^ 3 * β * (α + 2 * β)) * X ^ 5 + C (α ^ 4 * β ^ 2) * X ^ 6 := by
    simp only [map_mul, map_add, map_pow, map_ofNat]; ring
  rw [this]
  simp only [coeff_add, coeff_one, coeff_C_mul, coeff_X_pow, coeff_X]
  norm_num
  ring

theorem exists_violation_six :
    ∃ A : Matrix (Fin 6) (Fin 6) ℂ, A.PosSemidef ∧ A.rank ≤ 2 ∧
      ¬ ((A.permanent) • (1 : Matrix (Perm (Fin 6)) (Perm (Fin 6)) ℂ) -
        schurPower A).PosSemidef := by
  set l : ℝ := 5 / 2 with hl
  set μ : ℝ := 1 / 5 with hμ
  set V := V6 (l : ℂ) (μ : ℂ) with hV
  refine ⟨Vᴴ * V, posSemidef_gram V, rank_gram_le V, ?_⟩
  obtain ⟨x, hx⟩ := exists_wt (n := 6) (a := 4) (by norm_num)
  refine not_psd_of_basis V x ?_
  have hc : cpoly V = (1 - C (((l ^ 4 : ℝ)) : ℂ) * X ^ 4) * (1 - C (((μ ^ 2 : ℝ)) : ℂ) * X ^ 2) := by
    rw [hV, cpoly_V6]; push_cast; rfl
  rw [hc, sum_P6, hV, qpoly_V6, hx, norm_real_sq, norm_real_sq, coeff4_prod]
  rw [hl, hμ]
  norm_num [Nat.factorial]

/-! ### `n = 5`: a four-state test vector (two singlets times `e₀`) -/

def V5 (l : ℂ) : Matrix (Fin 2) (Fin 5) ℂ :=
  !![1, 1, 1, 1, 1; 0, l, l * Complex.I, -l, -(l * Complex.I)]

def x5 : Fin 4 → (Fin 5 → Fin 2) :=
  ![![0, 0, 0, 1, 1], ![0, 0, 1, 0, 1], ![0, 1, 0, 1, 0], ![0, 1, 1, 0, 0]]

def a5 : Fin 4 → ℂ := ![1, -1, -1, 1]

lemma x5_inj : Function.Injective x5 := by decide

lemma cpoly_V5 (l : ℂ) : cpoly (V5 l) = 1 - C (l ^ 4) * X ^ 4 := by
  have hJ : (C Complex.I : ℂ[X]) * C Complex.I = -1 := by
    rw [← C_mul, Complex.I_mul_I]; simp
  unfold cpoly
  simp only [V5, Fin.prod_univ_succ, Fin.prod_univ_zero]
  simp
  linear_combination (((C l) ^ 4 * X ^ 4 - (C l) ^ 2 * X ^ 2)) * hJ

lemma comb5 (V : Matrix (Fin 2) (Fin 5) ℂ) (σ : Perm (Fin 5)) :
    ∑ k, a5 k * wv V σ (x5 k) = V 0 (σ 0) * (V 0 (σ 1) * V 1 (σ 4) - V 1 (σ 1) * V 0 (σ 4)) *
      (V 0 (σ 2) * V 1 (σ 3) - V 1 (σ 2) * V 0 (σ 3)) := by
  simp only [Fin.sum_univ_four, a5, x5, wv, Fin.prod_univ_succ, Fin.prod_univ_zero]
  simp
  ring

def w5 (l : ℂ) : Fin 5 → ℂ := ![0, l, l * Complex.I, -l, -(l * Complex.I)]

def mtab : Fin 5 → Fin 5 → ℕ :=
  ![![0, 1, 1, 1, 1], ![1, 0, 2, 4, 2], ![1, 2, 0, 2, 4], ![1, 4, 2, 0, 2], ![1, 2, 4, 2, 0]]

lemma norm_w5 (l : ℝ) (i j : Fin 5) : ‖w5 l j - w5 l i‖ ^ 2 = l ^ 2 * (mtab i j : ℝ) := by
  fin_cases i <;> fin_cases j <;> simp [w5, mtab, Complex.sq_norm, Complex.normSq_apply] <;> ring

lemma sum_mtab : ∑ σ : Perm (Fin 5), (mtab (σ 1) (σ 4) * mtab (σ 2) (σ 3) : ℕ) = 448 := by
  decide +kernel

lemma sum_five (l : ℝ) :
    ∑ σ : Perm (Fin 5), ‖∑ k, a5 k * star (wv (V5 l) σ (x5 k))‖ ^ 2 = l ^ 4 * 448 := by
  have h1 : ∀ σ : Perm (Fin 5), ∑ k, a5 k * star (wv (V5 l) σ (x5 k)) =
      star (∑ k, a5 k * wv (V5 l) σ (x5 k)) := by
    intro σ
    simp only [star_sum, star_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : star (a5 k) = a5 k := by fin_cases k <;> simp [a5]
    rw [this, mul_comm]
  have e0 : ∀ j, V5 l 0 j = 1 := fun j => by fin_cases j <;> simp [V5]
  have e1 : ∀ j, V5 l 1 j = w5 l j := fun j => by fin_cases j <;> simp [V5, w5]
  have h2 : ∀ σ : Perm (Fin 5), ‖∑ k, a5 k * star (wv (V5 l) σ (x5 k))‖ ^ 2 =
      l ^ 4 * ((mtab (σ 1) (σ 4) * mtab (σ 2) (σ 3) : ℕ) : ℝ) := by
    intro σ
    rw [h1, norm_star, comb5]
    simp only [e0, e1, one_mul, mul_one, norm_mul, mul_pow]
    rw [norm_w5, norm_w5]
    push_cast
    ring
  simp_rw [h2]
  rw [← Finset.mul_sum]
  congr 1
  exact_mod_cast congrArg (Nat.cast (R := ℝ)) sum_mtab

theorem exists_violation_five :
    ∃ A : Matrix (Fin 5) (Fin 5) ℂ, A.PosSemidef ∧ A.rank ≤ 2 ∧
      ¬ ((A.permanent) • (1 : Matrix (Perm (Fin 5)) (Perm (Fin 5)) ℂ) -
        schurPower A).PosSemidef := by
  set l : ℝ := 6 / 5 with hl
  set V := V5 (l : ℂ) with hV
  refine ⟨Vᴴ * V, posSemidef_gram V, rank_gram_le V, ?_⟩
  have hper : (permanent (Vᴴ * V)).re = 120 + 24 * l ^ 8 := by
    rw [permanent_gram_re, hV, cpoly_V5]
    have := sum_two_terms 0 5 ((l : ℂ) ^ 4) (by norm_num)
    simp only [pow_zero, one_mul] at this
    rw [this, norm_real_pow8]
    norm_num [Nat.factorial]
  refine not_psd_of_test V x5 x5_inj a5 ?_ ?_
  · rw [hper]; positivity
  · rw [hper, hV, sum_five]
    have : ∑ k, ‖a5 k‖ ^ 2 = 4 := by simp [Fin.sum_univ_four, a5]; norm_num
    rw [this, hl]
    norm_num

end Cutoff

/-- **Theorem 1.3 / 3.3, negative direction.**  For every `n ≥ 5` there is a complex Hermitian
positive semidefinite matrix of order `n` and rank at most `2` with `Π(A) ⋠ per(A) I`. -/
theorem not_pot_of_five_le (n : ℕ) (hn : 5 ≤ n) :
    ∃ A : Matrix (Fin n) (Fin n) ℂ, A.PosSemidef ∧ A.rank ≤ 2 ∧
      ¬ ((A.permanent • (1 : Matrix (Perm (Fin n)) (Perm (Fin n)) ℂ) - schurPower A).PosSemidef) := by
  rcases (show n = 5 ∨ n = 6 ∨ n = 7 ∨ 8 ≤ n by omega) with rfl | rfl | rfl | h
  · exact Cutoff.exists_violation_five
  · exact Cutoff.exists_violation_six
  · exact Cutoff.exists_violation_seven
  · exact Cutoff.exists_violation_of_eight_le n h

end Results.SoulesPotOrderFour
