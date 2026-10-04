import Results.SoulesPotOrderFour.Solution.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset Matrix

/-!
# Kernel-checked certificate checker (Kronecker substitution)

A polynomial inequality `P ≥ 0` is proved from an exact Gram certificate
`lcm · P = ∑ μ_h · β_hᵀ N_h β_h` (`N_h` positive definite) as follows.

* `Gi` is the ring of Gaussian integers (pairs of integers) and `psi : MvPolynomial (Fin v) Gi →+* Gi` the
  Kronecker substitution `X_l ↦ 2^(b · D^l)`; `psi_inj` shows it is injective on polynomials with per-variable
  degree `< D` and `L¹` norm `< 2^(b-1)`, which is certified by the majorant calculus `Maj`.
* The Gram side is evaluated on packed integers: the keys of the basis terms are split into a low part
  (`D^vL` positions) and a high part (the *slices*); `Blk.slicesC` computes the contribution of one block to the
  slices `σ ≡ c (mod m)`, merged by `mergeTree` and compared with the slices of the target polynomial
  (`sliceOK`).  Each chunk `c` is a separate kernel computation (`checkS_of_parts`).
* Positivity of `N_h` is certified by an integer lower triangular `C_h` with `C_h N_h C_hᵀ` diagonally dominant
  (`Blk.psdOK`, checked with packed arithmetic, `Blk.psd_sound`).
* `checkP` (target side) and `checkS` (Gram side) give `cert_core`: `0 ≤ Re (ev t P)` for every real point `t`.
`KronPipe.lean` connects the polynomial pipeline to the matrices of `Basic.lean`; `KronBound.lean` treats the
`19/18` quadratic form in 14 variables.
-/

namespace Results.SoulesPotOrderFour
namespace Kron

@[ext] structure Gi where
  re : ℤ
  im : ℤ

namespace Gi
instance : Add Gi := ⟨fun a b => ⟨a.re + b.re, a.im + b.im⟩⟩
instance : Mul Gi := ⟨fun a b => ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩⟩
instance : Neg Gi := ⟨fun a => ⟨-a.re, -a.im⟩⟩
instance : Zero Gi := ⟨⟨0, 0⟩⟩
instance : One Gi := ⟨⟨1, 0⟩⟩
@[simp] theorem add_re (a b : Gi) : (a + b).re = a.re + b.re := rfl
@[simp] theorem add_im (a b : Gi) : (a + b).im = a.im + b.im := rfl
@[simp] theorem mul_re (a b : Gi) : (a * b).re = a.re * b.re - a.im * b.im := rfl
@[simp] theorem mul_im (a b : Gi) : (a * b).im = a.re * b.im + a.im * b.re := rfl
@[simp] theorem neg_re (a : Gi) : (-a).re = -a.re := rfl
@[simp] theorem neg_im (a : Gi) : (-a).im = -a.im := rfl
@[simp] theorem zero_re : (0 : Gi).re = 0 := rfl
@[simp] theorem zero_im : (0 : Gi).im = 0 := rfl
@[simp] theorem one_re : (1 : Gi).re = 1 := rfl
@[simp] theorem one_im : (1 : Gi).im = 0 := rfl
instance : CommRing Gi where
  add_assoc a b c := by ext <;> simp [add_assoc]
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp [add_comm]
  neg_add_cancel a := by ext <;> simp
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  mul_assoc a b c := by ext <;> simp <;> ring
  mul_comm a b := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  nsmul := nsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  zsmul := zsmulRec
  zsmul_zero' _ := rfl
  zsmul_succ' _ _ := rfl
  zsmul_neg' _ _ := rfl
  natCast n := ⟨n, 0⟩
  natCast_zero := by show (⟨((0:ℕ):ℤ), 0⟩ : Gi) = ⟨0, 0⟩; simp
  natCast_succ n := by
    show (⟨((n+1:ℕ):ℤ), 0⟩ : Gi) = ⟨((n:ℕ):ℤ) + 1, 0⟩; simp
  intCast n := ⟨n, 0⟩
  intCast_ofNat n := rfl
  intCast_negSucc n := by
    show (⟨Int.negSucc n, 0⟩ : Gi) = ⟨-(((n+1:ℕ):ℤ)), -0⟩; simp [Int.negSucc_eq]
@[simp] theorem natCast_re (n : ℕ) : (n : Gi).re = n := rfl
@[simp] theorem natCast_im (n : ℕ) : (n : Gi).im = 0 := rfl
@[simp] theorem intCast_re (n : ℤ) : (n : Gi).re = n := rfl
@[simp] theorem intCast_im (n : ℤ) : (n : Gi).im = 0 := rfl
@[simp] theorem sub_re (a b : Gi) : (a - b).re = a.re - b.re := by
  rw [sub_eq_add_neg]; simp [sub_eq_add_neg]
@[simp] theorem sub_im (a b : Gi) : (a - b).im = a.im - b.im := by
  rw [sub_eq_add_neg]; simp [sub_eq_add_neg]
instance : Nontrivial Gi := ⟨⟨0, 1, fun h => by have := congrArg Gi.re h; simp at this⟩⟩
/-- The imaginary unit. -/
def I : Gi := ⟨0, 1⟩
/-- Evaluation `ℤ[i] → ℂ`. -/
def toC : Gi →+* ℂ where
  toFun a := (a.re : ℂ) + (a.im : ℂ) * Complex.I
  map_one' := by simp
  map_mul' a b := by
    simp only [mul_re, mul_im]; push_cast
    apply Complex.ext <;> simp
  map_zero' := by simp
  map_add' a b := by simp only [add_re, add_im]; push_cast; ring
/-- real part as additive hom -/
def reHom : Gi →+ ℤ := ⟨⟨Gi.re, rfl⟩, add_re⟩
def imHom : Gi →+ ℤ := ⟨⟨Gi.im, rfl⟩, add_im⟩
end Gi

/-- Digit lemma. -/
theorem digit_zero {ι : Type*} [DecidableEq ι] (c : ι → ℤ) (k : ι → ℕ) (B : ℕ) (hB : 2 ≤ B)
    (s : Finset ι) (hk : Set.InjOn k s) (hc : ∀ i ∈ s, |c i| < B)
    (h : ∑ i ∈ s, c i * (B : ℤ) ^ k i = 0) : ∀ i ∈ s, c i = 0 := by
  induction s using Finset.induction_on_min_value k with
  | empty => simp
  | insert a s has hmin ih =>
    have hlt : ∀ x ∈ s, k a < k x := by
      intro x hx
      refine lt_of_le_of_ne (hmin x hx) ?_
      intro heq
      exact has (by
        have := hk (by simp) (by simp [hx]) heq
        rw [this]; exact hx)
    rw [sum_insert has] at h
    have ha : c a = 0 := by
      have hdiv : ∑ x ∈ s, c x * (B : ℤ) ^ k x =
          (B : ℤ) ^ (k a + 1) * ∑ x ∈ s, c x * (B : ℤ) ^ (k x - k a - 1) := by
        rw [mul_sum]
        refine sum_congr rfl fun x hx => ?_
        have := hlt x hx
        have e : k x = (k a + 1) + (k x - k a - 1) := by omega
        conv_lhs => rw [e]
        rw [pow_add]; ring
      rw [hdiv] at h
      have hBa : (B : ℤ) ^ k a ≠ 0 := pow_ne_zero _ (by omega)
      have h2 : c a = -(B * ∑ x ∈ s, c x * (B : ℤ) ^ (k x - k a - 1)) := by
        have : (B : ℤ) ^ k a * (c a + B * ∑ x ∈ s, c x * (B : ℤ) ^ (k x - k a - 1)) = 0 := by
          rw [← h]; ring
        have := (mul_eq_zero.mp this).resolve_left hBa
        linarith
      have hd : (B : ℤ) ∣ c a := ⟨-(∑ x ∈ s, c x * (B : ℤ) ^ (k x - k a - 1)), by rw [h2]; ring⟩
      exact Int.eq_zero_of_abs_lt_dvd hd (hc a (mem_insert_self _ _))
    rw [ha, zero_mul, zero_add] at h
    intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · exact ha
    · exact ih (hk.mono (by simp)) (fun i hi => hc i (mem_insert_of_mem hi)) h i hi

/-- Mixed radix key. -/
def key {v : ℕ} (D : ℕ) (m : Fin v → ℕ) : ℕ := ∑ l : Fin v, m l * D ^ (l : ℕ)

theorem key_inj {v D : ℕ} (hD : 1 ≤ D) (m m' : Fin v → ℕ) (hm : ∀ l, m l < D) (hm' : ∀ l, m' l < D)
    (h : key D m = key D m') : m = m' := by
  induction v with
  | zero => funext l; exact l.elim0
  | succ v ih =>
    unfold key at h
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at h
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ] at h
    have e1 : ∀ m : Fin (v+1) → ℕ, ∑ i : Fin v, m i.succ * (D ^ (i : ℕ) * D) =
        (∑ i : Fin v, m i.succ * D ^ (i : ℕ)) * D := by
      intro m; rw [sum_mul]; exact sum_congr rfl fun i _ => by ring
    rw [e1, e1] at h
    have h0 : m 0 = m' 0 := by
      have := congrArg (· % D) h
      simp only [Nat.add_mul_mod_self_right] at this
      rwa [Nat.mod_eq_of_lt (hm 0), Nat.mod_eq_of_lt (hm' 0)] at this
    rw [h0] at h
    have h1 := Nat.add_left_cancel h
    have h2 : (∑ i : Fin v, m i.succ * D ^ (i : ℕ)) = ∑ i : Fin v, m' i.succ * D ^ (i : ℕ) :=
      Nat.eq_of_mul_eq_mul_right (by omega) h1
    have := ih (fun i => m i.succ) (fun i => m' i.succ) (fun i => hm _) (fun i => hm' _) h2
    funext l
    refine Fin.cases h0 (fun i => ?_) l
    exact congrFun this i


/-! ### The Kronecker homomorphism -/

abbrev MP (v : ℕ) := MvPolynomial (Fin v) Gi

/-- The `l`-th base-`D` digit of `k`. -/
def digit (D k l : ℕ) : ℕ := k / D ^ l % D

theorem sum_digit {v D : ℕ} (k : ℕ) (hk : k < D ^ v) :
    ∑ l : Fin v, digit D k l * D ^ (l : ℕ) = k := by
  have key : ∀ v, ∑ l : Fin v, digit D k l * D ^ (l : ℕ) = k % D ^ v := by
    intro v
    induction v with
    | zero => simp [Nat.mod_one]
    | succ v ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih, Nat.mod_pow_succ]
      unfold digit; ring
  rw [key, Nat.mod_eq_of_lt hk]

/-- The ring homomorphism sending the `l`-th variable to `2 ^ (b * D ^ l)`. -/
def psi {v : ℕ} (D b : ℕ) : MP v →+* Gi :=
  MvPolynomial.eval₂Hom (RingHom.id Gi) (fun l => (((2 : ℕ) ^ (b * D ^ (l : ℕ)) : ℕ) : Gi))

theorem prod_pow_two {v : ℕ} (D b : ℕ) (e : Fin v → ℕ) :
    ∏ i : Fin v, ((((2 : ℕ) ^ (b * D ^ (i : ℕ)) : ℕ) : Gi)) ^ e i
      = (((2 : ℕ) ^ (b * key D e) : ℕ) : Gi) := by
  have h1 : ∀ i : Fin v, ((((2 : ℕ) ^ (b * D ^ (i : ℕ)) : ℕ) : Gi)) ^ e i
      = (((2 : ℕ) ^ (b * D ^ (i : ℕ) * e i) : ℕ) : Gi) := by
    intro i; rw [← Nat.cast_pow, ← pow_mul]
  simp_rw [h1]
  rw [← Nat.cast_prod, Finset.prod_pow_eq_pow_sum]
  congr 2
  unfold key
  rw [mul_sum]
  exact sum_congr rfl fun i _ => by ring

theorem psi_eq {v : ℕ} (D b : ℕ) (h : MP v) :
    psi D b h = ∑ m ∈ h.support, h.coeff m *
      (((2 : ℕ) ^ (b * key D (fun l => m l)) : ℕ) : Gi) := by
  unfold psi
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq']
  exact sum_congr rfl fun m _ => by rw [RingHom.id_apply, prod_pow_two]

/-- The monomial whose exponent vector is the digit vector of `k`. -/
noncomputable def mon (D v k : ℕ) : MP v := ∏ l : Fin v, MvPolynomial.X l ^ digit D k l

theorem psi_mon {v : ℕ} (D b k : ℕ) (hk : k < D ^ v) :
    psi (v := v) D b (mon D v k) = (((2 : ℕ) ^ (b * k) : ℕ) : Gi) := by
  unfold mon
  rw [map_prod]
  simp_rw [map_pow]
  have : ∀ l : Fin v, psi (v := v) D b (MvPolynomial.X l) =
      (((2 : ℕ) ^ (b * D ^ (l : ℕ)) : ℕ) : Gi) := fun l => by simp [psi]
  simp_rw [this]
  rw [prod_pow_two]
  congr 3
  exact sum_digit k hk

/-! ### Norms and majorants -/

def nrmG (a : Gi) : ℕ := a.re.natAbs + a.im.natAbs

theorem nrmG_add (a b : Gi) : nrmG (a + b) ≤ nrmG a + nrmG b := by
  unfold nrmG; simp only [Gi.add_re, Gi.add_im]
  have := Int.natAbs_add_le a.re b.re
  have := Int.natAbs_add_le a.im b.im
  omega

theorem nrmG_mul (a b : Gi) : nrmG (a * b) ≤ nrmG a * nrmG b := by
  unfold nrmG; simp only [Gi.mul_re, Gi.mul_im]
  have h1 := Int.natAbs_sub_le (a.re * b.re) (a.im * b.im)
  have h2 := Int.natAbs_add_le (a.re * b.im) (a.im * b.re)
  simp only [Int.natAbs_mul] at h1 h2
  nlinarith [h1, h2]

theorem nrmG_neg (a : Gi) : nrmG (-a) = nrmG a := by
  unfold nrmG; simp


theorem nrmG_one : nrmG 1 = 1 := rfl

theorem nrmG_int (n : ℤ) : nrmG (n : Gi) = n.natAbs := by
  unfold nrmG; simp

/-- `L¹`-norm of a polynomial. -/
def nrm {v : ℕ} (p : MP v) : ℕ := ∑ m ∈ p.support, nrmG (p.coeff m)

theorem nrm_eq_of_subset {v : ℕ} (p : MP v) (s : Finset (Fin v →₀ ℕ)) (h : p.support ⊆ s) :
    nrm p = ∑ m ∈ s, nrmG (p.coeff m) := by
  unfold nrm
  refine sum_subset h fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.mp hm]; rfl

theorem nrm_coeff_le {v : ℕ} (p : MP v) (m : Fin v →₀ ℕ) : nrmG (p.coeff m) ≤ nrm p := by
  by_cases hm : m ∈ p.support
  · exact single_le_sum (f := fun m => nrmG (p.coeff m)) (fun _ _ => Nat.zero_le _) hm
  · rw [MvPolynomial.notMem_support_iff.mp hm]; exact Nat.zero_le _

theorem nrm_zero {v : ℕ} : nrm (0 : MP v) = 0 := by simp [nrm]

theorem nrm_add_le {v : ℕ} (p q : MP v) : nrm (p + q) ≤ nrm p + nrm q := by
  classical
  rw [nrm_eq_of_subset (p + q) (p.support ∪ q.support) MvPolynomial.support_add,
    nrm_eq_of_subset p (p.support ∪ q.support) subset_union_left,
    nrm_eq_of_subset q (p.support ∪ q.support) subset_union_right, ← sum_add_distrib]
  exact sum_le_sum fun m _ => by rw [MvPolynomial.coeff_add]; exact nrmG_add _ _

theorem nrm_neg {v : ℕ} (p : MP v) : nrm (-p) = nrm p := by
  unfold nrm
  rw [MvPolynomial.support_neg]
  exact sum_congr rfl fun m _ => by rw [MvPolynomial.coeff_neg, nrmG_neg]

theorem nrm_sum_le {v : ℕ} {ι : Type*} (s : Finset ι) (f : ι → MP v) :
    nrm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, nrm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nrm_zero]
  | insert a s has ih =>
    rw [sum_insert has, sum_insert has]
    exact (nrm_add_le _ _).trans (Nat.add_le_add_left ih _)

theorem nrm_monomial_le {v : ℕ} (m : Fin v →₀ ℕ) (a : Gi) :
    nrm (MvPolynomial.monomial m a) ≤ nrmG a := by
  classical
  unfold nrm
  by_cases ha : a = 0
  · simp [ha]
  · rw [MvPolynomial.support_monomial, if_neg ha]; simp

theorem nrm_mul_le {v : ℕ} (p q : MP v) : nrm (p * q) ≤ nrm p * nrm q := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p, MvPolynomial.as_sum q]
  rw [sum_mul_sum]
  refine (nrm_sum_le _ _).trans ?_
  unfold nrm
  rw [sum_mul_sum]
  refine sum_le_sum fun m _ => ?_
  refine (nrm_sum_le _ _).trans ?_
  refine sum_le_sum fun m' _ => ?_
  rw [MvPolynomial.monomial_mul]
  exact (nrm_monomial_le _ _).trans (nrmG_mul _ _)

theorem nrm_C_le {v : ℕ} (a : Gi) : nrm (MvPolynomial.C a : MP v) ≤ nrmG a := by
  rw [← MvPolynomial.monomial_zero']; exact nrm_monomial_le _ _

theorem nrm_X_le {v : ℕ} (l : Fin v) : nrm (MvPolynomial.X l : MP v) ≤ 1 := by
  rw [MvPolynomial.X, ]
  exact (nrm_monomial_le _ _).trans (le_of_eq nrmG_one)

/-- `p` has per-variable degrees `≤ d` and `L¹`-norm `≤ n`. -/
def Maj {v : ℕ} (d : Fin v → ℕ) (n : ℕ) (p : MP v) : Prop :=
  (∀ l, p.degreeOf l ≤ d l) ∧ nrm p ≤ n

namespace Maj
variable {v : ℕ} {d d' : Fin v → ℕ} {n n' : ℕ} {p q : MP v}

theorem mono (h : Maj d n p) (hd : ∀ l, d l ≤ d'' l) (hn : n ≤ n'') : Maj d'' n'' p :=
  ⟨fun l => (h.1 l).trans (hd l), h.2.trans hn⟩

theorem add (hp : Maj d n p) (hq : Maj d' n' q) :
    Maj (fun l => max (d l) (d' l)) (n + n') (p + q) :=
  ⟨fun l => (MvPolynomial.degreeOf_add_le l p q).trans (max_le_max (hp.1 l) (hq.1 l)),
    (nrm_add_le p q).trans (Nat.add_le_add hp.2 hq.2)⟩

theorem neg (hp : Maj d n p) : Maj d n (-p) :=
  ⟨fun l => by rw [MvPolynomial.degreeOf_neg]; exact hp.1 l, by rw [nrm_neg]; exact hp.2⟩

theorem sub (hp : Maj d n p) (hq : Maj d' n' q) :
    Maj (fun l => max (d l) (d' l)) (n + n') (p - q) := by
  rw [sub_eq_add_neg]; exact hp.add hq.neg

theorem mul (hp : Maj d n p) (hq : Maj d' n' q) :
    Maj (fun l => d l + d' l) (n * n') (p * q) :=
  ⟨fun l => (MvPolynomial.degreeOf_mul_le l p q).trans (Nat.add_le_add (hp.1 l) (hq.1 l)),
    (nrm_mul_le p q).trans (Nat.mul_le_mul hp.2 hq.2)⟩

theorem zero : Maj (fun _ : Fin v => 0) 0 (0 : MP v) :=
  ⟨fun l => by simp, by simp [nrm_zero]⟩

theorem one : Maj (fun _ : Fin v => 0) 1 (1 : MP v) :=
  ⟨fun l => by simp, by
    have := nrm_C_le (v := v) 1
    rw [MvPolynomial.C_1] at this; exact this.trans (le_of_eq nrmG_one)⟩

theorem C (a : Gi) : Maj (fun _ : Fin v => 0) (nrmG a) (MvPolynomial.C a : MP v) :=
  ⟨fun l => by simp [MvPolynomial.degreeOf_C], nrm_C_le a⟩

theorem X (l : Fin v) : Maj (fun l' => if l' = l then 1 else 0) 1 (MvPolynomial.X l : MP v) := by
  refine ⟨fun l' => ?_, nrm_X_le l⟩
  classical
  rw [MvPolynomial.degreeOf_X]

theorem sum {ι : Type*} (s : Finset ι) (f : ι → MP v) (d : ι → Fin v → ℕ) (n : ι → ℕ)
    (h : ∀ i ∈ s, Maj (d i) (n i) (f i)) :
    Maj (fun l => s.sup fun i => d i l) (∑ i ∈ s, n i) (∑ i ∈ s, f i) := by
  classical
  refine ⟨fun l => (MvPolynomial.degreeOf_sum_le l s f).trans
    (Finset.sup_mono_fun fun i hi => (h i hi).1 l), (nrm_sum_le s f).trans ?_⟩
  exact sum_le_sum fun i hi => (h i hi).2

theorem prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → MP v) (d : ι → Fin v → ℕ)
    (n : ι → ℕ) (h : ∀ i ∈ s, Maj (d i) (n i) (f i)) :
    Maj (fun l => ∑ i ∈ s, d i l) (∏ i ∈ s, n i) (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (one : Maj (fun _ : Fin v => 0) 1 (1 : MP v))
  | insert a s has ih =>
    rw [prod_insert has, prod_insert has]
    have := (h a (mem_insert_self _ _)).mul (ih fun i hi => h i (mem_insert_of_mem hi))
    refine this.mono (fun l => ?_) le_rfl
    rw [sum_insert has]

end Maj

/-! ### Injectivity of the Kronecker substitution -/

theorem psi_inj {v D b : ℕ} (hD : 1 ≤ D) (hb : 1 ≤ b) (h : MP v)
    (hdeg : ∀ l, h.degreeOf l < D) (hn : nrm h * 2 < 2 ^ b) (h0 : psi D b h = 0) : h = 0 := by
  classical
  rw [psi_eq] at h0
  have hdig : ∀ m ∈ h.support, ∀ l, m l < D := fun m hm l =>
    (MvPolynomial.degreeOf_lt_iff (by omega)).mp (hdeg l) m hm
  have hinj : Set.InjOn (fun m : Fin v →₀ ℕ => key D (fun l => m l)) h.support := by
    intro m hm m' hm' he
    have := key_inj hD _ _ (hdig m hm) (hdig m' hm') he
    exact Finsupp.ext fun l => congrFun this l
  have hB : 2 ≤ 2 ^ b := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb
  have hcoef : ∀ m, ((h.coeff m).re.natAbs : ℤ) < ((2 ^ b : ℕ) : ℤ) ∧
      ((h.coeff m).im.natAbs : ℤ) < ((2 ^ b : ℕ) : ℤ) := by
    intro m
    have := nrm_coeff_le h m
    unfold nrmG at this
    constructor <;> exact_mod_cast (by omega)
  have key : ∀ m ∈ h.support, (h.coeff m).re = 0 ∧ (h.coeff m).im = 0 := by
    have hre := congrArg Gi.re h0
    have him := congrArg Gi.im h0
    have e1 : ∀ m ∈ h.support, ((h.coeff m * (((2 : ℕ) ^ (b * key D fun l => m l) : ℕ) : Gi)).re
        = (h.coeff m).re * ((2 ^ b : ℕ) : ℤ) ^ (key D fun l => m l) ∧
        (h.coeff m * (((2 : ℕ) ^ (b * key D fun l => m l) : ℕ) : Gi)).im
        = (h.coeff m).im * ((2 ^ b : ℕ) : ℤ) ^ (key D fun l => m l)) := by
      intro m _
      simp only [Gi.mul_re, Gi.mul_im, Gi.natCast_re, Gi.natCast_im]
      push_cast
      rw [pow_mul]; simp
    have hs1 : ∑ m ∈ h.support, (h.coeff m).re * ((2 ^ b : ℕ) : ℤ) ^ (key D fun l => m l) = 0 := by
      have := map_sum Gi.reHom (fun m => h.coeff m * (((2 : ℕ) ^ (b * key D fun l => m l) : ℕ) : Gi))
        h.support
      simp only [Gi.reHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
      rw [this] at hre
      simp only [Gi.zero_re] at hre
      rw [← hre]
      exact sum_congr rfl fun m hm => (e1 m hm).1.symm
    have hs2 : ∑ m ∈ h.support, (h.coeff m).im * ((2 ^ b : ℕ) : ℤ) ^ (key D fun l => m l) = 0 := by
      have := map_sum Gi.imHom (fun m => h.coeff m * (((2 : ℕ) ^ (b * key D fun l => m l) : ℕ) : Gi))
        h.support
      simp only [Gi.imHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
      rw [this] at him
      simp only [Gi.zero_im] at him
      rw [← him]
      exact sum_congr rfl fun m hm => (e1 m hm).2.symm
    have z1 := digit_zero (fun m => (h.coeff m).re) (fun m => key D fun l => m l) (2 ^ b) hB
      h.support hinj (fun m _ => by
        have := (hcoef m).1; rwa [Int.abs_eq_natAbs]) hs1
    have z2 := digit_zero (fun m => (h.coeff m).im) (fun m => key D fun l => m l) (2 ^ b) hB
      h.support hinj (fun m _ => by
        have := (hcoef m).2; rwa [Int.abs_eq_natAbs]) hs2
    exact fun m hm => ⟨z1 m hm, z2 m hm⟩
  refine MvPolynomial.ext _ _ fun m => ?_
  by_cases hm : m ∈ h.support
  · have := key m hm
    simp only [MvPolynomial.coeff_zero]
    refine Gi.ext ?_ ?_ <;> simp [this.1, this.2]
  · simp [MvPolynomial.notMem_support_iff.mp hm]

/-! ### Big-natural packing -/

abbrev p2 (w : ℕ) : ℕ := Nat.pow 2 w

theorem p2_eq (w : ℕ) : p2 w = 2 ^ w := Nat.pow_eq

/-- The `j`-th field of width `w` of `X`. -/
def fieldAt (w X j : ℕ) : ℕ := X >>> (w * j) % p2 w

theorem fieldAt_eq (w X j : ℕ) : fieldAt w X j = X / 2 ^ (w * j) % 2 ^ w := by
  simp only [fieldAt, p2_eq, Nat.shiftRight_eq_div_pow]

theorem fieldAt_lt (w X j : ℕ) : fieldAt w X j < 2 ^ w := by
  rw [fieldAt_eq]; exact Nat.mod_lt _ (by positivity)

theorem pack_succ (w : ℕ) (d : ℕ → ℕ) (n : ℕ) :
    ∑ j ∈ range (n + 1), d j * 2 ^ (w * j) = d 0 + 2 ^ w * ∑ j ∈ range n, d (j + 1) * 2 ^ (w * j) := by
  rw [Finset.sum_range_succ' (fun j => d j * 2 ^ (w * j)) n]
  simp only [mul_zero, pow_zero, mul_one]
  rw [add_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_add, pow_add, mul_one]; ring

theorem fieldAt_zero (w X : ℕ) : fieldAt w X 0 = X % 2 ^ w := by
  rw [fieldAt_eq]; simp

theorem fieldAt_succ (w X k : ℕ) : fieldAt w X (k + 1) = fieldAt w (X / 2 ^ w) k := by
  rw [fieldAt_eq, fieldAt_eq, Nat.div_div_eq_div_mul, ← pow_add]
  congr 3; ring

/-- Digit extraction of a packed number. -/
theorem fieldAt_pack (w : ℕ) (n : ℕ) : ∀ (d : ℕ → ℕ), (∀ j, d j < 2 ^ w) → ∀ k, k < n →
    fieldAt w (∑ j ∈ range n, d j * 2 ^ (w * j)) k = d k := by
  induction n with
  | zero => intro d hd k hk; omega
  | succ n ih =>
    intro d hd k hk
    rw [pack_succ]
    have hdiv : (d 0 + 2 ^ w * ∑ j ∈ range n, d (j + 1) * 2 ^ (w * j)) / 2 ^ w =
        ∑ j ∈ range n, d (j + 1) * 2 ^ (w * j) := by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (hd 0), zero_add]
    cases k with
    | zero =>
      rw [fieldAt_zero, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hd 0)]
    | succ k =>
      rw [fieldAt_succ, hdiv]
      exact ih (fun j => d (j + 1)) (fun j => hd _) k (by omega)

/-! ### Positive semidefiniteness from a diagonally dominant congruence -/

theorem dd_quad {n : ℕ} (Δ : Fin n → Fin n → ℝ) (hsym : ∀ i j, Δ i j = Δ j i)
    (hdd : ∀ i, ∑ j, (if i = j then 0 else |Δ i j|) ≤ Δ i i) (u : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, u i * Δ i j * u j := by
  set A : Fin n → Fin n → ℝ := fun i j => if i = j then 0 else Δ i j with hA
  have hAs : ∀ i j, A i j = A j i := by
    intro i j; simp only [hA]; by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h, hsym i j]
  have hsplit : ∑ i, ∑ j, u i * Δ i j * u j = ∑ i, Δ i i * u i ^ 2 + ∑ i, ∑ j, u i * A i j * u j := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    have : ∀ j, u i * Δ i j * u j = (if i = j then Δ i i * u i ^ 2 else 0) + u i * A i j * u j := by
      intro j; simp only [hA]; by_cases h : i = j
      · subst h; simp; ring
      · simp [h]
    simp_rw [this]
    rw [sum_add_distrib, sum_ite_eq]; simp
  have hpair : ∀ i j, 0 ≤ 2 * (u i * A i j * u j) + |A i j| * (u i ^ 2 + u j ^ 2) := by
    intro i j
    rcases le_or_gt 0 (A i j) with h | h
    · rw [abs_of_nonneg h]; nlinarith [mul_nonneg h (sq_nonneg (u i + u j))]
    · rw [abs_of_neg h]; nlinarith [mul_nonneg (neg_nonneg.mpr h.le) (sq_nonneg (u i - u j))]
  have hsum : 0 ≤ ∑ i, ∑ j, (2 * (u i * A i j * u j) + |A i j| * (u i ^ 2 + u j ^ 2)) :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => hpair i j
  have e1 : ∑ i, ∑ j, (2 * (u i * A i j * u j) + |A i j| * (u i ^ 2 + u j ^ 2)) =
      2 * ∑ i, ∑ j, u i * A i j * u j + 2 * ∑ i, u i ^ 2 * ∑ j, |A i j| := by
    have h1 : ∑ i, ∑ j, |A i j| * u j ^ 2 = ∑ i, ∑ j, |A i j| * u i ^ 2 := by
      rw [sum_comm]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      rw [hAs j i]
    simp only [mul_add, sum_add_distrib, ← mul_sum]
    have h2 : ∑ i, ∑ j, |A i j| * u i ^ 2 = ∑ i, u i ^ 2 * ∑ j, |A i j| := by
      refine sum_congr rfl fun i _ => ?_
      rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
    rw [h1, h2]; ring
  have hle : ∑ i, u i ^ 2 * ∑ j, |A i j| ≤ ∑ i, Δ i i * u i ^ 2 := by
    refine sum_le_sum fun i _ => ?_
    have : ∑ j, |A i j| ≤ Δ i i := by
      refine le_trans (le_of_eq (sum_congr rfl fun j _ => ?_)) (hdd i)
      simp only [hA]; split_ifs <;> simp
    nlinarith [sq_nonneg (u i)]
  rw [hsplit]
  linarith

theorem psd_quad {n : ℕ} (Nf Cf : ℕ → ℕ → ℤ) (hsym : ∀ i j, Nf i j = Nf j i)
    (hlow : ∀ i j, i < j → Cf i j = 0) (hdiag : ∀ i < n, Cf i i ≠ 0)
    (hdd : ∀ i < n, ∑ j ∈ range n, (if i = j then 0 else |∑ k ∈ range n, ∑ l ∈ range n,
        Cf i k * Nf k l * Cf j l|) ≤ ∑ k ∈ range n, ∑ l ∈ range n, Cf i k * Nf k l * Cf i l)
    (w : ℕ → ℝ) : 0 ≤ ∑ i ∈ range n, ∑ j ∈ range n, (Nf i j : ℝ) * w i * w j := by
  classical
  let C : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (Cf i j : ℝ)
  let N : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (Nf i j : ℝ)
  have hCdet : C.det ≠ 0 := by
    have : C.BlockTriangular OrderDual.toDual := by
      intro i j hij
      simp only [Matrix.of_apply, C]
      have : (i : ℕ) < j := hij
      exact_mod_cast hlow i j this
    rw [Matrix.det_of_lowerTriangular C this]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by
      simp only [Matrix.of_apply, C]; exact_mod_cast hdiag i i.2
  have hCT : IsUnit Cᵀ.det := by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hCdet
  set wv : Fin n → ℝ := fun i => w i with hwv
  obtain ⟨u, hu⟩ : ∃ u, Cᵀ.mulVec u = wv := ⟨(Cᵀ)⁻¹.mulVec wv, by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hCT, Matrix.one_mulVec]⟩
  set Δ : Matrix (Fin n) (Fin n) ℝ := C * N * Cᵀ with hΔ
  have hΔe : ∀ i j : Fin n, Δ i j =
      ((∑ k ∈ range n, ∑ l ∈ range n, Cf i k * Nf k l * Cf j l : ℤ) : ℝ) := by
    intro i j
    have e1 : ∀ k : ℕ, ((∑ l ∈ range n, Cf i k * Nf k l * Cf j l : ℤ) : ℝ)
        = ∑ l : Fin n, (Cf i k : ℝ) * Nf k l * Cf j l := by
      intro k; push_cast
      exact (Fin.sum_univ_eq_sum_range (fun l => (Cf i k : ℝ) * Nf k l * Cf j l) n).symm
    push_cast
    simp only [hΔ, C, N, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    rw [← Fin.sum_univ_eq_sum_range (fun k => ∑ l ∈ range n, (Cf i k : ℝ) * Nf k l * Cf j l) n]
    simp only [← Fin.sum_univ_eq_sum_range (fun l => (Cf i _ : ℝ) * Nf _ l * Cf j l) n]
    simp only [Finset.sum_mul]
    rw [sum_comm]
  have hq : ∑ i ∈ range n, ∑ j ∈ range n, (Nf i j : ℝ) * w i * w j = ∑ i, ∑ j, u i * Δ i j * u j := by
    have h1 : ∑ i ∈ range n, ∑ j ∈ range n, (Nf i j : ℝ) * w i * w j = wv ⬝ᵥ N.mulVec wv := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range n, (Nf i j : ℝ) * w i * w j) n]
      simp only [dotProduct, Matrix.mulVec, N, Matrix.of_apply, hwv, Finset.mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [← Fin.sum_univ_eq_sum_range (fun j => (Nf i j : ℝ) * w i * w j) n]
      refine sum_congr rfl fun j _ => ?_
      ring
    have h2 : (Δ.mulVec u) ⬝ᵥ u = wv ⬝ᵥ N.mulVec wv := by
      have e1 : Δ.mulVec u = C.mulVec (N.mulVec wv) := by
        rw [hΔ, ← hu, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      rw [e1, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hu]
    have h3 : (Δ.mulVec u) ⬝ᵥ u = ∑ i, ∑ j, u i * Δ i j * u j := by
      simp only [dotProduct, Matrix.mulVec, Finset.sum_mul]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      ring
    rw [h1, ← h2, h3]
  rw [hq]
  have hsymm : ∀ i j, Δ i j = Δ j i := by
    intro i j
    have hNT : Nᵀ = N := by
      ext a b; simp only [N, Matrix.transpose_apply, Matrix.of_apply]; exact_mod_cast hsym _ _
    have : Δᵀ = Δ := by
      rw [hΔ, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hNT,
        Matrix.mul_assoc]
    have h := congrFun (congrFun this i) j
    rw [Matrix.transpose_apply] at h
    exact h.symm
  refine dd_quad (fun i j => Δ i j) hsymm ?_ u
  intro i
  have := hdd i i.2
  rw [← Fin.sum_univ_eq_sum_range (fun j => if (i:ℕ) = j then (0:ℤ) else |∑ k ∈ range n, ∑ l ∈ range n,
    Cf i k * Nf k l * Cf j l|) n] at this
  have h' : ((∑ j : Fin n, if (i:ℕ) = j then (0:ℤ) else |∑ k ∈ range n, ∑ l ∈ range n,
    Cf i k * Nf k l * Cf j l| : ℤ) : ℝ) ≤ ((∑ k ∈ range n, ∑ l ∈ range n, Cf i k * Nf k l * Cf i l : ℤ) : ℝ) := by
    exact_mod_cast this
  rw [← hΔe i i] at h'
  refine le_trans (le_of_eq ?_) h'
  push_cast
  refine sum_congr rfl fun j _ => ?_
  rw [hΔe i j]
  by_cases h : i = j
  · simp [h]
  · have : (i : ℕ) ≠ j := fun h' => h (Fin.ext h')
    simp [h, this]

/-! ### Gram blocks: data and the packed positivity check -/

structure Blk where
  n : ℕ
  mu : ℕ
  wN : ℕ
  wC : ℕ
  Nl : List ℕ
  Cl : List ℕ
  tm : List ℕ
deriving Inhabited

def mapI (f : ℕ → ℕ → ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | i, a :: as => f i a :: mapI f (i + 1) as

theorem mapI_range (g : ℕ → ℕ → ℕ) (f : ℕ → ℕ) (m : ℕ) : ∀ s,
    mapI g s ((List.range m).map f) = (List.range m).map (fun i => g (s + i) (f i)) := by
  induction m generalizing f with
  | zero => intro s; simp [mapI]
  | succ m ih =>
    intro s
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, mapI, ih (f ∘ Nat.succ) (s + 1),
      List.map_cons, List.map_map]
    simp only [Function.comp_def, add_zero, Nat.succ_eq_add_one]
    congr 2
    funext i; congr 1; omega

/-- Symmetric completion of the lower triangular packed rows. -/
def buildAux (w : ℕ) : ℕ → List ℕ → List ℕ → List ℕ
  | _, acc, [] => acc
  | r, acc, l :: ls =>
    buildAux w (r + 1) (mapI (fun i a => a + (fieldAt w l i <<< (w * r))) 0 acc ++ [l % p2 (w * (r + 1))]) ls

def buildFull (w : ℕ) (ls : List ℕ) : List ℕ := buildAux w 0 [] ls

/-- The symmetric field matrix of the lower triangular packed rows `L`. -/
def gN (w : ℕ) (L : List ℕ) (i j : ℕ) : ℕ := fieldAt w (L.getD (max i j) 0) (min i j)

/-- Packed full rows. -/
def FF (w : ℕ) (L : List ℕ) : List ℕ :=
  (List.range L.length).map (fun i => ∑ j ∈ range L.length, gN w L i j * 2 ^ (w * j))

theorem pack_fields (w : ℕ) : ∀ (n X : ℕ), ∑ j ∈ range n, fieldAt w X j * 2 ^ (w * j) = X % 2 ^ (w * n) := by
  intro n
  induction n with
  | zero => intro X; simp [Nat.mod_one]
  | succ n ih =>
    intro X
    rw [pack_succ, fieldAt_zero]
    have : ∀ j, fieldAt w X (j + 1) = fieldAt w (X / 2 ^ w) j := fun j => fieldAt_succ w X j
    simp only [this]
    have e : 2 ^ (w * (n + 1)) = 2 ^ w * 2 ^ (w * n) := by rw [← pow_add]; congr 1; ring
    rw [ih, e, Nat.mod_mul]

theorem getD_append_left (l l' : List ℕ) (n : ℕ) (h : n < l.length) :
    (l ++ l').getD n 0 = l.getD n 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right (l l' : List ℕ) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').getD n 0 = l'.getD (n - l.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem buildAux_eq (w : ℕ) (ls : List ℕ) : ∀ pre : List ℕ,
    buildAux w pre.length (FF w pre) ls = FF w (pre ++ ls) := by
  induction ls with
  | nil => intro pre; simp [buildAux]
  | cons l ls ih =>
    intro pre
    rw [buildAux]
    have hstep : mapI (fun i a => a + (fieldAt w l i <<< (w * pre.length))) 0 (FF w pre) ++
        [l % p2 (w * (pre.length + 1))] = FF w (pre ++ [l]) := by
      set r := pre.length with hr
      have hlen : (pre ++ [l]).length = r + 1 := by simp [hr]
      unfold FF
      rw [hlen, List.range_succ, List.map_append, ← hr]
      have e1 : mapI (fun i a => a + (fieldAt w l i <<< (w * r))) 0
          ((List.range r).map (fun i => ∑ j ∈ range r, gN w pre i j * 2 ^ (w * j))) =
          (List.range r).map (fun i => ∑ j ∈ range (r + 1), gN w (pre ++ [l]) i j * 2 ^ (w * j)) := by
        rw [mapI_range]
        refine List.map_congr_left fun i hi => ?_
        have hi' : i < r := List.mem_range.mp hi
        rw [sum_range_succ, zero_add, Nat.shiftLeft_eq]
        congr 1
        · refine sum_congr rfl fun j hj => ?_
          have hj' : j < r := mem_range.mp hj
          unfold gN
          rw [getD_append_left _ _ _ (by omega)]
        · unfold gN
          have h1 : max i r = r := by omega
          have h2 : min i r = i := by omega
          rw [h1, h2, getD_append_right _ _ _ (by simp [hr])]
          simp [hr, mul_comm]
      rw [hlen] at *
      rw [e1]
      congr 1
      simp only [List.map_cons, List.map_nil]
      congr 1
      rw [p2_eq, ← pack_fields]
      refine sum_congr rfl fun j hj => ?_
      have hj' : j < r + 1 := mem_range.mp hj
      unfold gN
      have : max r j = r := by omega
      have h2 : min r j = j := by omega
      rw [this, h2, getD_append_right _ _ _ (by simp [hr])]
      simp [hr]
    have hlen : (pre ++ [l]).length = pre.length + 1 := by simp
    rw [hstep, ← hlen, ih (pre ++ [l]), List.append_assoc]
    rfl

theorem buildFull_eq (w : ℕ) (L : List ℕ) : buildFull w L = FF w L := by
  have := buildAux_eq w L []
  simpa [FF, buildFull] using this

/-- Streaming dot product of the fields of `X` with the list `hs`. -/
def dotF (w : ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | X, h :: hs => (X % p2 w) * h + dotF w (X >>> w) hs

theorem dotF_eq (w m : ℕ) (h : ℕ → ℕ) : ∀ X : ℕ,
    dotF w X ((List.range m).map h) = ∑ j ∈ range m, fieldAt w X j * h j := by
  induction m generalizing h with
  | zero => intro X; simp [dotF]
  | succ m ih =>
    intro X
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, dotF, ih, sum_range_succ',
      fieldAt_zero, p2_eq, add_comm]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [fieldAt_succ, Nat.shiftRight_eq_div_pow]
    rfl

/-- Column `k` of the (lower triangular) rows, Horner packed with digit width `wd`. -/
def colPack (wC wd k : ℕ) : List ℕ → ℕ
  | [] => 0
  | r :: rs => fieldAt wC r k + (colPack wC wd k rs) <<< wd

theorem colPack_eq (wC wd k : ℕ) (L : List ℕ) :
    colPack wC wd k L = ∑ j ∈ range L.length, fieldAt wC (L.getD j 0) k * 2 ^ (wd * j) := by
  induction L with
  | nil => simp [colPack]
  | cons r rs ih =>
    rw [colPack, ih, List.length_cons, pack_succ wd (fun j => fieldAt wC ((r :: rs).getD j 0) k)]
    simp [Nat.shiftLeft_eq, mul_comm]

/-- `∑_{j<m} 2^(wd j)` -/
def ones (wd m : ℕ) : ℕ := (p2 (wd * m) - 1) / (p2 wd - 1)

theorem ones_eq (wd m : ℕ) (hwd : 1 ≤ wd) : ones wd m = ∑ j ∈ range m, 2 ^ (wd * j) := by
  unfold ones
  have h2 : 2 ≤ 2 ^ wd := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ wd := Nat.pow_le_pow_right (by omega) hwd
  have := Nat.geomSum_eq h2 m
  simp only [p2_eq]
  rw [← pow_mul] at this
  rw [← this]
  exact sum_congr rfl fun j _ => by rw [pow_mul]

/-- Streaming digits. -/
def digitsN (wd : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, X => (X % p2 wd) :: digitsN wd n (X >>> wd)

theorem digitsN_eq (wd n : ℕ) : ∀ X, digitsN wd n X = (List.range n).map (fun j => fieldAt wd X j) := by
  induction n with
  | zero => intro X; simp [digitsN]
  | succ n ih =>
    intro X
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, digitsN, ih, fieldAt_zero, p2_eq]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply]
    rw [fieldAt_succ, Nat.shiftRight_eq_div_pow]

theorem take_map_range (f : ℕ → ℕ) (m n : ℕ) (h : m ≤ n) :
    ((List.range n).map f).take m = (List.range m).map f := by
  rw [← List.map_take]; congr 1
  rw [List.take_range]; simp [h]

/-- offset of the `N` fields. -/
def Blk.oN (blk : Blk) : ℕ := 2 ^ (blk.wN - 1)
def Blk.oC (blk : Blk) : ℕ := 2 ^ (blk.wC - 1)

/-- The (symmetric) Gram numerators. -/
def Blk.Nz (blk : Blk) (i j : ℕ) : ℤ := (gN blk.wN blk.Nl i j : ℤ) - blk.oN

/-- The lower triangular integer congruence. -/
def Blk.Cz (blk : Blk) (i j : ℕ) : ℤ :=
  if j ≤ i then (fieldAt blk.wC (blk.Cl.getD i 0) j : ℤ) - blk.oC else 0

theorem gN_symm (w : ℕ) (L : List ℕ) (i j : ℕ) : gN w L i j = gN w L j i := by
  unfold gN; rw [max_comm, min_comm]

theorem Blk.N_symm (blk : Blk) (i j : ℕ) : blk.Nz i j = blk.Nz j i := by
  unfold Blk.Nz; rw [gN_symm]

theorem Blk.C_low (blk : Blk) (i j : ℕ) (h : i < j) : blk.Cz i j = 0 := by
  unfold Blk.Cz; simp [not_le.mpr h]

theorem two_pow_eq (w : ℕ) (hw : 1 ≤ w) : 2 ^ w = 2 * 2 ^ (w - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  simp [pow_succ]; ring

theorem fieldAt_sub_bound (w X j : ℕ) (hw : 1 ≤ w) : |(fieldAt w X j : ℤ) - (2 ^ (w - 1) : ℕ)| ≤ (2 ^ (w - 1) : ℕ) := by
  have h := fieldAt_lt w X j
  rw [two_pow_eq w hw] at h
  generalize 2 ^ (w - 1) = c at h ⊢
  rw [abs_le]
  constructor <;> omega

theorem Blk.N_bound (blk : Blk) (hN : 1 ≤ blk.wN) (i j : ℕ) : |blk.Nz i j| ≤ blk.oN := by
  unfold Blk.Nz gN Blk.oN; exact_mod_cast fieldAt_sub_bound _ _ _ hN

theorem Blk.C_bound (blk : Blk) (hC : 1 ≤ blk.wC) (i j : ℕ) : |blk.Cz i j| ≤ blk.oC := by
  unfold Blk.Cz Blk.oC; split_ifs
  · exact_mod_cast fieldAt_sub_bound _ _ _ hC
  · simp

/-- The congruence `C N Cᵀ`. -/
def Blk.Δ (blk : Blk) (i j : ℕ) : ℤ :=
  ∑ k ∈ range blk.n, ∑ l ∈ range blk.n, blk.Cz i k * blk.Nz k l * blk.Cz j l

theorem Blk.Δ_bound (blk : Blk) (hN : 1 ≤ blk.wN) (hC : 1 ≤ blk.wC) (i j : ℕ) :
    |blk.Δ i j| ≤ ((blk.n * blk.n * (blk.oC * blk.oN * blk.oC) : ℕ) : ℤ) := by
  unfold Blk.Δ
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ k ∈ range blk.n, |∑ l ∈ range blk.n, blk.Cz i k * blk.Nz k l * blk.Cz j l|
      ≤ (blk.n : ℤ) * ((blk.oC * blk.oN * blk.oC : ℕ) : ℤ) := by
    intro k _
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_card_nsmul _ _ ((blk.oC * blk.oN * blk.oC : ℕ) : ℤ) ?_).trans ?_
    · intro l _
      rw [abs_mul, abs_mul]
      have h1 := blk.C_bound hC i k
      have h2 := blk.N_bound hN k l
      have h3 := blk.C_bound hC j l
      push_cast
      gcongr
    · simp
  refine (sum_le_card_nsmul _ _ _ this).trans ?_
  simp only [card_range, nsmul_eq_mul]
  push_cast
  exact le_of_eq (by ring)

/-! #### Residues -/

theorem zmod_negmod (M : ℕ) (hM : 0 < M) (a t : ℕ) :
    (((a + (M - t % M)) % M : ℕ) : ZMod M) = (a : ZMod M) - (t : ZMod M) := by
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (Nat.mod_lt t hM).le, ZMod.natCast_self,
    ZMod.natCast_mod]
  ring

def Blk.rcol (blk : Blk) (wd k : ℕ) : ℕ :=
  (colPack blk.wC wd k (blk.Cl.drop k) <<< (wd * k) +
    (p2 (wd * blk.n) - ((p2 (blk.wC - 1) * ones wd (blk.n - k)) <<< (wd * k)) % p2 (wd * blk.n))) %
      p2 (wd * blk.n)

theorem getD_drop (L : List ℕ) (k j : ℕ) : (L.drop k).getD j 0 = L.getD (k + j) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem Blk.rcol_int (blk : Blk) (wd k : ℕ) (hwd : 1 ≤ wd) (hn : blk.Cl.length = blk.n) (hk : k < blk.n) :
    ((colPack blk.wC wd k (blk.Cl.drop k) <<< (wd * k) : ℕ) : ℤ) -
      (((p2 (blk.wC - 1) * ones wd (blk.n - k)) <<< (wd * k) : ℕ) : ℤ) =
    ∑ j ∈ range blk.n, blk.Cz j k * (2 : ℤ) ^ (wd * j) := by
  obtain ⟨m, hm⟩ : ∃ m, blk.n = k + m := ⟨blk.n - k, by omega⟩
  have hlen : (blk.Cl.drop k).length = m := by simp [hn, hm]
  rw [colPack_eq, hlen, ones_eq wd _ hwd, show blk.n - k = m by omega, Nat.shiftLeft_eq,
    Nat.shiftLeft_eq, hm, Finset.sum_range_add]
  have h0 : ∑ j ∈ range k, blk.Cz j k * (2 : ℤ) ^ (wd * j) = 0 :=
    sum_eq_zero fun j hj => by rw [blk.C_low j k (mem_range.mp hj), zero_mul]
  rw [h0, zero_add]
  push_cast
  rw [mul_sum, sum_mul, sum_mul, ← sum_sub_distrib]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j < m := mem_range.mp hj
  rw [getD_drop, p2_eq]
  unfold Blk.Cz
  rw [if_pos (by omega)]
  push_cast
  rw [mul_add wd k j, pow_add]
  simp only [Blk.oC]; push_cast
  ring

theorem Blk.rcol_zmod (blk : Blk) (wd k : ℕ) (hwd : 1 ≤ wd) (hn : blk.Cl.length = blk.n)
    (hk : k < blk.n) :
    ((blk.rcol wd k : ℕ) : ZMod (2 ^ (wd * blk.n))) =
      ((∑ j ∈ range blk.n, blk.Cz j k * (2 : ℤ) ^ (wd * j) : ℤ) : ZMod (2 ^ (wd * blk.n))) := by
  unfold Blk.rcol
  rw [p2_eq, zmod_negmod _ (by positivity)]
  have := congrArg (Int.cast : ℤ → ZMod (2 ^ (wd * blk.n))) (blk.rcol_int wd k hwd hn hk)
  simp only [Int.cast_sub, Int.cast_natCast] at this
  rw [p2_eq] at this
  exact this

theorem list_range_sum' {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

def Blk.rcols (blk : Blk) (wd : ℕ) : List ℕ := (List.range blk.n).map (blk.rcol wd)

def Blk.zres (blk : Blk) (wd X : ℕ) : ℕ :=
  (dotF blk.wN X (blk.rcols wd) +
    (p2 (wd * blk.n) - (p2 (blk.wN - 1) * (blk.rcols wd).sum) % p2 (wd * blk.n))) % p2 (wd * blk.n)

def Blk.zs (blk : Blk) (wd : ℕ) : List ℕ := (buildFull blk.wN blk.Nl).map (blk.zres wd)

/-- the packed row `i` of the full symmetric `N` -/
def Blk.Nrow (blk : Blk) (i : ℕ) : ℕ := ∑ j ∈ range blk.n, gN blk.wN blk.Nl i j * 2 ^ (blk.wN * j)

theorem Blk.zs_eq (blk : Blk) (wd : ℕ) (hn : blk.Nl.length = blk.n) :
    blk.zs wd = (List.range blk.n).map (fun i => blk.zres wd (blk.Nrow i)) := by
  unfold Blk.zs
  rw [buildFull_eq, FF, hn, List.map_map]
  rfl

theorem Blk.zres_zmod (blk : Blk) (wd : ℕ) (hwd : 1 ≤ wd) (hnC : blk.Cl.length = blk.n)
    (i : ℕ) :
    ((blk.zres wd (blk.Nrow i) : ℕ) : ZMod (2 ^ (wd * blk.n))) =
      ((∑ j ∈ range blk.n, (∑ l ∈ range blk.n, blk.Nz i l * blk.Cz j l) * (2 : ℤ) ^ (wd * j) : ℤ) :
        ZMod (2 ^ (wd * blk.n))) := by
  unfold Blk.zres
  rw [p2_eq, zmod_negmod _ (by positivity)]
  have hd : dotF blk.wN (blk.Nrow i) (blk.rcols wd) = ∑ l ∈ range blk.n, gN blk.wN blk.Nl i l * blk.rcol wd l := by
    unfold Blk.rcols
    rw [dotF_eq]
    refine sum_congr rfl fun l hl => ?_
    rw [Blk.Nrow, fieldAt_pack _ _ (fun j => gN blk.wN blk.Nl i j) (fun j => fieldAt_lt _ _ _) l (mem_range.mp hl)]
  rw [hd]
  have hsum : (blk.rcols wd).sum = ∑ l ∈ range blk.n, blk.rcol wd l := by
    unfold Blk.rcols
    rw [list_range_sum']
  rw [hsum]
  have hR : ∀ l ∈ range blk.n, ((blk.rcol wd l : ℕ) : ZMod (2 ^ (wd * blk.n))) =
      ((∑ j ∈ range blk.n, blk.Cz j l * (2 : ℤ) ^ (wd * j) : ℤ) : ZMod (2 ^ (wd * blk.n))) :=
    fun l hl => blk.rcol_zmod wd l hwd hnC (mem_range.mp hl)
  have key : (∑ l ∈ range blk.n, (gN blk.wN blk.Nl i l : ℤ) * ∑ j ∈ range blk.n, blk.Cz j l * (2 : ℤ) ^ (wd * j)) -
      (blk.oN : ℤ) * ∑ l ∈ range blk.n, ∑ j ∈ range blk.n, blk.Cz j l * (2 : ℤ) ^ (wd * j) =
      ∑ j ∈ range blk.n, (∑ l ∈ range blk.n, blk.Nz i l * blk.Cz j l) * (2 : ℤ) ^ (wd * j) := by
    calc _ = ∑ l ∈ range blk.n, ((gN blk.wN blk.Nl i l : ℤ) - blk.oN) *
            ∑ j ∈ range blk.n, blk.Cz j l * (2 : ℤ) ^ (wd * j) := by
          rw [mul_sum, ← sum_sub_distrib]
          exact sum_congr rfl fun l _ => by ring
      _ = ∑ l ∈ range blk.n, ∑ j ∈ range blk.n, blk.Nz i l * blk.Cz j l * (2 : ℤ) ^ (wd * j) := by
          refine sum_congr rfl fun l _ => ?_
          rw [mul_sum]
          exact sum_congr rfl fun j _ => by unfold Blk.Nz; ring
      _ = _ := by
          rw [sum_comm]
          exact sum_congr rfl fun j _ => by rw [sum_mul]
  have e1 : ∑ l ∈ range blk.n, (gN blk.wN blk.Nl i l : ZMod (2 ^ (wd * blk.n))) *
        ((blk.rcol wd l : ℕ) : ZMod (2 ^ (wd * blk.n))) =
      ∑ l ∈ range blk.n, (gN blk.wN blk.Nl i l : ZMod (2 ^ (wd * blk.n))) *
        ((∑ j ∈ range blk.n, blk.Cz j l * (2 : ℤ) ^ (wd * j) : ℤ) : ZMod (2 ^ (wd * blk.n))) :=
    sum_congr rfl fun l hl => by rw [hR l hl]
  have e2 : ∑ l ∈ range blk.n, ((blk.rcol wd l : ℕ) : ZMod (2 ^ (wd * blk.n))) =
      ∑ l ∈ range blk.n, ((∑ j ∈ range blk.n, blk.Cz j l * (2 : ℤ) ^ (wd * j) : ℤ) : ZMod (2 ^ (wd * blk.n))) :=
    sum_congr rfl hR
  have := congrArg (Int.cast : ℤ → ZMod (2 ^ (wd * blk.n))) key
  push_cast at this ⊢
  rw [e1, e2]
  simp only [Blk.oN, p2_eq] at this ⊢
  push_cast at this ⊢
  linear_combination this


def Blk.xrow (blk : Blk) (wd i : ℕ) : ℕ :=
  (dotF blk.wC (blk.Cl.getD i 0) ((blk.zs wd).take (i + 1)) + p2 (wd - 1) * ones wd blk.n +
    (p2 (wd * blk.n) - (p2 (blk.wC - 1) * ((blk.zs wd).take (i + 1)).sum) % p2 (wd * blk.n))) %
      p2 (wd * blk.n)

/-- the packed row `i` of `C N Cᵀ`, offset to make all digits nonnegative -/
def Blk.Tint (blk : Blk) (wd i : ℕ) : ℤ :=
  ∑ j ∈ range blk.n, (blk.Δ i j + ((2 ^ (wd - 1) : ℕ) : ℤ)) * (2 : ℤ) ^ (wd * j)

theorem Blk.xrow_gen (blk : Blk) (Z : ℕ → ℤ) (i : ℕ) (hi : i < blk.n) :
    (∑ k ∈ range (i + 1), (fieldAt blk.wC (blk.Cl.getD i 0) k : ℤ) * Z k) -
      (blk.oC : ℤ) * ∑ k ∈ range (i + 1), Z k = ∑ k ∈ range blk.n, blk.Cz i k * Z k := by
  obtain ⟨m, hm⟩ : ∃ m, blk.n = (i + 1) + m := ⟨blk.n - (i + 1), by omega⟩
  rw [mul_sum, ← sum_sub_distrib]
  conv_rhs => rw [hm, Finset.sum_range_add]
  have h0 : ∑ k ∈ range m, blk.Cz i (i + 1 + k) * Z (i + 1 + k) = 0 :=
    sum_eq_zero fun k _ => by rw [blk.C_low i _ (by omega), zero_mul]
  rw [h0, add_zero]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k < i + 1 := mem_range.mp hk
  unfold Blk.Cz; rw [if_pos (by omega)]; ring

theorem Blk.Δ_sum (blk : Blk) (wd i : ℕ) :
    ∑ k ∈ range blk.n, blk.Cz i k *
      ∑ j ∈ range blk.n, (∑ l ∈ range blk.n, blk.Nz k l * blk.Cz j l) * (2 : ℤ) ^ (wd * j) =
    ∑ j ∈ range blk.n, blk.Δ i j * (2 : ℤ) ^ (wd * j) := by
  unfold Blk.Δ
  simp only [mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  refine sum_congr rfl fun k _ => ?_
  refine sum_congr rfl fun l _ => ?_
  ring

theorem Blk.xrow_int (blk : Blk) (wd : ℕ) (i : ℕ) (hi : i < blk.n) :
    (∑ k ∈ range (i + 1), (fieldAt blk.wC (blk.Cl.getD i 0) k : ℤ) *
        ∑ j ∈ range blk.n, (∑ l ∈ range blk.n, blk.Nz k l * blk.Cz j l) * (2 : ℤ) ^ (wd * j)) +
      ((2 ^ (wd - 1) : ℕ) : ℤ) * ∑ j ∈ range blk.n, (2 : ℤ) ^ (wd * j) -
      (blk.oC : ℤ) * ∑ k ∈ range (i + 1),
        ∑ j ∈ range blk.n, (∑ l ∈ range blk.n, blk.Nz k l * blk.Cz j l) * (2 : ℤ) ^ (wd * j) =
    blk.Tint wd i := by
  have h := blk.xrow_gen (fun k => ∑ j ∈ range blk.n, (∑ l ∈ range blk.n, blk.Nz k l * blk.Cz j l) *
    (2 : ℤ) ^ (wd * j)) i hi
  rw [blk.Δ_sum] at h
  unfold Blk.Tint
  simp only [add_mul, sum_add_distrib]
  rw [← mul_sum]
  linarith

theorem Blk.xrow_zmod (blk : Blk) (wd : ℕ) (hwd : 1 ≤ wd) (hnC : blk.Cl.length = blk.n)
    (hnN : blk.Nl.length = blk.n) (i : ℕ) (hi : i < blk.n) :
    ((blk.xrow wd i : ℕ) : ZMod (2 ^ (wd * blk.n))) = ((blk.Tint wd i : ℤ) : ZMod (2 ^ (wd * blk.n))) := by
  unfold Blk.xrow
  simp only [p2_eq]
  rw [zmod_negmod _ (by positivity), blk.zs_eq wd hnN, take_map_range _ _ _ (by omega)]
  rw [dotF_eq, list_range_sum', ones_eq wd _ hwd]
  have hz : ∀ k ∈ range (i + 1), ((blk.zres wd (blk.Nrow k) : ℕ) : ZMod (2 ^ (wd * blk.n))) =
      ((∑ j ∈ range blk.n, (∑ l ∈ range blk.n, blk.Nz k l * blk.Cz j l) * (2 : ℤ) ^ (wd * j) : ℤ) :
        ZMod (2 ^ (wd * blk.n))) := fun k _ => blk.zres_zmod wd hwd hnC k
  have e1 : ∑ k ∈ range (i + 1), ((fieldAt blk.wC (blk.Cl.getD i 0) k : ℕ) : ZMod (2 ^ (wd * blk.n))) *
        ((blk.zres wd (blk.Nrow k) : ℕ) : ZMod (2 ^ (wd * blk.n))) =
      ∑ k ∈ range (i + 1), ((fieldAt blk.wC (blk.Cl.getD i 0) k : ℕ) : ZMod (2 ^ (wd * blk.n))) *
        ((∑ j ∈ range blk.n, (∑ l ∈ range blk.n, blk.Nz k l * blk.Cz j l) * (2 : ℤ) ^ (wd * j) : ℤ) :
          ZMod (2 ^ (wd * blk.n))) :=
    sum_congr rfl fun k hk => by rw [hz k hk]
  have e2 : ∑ k ∈ range (i + 1), ((blk.zres wd (blk.Nrow k) : ℕ) : ZMod (2 ^ (wd * blk.n))) =
      ∑ k ∈ range (i + 1), ((∑ j ∈ range blk.n, (∑ l ∈ range blk.n, blk.Nz k l * blk.Cz j l) *
        (2 : ℤ) ^ (wd * j) : ℤ) : ZMod (2 ^ (wd * blk.n))) := sum_congr rfl hz
  have := congrArg (Int.cast : ℤ → ZMod (2 ^ (wd * blk.n))) (blk.xrow_int wd i hi)
  push_cast at this ⊢
  rw [e1, e2]
  simp only [Blk.oC] at this ⊢
  push_cast at this ⊢
  linear_combination this

theorem sum_digits_lt (B : ℤ) (hB : 1 ≤ B) (d : ℕ → ℤ) (n : ℕ) (hd : ∀ j < n, 0 ≤ d j ∧ d j < B) :
    0 ≤ ∑ j ∈ range n, d j * B ^ j ∧ ∑ j ∈ range n, d j * B ^ j < B ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih fun j hj => hd j (by omega)
    have hdn := hd n (by omega)
    rw [sum_range_succ, pow_succ]
    have hp : 0 < B ^ n := by positivity
    constructor
    · have := mul_nonneg hdn.1 hp.le
      linarith [ih'.1]
    · nlinarith [ih'.2, hdn.2, hp]

theorem Blk.xrow_eq (blk : Blk) (wd : ℕ) (hwd : 1 ≤ wd) (hnC : blk.Cl.length = blk.n)
    (hnN : blk.Nl.length = blk.n) (hbd : ∀ i j, |blk.Δ i j| < ((2 ^ (wd - 1) : ℕ) : ℤ))
    (i : ℕ) (hi : i < blk.n) : (blk.xrow wd i : ℤ) = blk.Tint wd i := by
  have h2 := two_pow_eq wd hwd
  have hB : (1 : ℤ) ≤ 2 ^ wd := one_le_pow₀ (by norm_num)
  have h2z : (2 : ℤ) ^ wd = 2 * 2 ^ (wd - 1) := by exact_mod_cast h2
  have hT := sum_digits_lt ((2 : ℤ) ^ wd) hB (fun j => blk.Δ i j + ((2 ^ (wd - 1) : ℕ) : ℤ)) blk.n
    (fun j _ => by
      have := abs_lt.mp (hbd i j)
      push_cast at this ⊢
      constructor <;> omega)
  have hT' : 0 ≤ blk.Tint wd i ∧ blk.Tint wd i < 2 ^ (wd * blk.n) := by
    unfold Blk.Tint
    rw [pow_mul]
    simpa [pow_mul] using hT
  have hx : (blk.xrow wd i : ℤ) < 2 ^ (wd * blk.n) := by
    unfold Blk.xrow
    simp only [p2_eq]
    exact_mod_cast Nat.mod_lt _ (show 0 < 2 ^ (wd * blk.n) by positivity)
  have hmod := (ZMod.intCast_eq_intCast_iff (blk.xrow wd i : ℤ) (blk.Tint wd i) (2 ^ (wd * blk.n))).mp
    (by have := blk.xrow_zmod wd hwd hnC hnN i hi; push_cast at this ⊢; exact this)
  unfold Int.ModEq at hmod
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hx),
    Int.emod_eq_of_lt hT'.1 (by exact_mod_cast hT'.2)] at hmod
  exact hmod

def absSum (h : ℕ) (ds : List ℕ) : ℕ := (ds.map (fun d => (d - h) + (h - d))).sum

/-- Streaming `∑ |digit - h|` over the first `n` digits. -/
def absScan (w h : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, X => ((X % p2 w) - h) + (h - X % p2 w) + absScan w h n (X >>> w)

theorem absScan_eq (w h : ℕ) : ∀ (n X : ℕ), absScan w h n X = absSum h (digitsN w n X)
  | 0, X => by simp [absScan, digitsN, absSum]
  | n + 1, X => by
    rw [absScan, absScan_eq w h n, digitsN]
    simp [absSum]

def Blk.ddOK (blk : Blk) (wd i : ℕ) : Bool :=
  decide (fieldAt blk.wC (blk.Cl.getD i 0) i ≠ p2 (blk.wC - 1)) &&
    decide (p2 (wd - 1) ≤ fieldAt wd (blk.xrow wd i) i) &&
    decide (absScan wd (p2 (wd - 1)) blk.n (blk.xrow wd i) ≤
      (fieldAt wd (blk.xrow wd i) i - p2 (wd - 1)) +
        ((fieldAt wd (blk.xrow wd i) i - p2 (wd - 1)) +
          (p2 (wd - 1) - fieldAt wd (blk.xrow wd i) i)))

/-- Packed check that `C N Cᵀ` is diagonally dominant with nonzero diagonal of `C`. -/
def Blk.psdOK (blk : Blk) (wd : ℕ) : Bool :=
  decide (1 ≤ blk.wN ∧ 1 ≤ blk.wC ∧ 1 ≤ wd ∧ blk.Nl.length = blk.n ∧ blk.Cl.length = blk.n ∧
    blk.n * blk.n * 2 ^ (blk.wC - 1 + (blk.wN - 1) + (blk.wC - 1)) < 2 ^ (wd - 1)) &&
  (List.range blk.n).all (blk.ddOK wd)

theorem nat_absdiff (a b : ℕ) : (((a - b) + (b - a) : ℕ) : ℤ) = |(a : ℤ) - b| := by
  rcases le_total a b with h | h
  · rw [abs_of_nonpos (by omega)]; omega
  · rw [abs_of_nonneg (by omega)]; omega

theorem Blk.dd_sound (blk : Blk) (wd : ℕ) (hwd : 1 ≤ wd) (hnC : blk.Cl.length = blk.n)
    (hnN : blk.Nl.length = blk.n) (hbd : ∀ i j, |blk.Δ i j| < ((2 ^ (wd - 1) : ℕ) : ℤ))
    (i : ℕ) (hi : i < blk.n) (hdd : blk.ddOK wd i = true) :
    ∑ j ∈ range blk.n, (if i = j then 0 else |blk.Δ i j|) ≤ blk.Δ i i := by
  have h2 := two_pow_eq wd hwd
  have hx := blk.xrow_eq wd hwd hnC hnN hbd i hi
  unfold Blk.Tint at hx
  unfold Blk.ddOK at hdd
  simp only [Bool.and_eq_true, decide_eq_true_eq, p2_eq] at hdd
  obtain ⟨⟨_, hge⟩, hsum⟩ := hdd
  generalize hc : 2 ^ (wd - 1) = c at hbd hx hge hsum h2
  -- the digits
  have hnn : ∀ j, 0 ≤ blk.Δ i j + (c : ℤ) := fun j => by
    have := abs_lt.mp (hbd i j); omega
  set dn : ℕ → ℕ := fun j => (blk.Δ i j + (c : ℤ)).toNat with hdn_def
  have hdn : ∀ j, (dn j : ℤ) = blk.Δ i j + (c : ℤ) := fun j => Int.toNat_of_nonneg (hnn j)
  have hdn_lt : ∀ j, dn j < 2 ^ wd := fun j => by
    have := abs_lt.mp (hbd i j)
    have h2c : ((2 ^ wd : ℕ) : ℤ) = 2 * (c : ℤ) := by exact_mod_cast h2
    have h3 : (dn j : ℤ) < ((2 ^ wd : ℕ) : ℤ) := by
      rw [hdn j, h2c]; omega
    exact_mod_cast h3
  have hxN : blk.xrow wd i = ∑ j ∈ range blk.n, dn j * 2 ^ (wd * j) := by
    have : ((blk.xrow wd i : ℕ) : ℤ) = ((∑ j ∈ range blk.n, dn j * 2 ^ (wd * j) : ℕ) : ℤ) := by
      rw [hx]; push_cast
      exact sum_congr rfl fun j _ => by rw [hdn j]
    exact_mod_cast this
  have hds : digitsN wd blk.n (blk.xrow wd i) = (List.range blk.n).map dn := by
    rw [digitsN_eq]
    refine List.map_congr_left fun j hj => ?_
    rw [hxN]
    exact fieldAt_pack wd blk.n dn hdn_lt j (List.mem_range.mp hj)
  have hfa : fieldAt wd (blk.xrow wd i) i = dn i := by
    rw [hxN]; exact fieldAt_pack wd blk.n dn hdn_lt i hi
  rw [absScan_eq, hds, hfa] at hsum
  rw [hfa] at hge
  unfold absSum at hsum
  rw [List.map_map, list_range_sum'] at hsum
  have hge' : (c : ℤ) ≤ dn i := by exact_mod_cast hge
  have hΔi : (0 : ℤ) ≤ blk.Δ i i := by have := hdn i; omega
  have h5 : ((∑ j ∈ range blk.n, ((fun d => d - c + (c - d)) ∘ dn) j : ℕ) : ℤ) =
      ∑ j ∈ range blk.n, |blk.Δ i j| := by
    push_cast [Nat.cast_sum]
    refine sum_congr rfl fun j _ => ?_
    simp only [Function.comp_apply]
    rw [nat_absdiff, hdn j]
    congr 1; ring
  have h6 := (Nat.cast_le (α := ℤ)).mpr hsum
  rw [h5] at h6
  have h7 : ((dn i - c : ℕ) : ℤ) = blk.Δ i i := by
    rw [Nat.cast_sub hge, hdn i]; ring
  have h9 : c - dn i = 0 := Nat.sub_eq_zero_of_le hge
  rw [h9] at h6
  push_cast [Nat.cast_add, h7] at h6
  have hsplit : ∑ j ∈ range blk.n, |blk.Δ i j| =
      |blk.Δ i i| + ∑ j ∈ range blk.n, (if i = j then 0 else |blk.Δ i j|) := by
    have : ∀ j, |blk.Δ i j| = (if i = j then |blk.Δ i i| else 0) +
        (if i = j then 0 else |blk.Δ i j|) := by
      intro j; by_cases hij : i = j
      · subst hij; rw [if_pos rfl, if_pos rfl, add_zero]
      · rw [if_neg hij, if_neg hij, zero_add]
    rw [sum_congr rfl fun j _ => this j, sum_add_distrib, sum_ite_eq]; simp [hi]
  rw [abs_of_nonneg hΔi] at hsplit
  linarith

theorem Blk.psd_sound (blk : Blk) (wd : ℕ) (h : blk.psdOK wd = true) (w : ℕ → ℝ) :
    0 ≤ ∑ i ∈ range blk.n, ∑ j ∈ range blk.n, (blk.Nz i j : ℝ) * w i * w j := by
  unfold Blk.psdOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hN, hC, hwd, hnN, hnC, hbound⟩, hall⟩ := h
  have hbd : ∀ i j, |blk.Δ i j| < ((2 ^ (wd - 1) : ℕ) : ℤ) := fun i j =>
    lt_of_le_of_lt (blk.Δ_bound hN hC i j) (by
      unfold Blk.oC Blk.oN
      have : blk.n * blk.n * (2 ^ (blk.wC - 1) * 2 ^ (blk.wN - 1) * 2 ^ (blk.wC - 1)) <
          2 ^ (wd - 1) := by
        rw [← pow_add, ← pow_add]; exact hbound
      exact_mod_cast this)
  refine psd_quad (blk.Nz) (blk.Cz) blk.N_symm blk.C_low ?_ ?_ w
  · intro i hi
    have := hall i hi
    unfold Blk.ddOK at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    unfold Blk.Cz; rw [if_pos le_rfl]
    intro h0
    apply this.1.1
    simp only [p2_eq]
    have : (fieldAt blk.wC (blk.Cl.getD i 0) i : ℤ) = ((2 ^ (blk.wC - 1) : ℕ) : ℤ) := by
      unfold Blk.oC at h0; linarith
    exact_mod_cast this
  · intro i hi
    exact blk.dd_sound wd hwd hnC hnN hbd i hi (hall i hi)

theorem Blk.psdOK_params (blk : Blk) (wd : ℕ) (h : blk.psdOK wd = true) :
    1 ≤ blk.wN ∧ blk.Nl.length = blk.n := by
  unfold Blk.psdOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2.2.2.1⟩

/-! ### Gram blocks: the polynomial and its Kronecker image -/

/-- Absolute keys: entries are `(gap, owner, coef)`. -/
def scanT {α : Type} : ℕ → List (ℕ × ℕ × α) → List (ℕ × ℕ × α)
  | _, [] => []
  | base, (g, o, c) :: r => (base + g, o, c) :: scanT (base + g) r

/-- A term `(gap, owner, coef)` stored in one natural number: `gap * 2^48 + owner * 2^24 + (coef + 2^23)`. -/
def decTm (x : ℕ) : ℕ × ℕ × ℤ := (x >>> 48, (x >>> 24) % 16777216, ((x % 16777216 : ℕ) : ℤ) - 8388608)

/-- All terms with absolute keys and signed coefficients. -/
def Blk.allT (blk : Blk) : List (ℕ × ℕ × ℤ) := scanT 0 (blk.tm.map decTm)

/-- `U_i = ∑_j N_ij x_j` evaluated at the Kronecker point. -/
def Blk.Uz (blk : Blk) (b i : ℕ) : ℤ :=
  (blk.allT.map (fun t => blk.Nz i t.2.1 * t.2.2 * 2 ^ (b * t.1))).sum

/-- Specification of `psiS`. -/
def Blk.psiS' (blk : Blk) (b : ℕ) : ℤ :=
  (blk.allT.map (fun t => t.2.2 * 2 ^ (b * t.1) * blk.Uz b t.2.1)).sum

/-- Number of the block's absolute coefficient mass. -/
def Blk.A (blk : Blk) : ℕ := (blk.allT.map (fun t => t.2.2.natAbs)).sum

theorem nat_list_sum_cast {α : Type*} (l : List α) (f : α → ℕ) :
    (((l.map f).sum : ℕ) : ℤ) = (l.map (fun x => (f x : ℤ))).sum := by
  induction l with
  | nil => simp
  | cons x r ih => simp [ih]

theorem list_sum_neg {α : Type*} (l : List α) (f : α → ℤ) :
    (l.map (fun x => -f x)).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons x r ih => simp [ih]; ring

theorem list_sum_sub {α : Type*} (l : List α) (f g : α → ℤ) :
    (l.map (fun x => f x - g x)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x r ih => simp [ih]; ring

/-! #### The polynomials -/

noncomputable def Blk.uP (blk : Blk) (D v i : ℕ) : MP v :=
  (blk.allT.map (fun t => MvPolynomial.C ((blk.Nz i t.2.1 * t.2.2 : ℤ) : Gi) * mon D v t.1)).sum

noncomputable def Blk.Sp (blk : Blk) (D v : ℕ) : MP v :=
  (blk.allT.map (fun t => MvPolynomial.C ((t.2.2 : ℤ) : Gi) * mon D v t.1 * blk.uP D v t.2.1)).sum

theorem psi_C {v : ℕ} (D b : ℕ) (a : Gi) : psi (v := v) D b (MvPolynomial.C a) = a := by
  simp [psi]

theorem psi_term {v : ℕ} (D b k : ℕ) (z : ℤ) (hk : k < D ^ v) :
    psi (v := v) D b (MvPolynomial.C (z : Gi) * mon D v k) = ((z * ((2 ^ (b * k) : ℕ) : ℤ) : ℤ) : Gi) := by
  rw [map_mul, psi_C, psi_mon D b k hk]
  simp

theorem Blk.psi_uP {v : ℕ} (blk : Blk) (D b i : ℕ) (hk : ∀ t ∈ blk.allT, t.1 < D ^ v) :
    psi (v := v) D b (blk.uP D v i) = ((blk.Uz b i : ℤ) : Gi) := by
  unfold Blk.uP Blk.Uz
  rw [map_list_sum, List.map_map, Int.cast_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  simp only [Function.comp_apply]
  rw [psi_term D b t.1 _ (hk t ht)]
  simp

theorem Blk.psi_Sp {v : ℕ} (blk : Blk) (D b : ℕ) (hk : ∀ t ∈ blk.allT, t.1 < D ^ v) :
    psi (v := v) D b (blk.Sp D v) = ((blk.psiS' b : ℤ) : Gi) := by
  unfold Blk.Sp Blk.psiS'
  rw [map_list_sum, List.map_map, Int.cast_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  simp only [Function.comp_apply]
  rw [map_mul, psi_term D b t.1 _ (hk t ht), blk.psi_uP D b _ hk]
  push_cast; ring

/-! ### The sliced evaluation of the Gram polynomial -/

/-- Shift of a signed integer (only natural numbers are shifted). -/
def shlZ (x : ℤ) (e : ℕ) : ℤ :=
  match x with
  | Int.ofNat n => Int.ofNat (n <<< e)
  | Int.negSucc n => Int.negSucc (((n + 1) <<< e) - 1)

theorem shlZ_eq (x : ℤ) (e : ℕ) : shlZ x e = x * 2 ^ e := by
  cases x with
  | ofNat n => simp [shlZ, Nat.shiftLeft_eq]
  | negSucc n =>
    have h1 : 1 ≤ (n + 1) * 2 ^ e := Nat.mul_pos (Nat.succ_pos n) (Nat.two_pow_pos e)
    simp only [shlZ, Nat.shiftLeft_eq]
    rw [Int.negSucc_eq, Int.negSucc_eq, Nat.cast_sub h1]
    push_cast; ring

theorem list_sum_comm {α β : Type*} (L1 : List α) (L2 : List β) (f : α → β → ℤ) :
    (L1.map (fun x => (L2.map (fun y => f x y)).sum)).sum =
      (L2.map (fun y => (L1.map (fun x => f x y)).sum)).sum := by
  induction L1 with
  | nil => simp
  | cons x r ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [← List.sum_map_add]

theorem foldl_add_sum {α : Type*} (g : α → ℤ) (L : List α) (a : ℤ) :
    L.foldl (fun acc x => acc + g x) a = a + (L.map g).sum := by
  induction L generalizing a with
  | nil => simp
  | cons x r ih => simp [ih]; ring

/-! #### Grouping by the high part of the key -/

abbrev Tm := ℕ × ℕ × ℤ

/-- Groups of consecutive terms with the same `key / K`; the stored keys are `key % K`. -/
def grpAux (K : ℕ) : ℕ → List Tm → List Tm → List (ℕ × List Tm)
  | h, cur, [] => [(h, cur.reverse)]
  | h, cur, t :: r =>
    if t.1 / K = h then grpAux K h ((t.1 % K, t.2) :: cur) r
    else (h, cur.reverse) :: grpAux K (t.1 / K) [(t.1 % K, t.2)] r

def grp (K : ℕ) : List Tm → List (ℕ × List Tm)
  | [] => []
  | t :: r => grpAux K (t.1 / K) [(t.1 % K, t.2)] r

theorem grpAux_sum (K : ℕ) (f : Tm → ℤ) : ∀ (r : List Tm) (h : ℕ) (cur : List Tm),
    ((grpAux K h cur r).map (fun g => (g.2.map (fun s => f (g.1 * K + s.1, s.2))).sum)).sum
      = (cur.map (fun s => f (h * K + s.1, s.2))).sum + (r.map f).sum := by
  intro r
  induction r with
  | nil =>
    intro h cur
    simp [grpAux, List.map_reverse, List.sum_reverse]
  | cons t r ih =>
    intro h cur
    unfold grpAux
    split_ifs with hh
    · rw [ih]
      simp only [List.map_cons, List.sum_cons]
      have : h * K + t.1 % K = t.1 := by rw [← hh]; exact Nat.div_add_mod' t.1 K
      rw [this]
      ring
    · simp only [List.map_cons, List.sum_cons, List.map_reverse, List.sum_reverse]
      rw [ih]
      have : t.1 / K * K + t.1 % K = t.1 := Nat.div_add_mod' t.1 K
      simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero, this]

theorem grp_sum (K : ℕ) (f : Tm → ℤ) (T : List Tm) :
    ((grp K T).map (fun g => (g.2.map (fun s => f (g.1 * K + s.1, s.2))).sum)).sum = (T.map f).sum := by
  cases T with
  | nil => simp [grp]
  | cons t r =>
    unfold grp
    rw [grpAux_sum]
    simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero]
    have : t.1 / K * K + t.1 % K = t.1 := Nat.div_add_mod' t.1 K
    rw [this]

theorem grpAux_owner (K : ℕ) (P : ℕ → Prop) : ∀ (r : List Tm) (h : ℕ) (cur : List Tm),
    (∀ s ∈ cur, P s.2.1) → (∀ t ∈ r, P t.2.1) → ∀ g ∈ grpAux K h cur r, ∀ s ∈ g.2, P s.2.1 := by
  intro r
  induction r with
  | nil =>
    intro h cur hc _ g hg s hs
    simp only [grpAux, List.mem_singleton] at hg
    subst hg
    exact hc s (List.mem_reverse.mp hs)
  | cons t r ih =>
    intro h cur hc hr g hg s hs
    unfold grpAux at hg
    split_ifs at hg with hh
    · exact ih h _ (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hr t (by simp)
        · exact hc x hx) (fun x hx => hr x (by simp [hx])) g hg s hs
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact hc s (List.mem_reverse.mp hs)
      · exact ih _ _ (fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; exact hr t (by simp))
          (fun x hx => hr x (by simp [hx])) g hg s hs

theorem grp_owner (K : ℕ) (P : ℕ → Prop) (T : List Tm) (hT : ∀ t ∈ T, P t.2.1) :
    ∀ g ∈ grp K T, ∀ s ∈ g.2, P s.2.1 := by
  cases T with
  | nil => simp [grp]
  | cons t r =>
    exact grpAux_owner K P r _ _ (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact hT t (by simp))
      (fun x hx => hT x (by simp [hx]))

/-! #### Merging sorted slice lists -/

/-- `∑ x 2^(b K σ)` over a list of `(σ, x)`. -/
def evalSl (K b : ℕ) (l : List (ℕ × ℤ)) : ℤ := (l.map (fun p => p.2 * 2 ^ (b * (K * p.1)))).sum

/-- Kernel evaluation of `evalSl`: shifts of the slices. -/
def evalSlK (K b : ℕ) (l : List (ℕ × ℤ)) : ℤ := l.foldl (fun acc p => acc + shlZ p.2 (b * (K * p.1))) 0

theorem evalSlK_eq (K b : ℕ) (l : List (ℕ × ℤ)) : evalSlK K b l = evalSl K b l := by
  unfold evalSlK evalSl
  simp only [shlZ_eq]
  rw [foldl_add_sum, zero_add]

def mergeAdd : ℕ → List (ℕ × ℤ) → List (ℕ × ℤ) → List (ℕ × ℤ)
  | 0, l1, l2 => l1 ++ l2
  | _ + 1, [], l2 => l2
  | _ + 1, l1, [] => l1
  | f + 1, (k1, x1) :: r1, (k2, x2) :: r2 =>
    if k1 < k2 then (k1, x1) :: mergeAdd f r1 ((k2, x2) :: r2)
    else if k2 < k1 then (k2, x2) :: mergeAdd f ((k1, x1) :: r1) r2
    else (k1, x1 + x2) :: mergeAdd f r1 r2

theorem evalSl_mergeAdd (K b : ℕ) : ∀ (f : ℕ) (l1 l2 : List (ℕ × ℤ)),
    evalSl K b (mergeAdd f l1 l2) = evalSl K b l1 + evalSl K b l2 := by
  intro f
  induction f with
  | zero => intro l1 l2; simp [mergeAdd, evalSl]
  | succ f ih =>
    intro l1 l2
    cases l1 with
    | nil => simp [mergeAdd, evalSl]
    | cons p r1 =>
      cases l2 with
      | nil => simp [mergeAdd, evalSl]
      | cons q r2 =>
        obtain ⟨k1, x1⟩ := p
        obtain ⟨k2, x2⟩ := q
        simp only [mergeAdd]
        split_ifs with h1 h2
        · have := ih r1 ((k2, x2) :: r2)
          simp only [evalSl, List.map_cons, List.sum_cons] at this ⊢
          rw [this]; ring
        · have := ih ((k1, x1) :: r1) r2
          simp only [evalSl, List.map_cons, List.sum_cons] at this ⊢
          rw [this]; ring
        · have hk : k1 = k2 := by omega
          subst hk
          have := ih r1 r2
          simp only [evalSl, List.map_cons, List.sum_cons] at this ⊢
          rw [this]; ring

def mergeRound : List (List (ℕ × ℤ)) → List (List (ℕ × ℤ))
  | [] => []
  | [l] => [l]
  | l1 :: l2 :: r => mergeAdd (l1.length + l2.length) l1 l2 :: mergeRound r

def evalSlL (K b : ℕ) (ls : List (List (ℕ × ℤ))) : ℤ := (ls.map (evalSl K b)).sum

theorem evalSlL_mergeRound (K b : ℕ) : ∀ ls : List (List (ℕ × ℤ)),
    evalSlL K b (mergeRound ls) = evalSlL K b ls
  | [] => by simp [mergeRound, evalSlL]
  | [l] => by simp [mergeRound, evalSlL]
  | l1 :: l2 :: r => by
    have := evalSlL_mergeRound K b r
    simp only [mergeRound, evalSlL, List.map_cons, List.sum_cons] at this ⊢
    rw [this, evalSl_mergeAdd]; ring

def mergeTree : ℕ → List (List (ℕ × ℤ)) → List (ℕ × ℤ)
  | 0, ls => ls.flatten
  | _ + 1, [] => []
  | _ + 1, [l] => l
  | f + 1, l1 :: l2 :: r => mergeTree f (mergeRound (l1 :: l2 :: r))

theorem evalSl_mergeTree (K b : ℕ) : ∀ (f : ℕ) (ls : List (List (ℕ × ℤ))),
    evalSl K b (mergeTree f ls) = evalSlL K b ls := by
  intro f
  induction f with
  | zero =>
    intro ls
    simp only [mergeTree, evalSl, evalSlL, List.map_flatten, List.sum_flatten, List.map_map]
    rfl
  | succ f ih =>
    intro ls
    match ls with
    | [] => simp [mergeTree, evalSl, evalSlL]
    | [l] => simp [mergeTree, evalSlL]
    | l1 :: l2 :: r =>
      rw [mergeTree, ih, evalSlL_mergeRound]

/-! #### The leaf computation -/

theorem foldl_add_sumN {α : Type*} (g : α → ℕ) (L : List α) (a : ℕ) :
    L.foldl (fun acc x => acc + g x) a = a + (L.map g).sum := by
  induction L generalizing a with
  | nil => simp
  | cons x r ih => simp [ih]; ring

theorem sum_filter_split {α : Type*} (L : List α) (p : α → Bool) (f : α → ℤ) :
    (L.map f).sum = ((L.filter p).map f).sum + ((L.filter (fun x => !p x)).map f).sum := by
  induction L with
  | nil => simp
  | cons x r ih =>
    by_cases h : p x
    · simp [h, ih]; ring
    · simp [h, ih]; ring

/-- `∑ field · |c| 2^(b k)` over a term list (all natural numbers). -/
def innerN (wN row b : ℕ) (B : List Tm) : ℕ :=
  B.foldl (fun acc t => acc + ((fieldAt wN row t.2.1 * t.2.2.natAbs) <<< (b * t.1))) 0

/-- `∑ c 2^(b k)` over a term list. -/
def psiB (b : ℕ) (B : List Tm) : ℤ := B.foldl (fun acc t => acc + shlZ t.2.2 (b * t.1)) 0

theorem psiB_eq (b : ℕ) (B : List Tm) : psiB b B = (B.map (fun t => t.2.2 * 2 ^ (b * t.1))).sum := by
  unfold psiB
  simp only [shlZ_eq]
  rw [foldl_add_sum, zero_add]

theorem innerN_eq (wN row b : ℕ) (B : List Tm) : (innerN wN row b B : ℤ) =
    (B.map (fun t => ((fieldAt wN row t.2.1 : ℕ) : ℤ) * (t.2.2.natAbs : ℤ) * 2 ^ (b * t.1))).sum := by
  unfold innerN
  simp only [Nat.shiftLeft_eq]
  rw [foldl_add_sumN, zero_add, nat_list_sum_cast]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  push_cast; ring

theorem innerN_diff (wN row b : ℕ) (B : List Tm) :
    (innerN wN row b (B.filter (fun t => decide (0 ≤ t.2.2))) : ℤ) -
      (innerN wN row b (B.filter (fun t => !decide (0 ≤ t.2.2))) : ℕ) =
    (B.map (fun t => ((fieldAt wN row t.2.1 : ℕ) : ℤ) * t.2.2 * 2 ^ (b * t.1))).sum := by
  rw [innerN_eq, innerN_eq, sum_filter_split B (fun t => decide (0 ≤ t.2.2))
    (fun t => ((fieldAt wN row t.2.1 : ℕ) : ℤ) * t.2.2 * 2 ^ (b * t.1))]
  have h1 : ((B.filter (fun t => decide (0 ≤ t.2.2))).map (fun t =>
      ((fieldAt wN row t.2.1 : ℕ) : ℤ) * (t.2.2.natAbs : ℤ) * 2 ^ (b * t.1))).sum =
      ((B.filter (fun t => decide (0 ≤ t.2.2))).map (fun t =>
      ((fieldAt wN row t.2.1 : ℕ) : ℤ) * t.2.2 * 2 ^ (b * t.1))).sum := by
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    have : 0 ≤ t.2.2 := by simpa using (List.mem_filter.mp ht).2
    rw [Int.natAbs_of_nonneg this]
  have h2 : ((B.filter (fun t => !decide (0 ≤ t.2.2))).map (fun t =>
      ((fieldAt wN row t.2.1 : ℕ) : ℤ) * (t.2.2.natAbs : ℤ) * 2 ^ (b * t.1))).sum =
      -((B.filter (fun t => !decide (0 ≤ t.2.2))).map (fun t =>
      ((fieldAt wN row t.2.1 : ℕ) : ℤ) * t.2.2 * 2 ^ (b * t.1))).sum := by
    rw [← list_sum_neg]
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    have h3 : ¬ 0 ≤ t.2.2 := by simpa using (List.mem_filter.mp ht).2
    have h4 : t.2.2 ≤ 0 := by omega
    rw [Int.ofNat_natAbs_of_nonpos h4]; ring
  rw [h1, h2]; ring

/-- A group of terms with the data the leaf needs: positive and negative parts and `∑ c 2^(b k)`. -/
structure GD where
  hk : ℕ
  ts : List Tm
  bp : List Tm
  bn : List Tm
  psi : ℤ

def mkGD (b : ℕ) (g : ℕ × List Tm) : GD :=
  ⟨g.1, g.2, g.2.filter (fun t => decide (0 ≤ t.2.2)), g.2.filter (fun t => !decide (0 ≤ t.2.2)),
    psiB b g.2⟩

/-- `∑_{s ∈ A, t ∈ B} N_{o_s o_t} c_s c_t 2^(b (k_s + k_t))`, rows of `N` fetched from the packed `RR`. -/
def leaf (RR nW wN oN b : ℕ) (A : List Tm) (g : GD) : ℤ :=
  A.foldl (fun acc s =>
    acc + shlZ (s.2.2 * (((innerN wN (fieldAt nW RR s.2.1) b g.bp : ℕ) : ℤ) -
      (innerN wN (fieldAt nW RR s.2.1) b g.bn : ℕ) - (oN : ℤ) * g.psi)) (b * s.1)) 0

def leafS (row : ℕ → ℕ) (wN oN b : ℕ) (A B : List Tm) : ℤ :=
  (A.map (fun s => (B.map (fun t =>
    (((fieldAt wN (row s.2.1) t.2.1 : ℕ) : ℤ) - oN) * s.2.2 * t.2.2 *
      2 ^ (b * (s.1 + t.1)))).sum)).sum

theorem leaf_eq (RR nW wN oN b : ℕ) (A : List Tm) (g : ℕ × List Tm) :
    leaf RR nW wN oN b A (mkGD b g) = leafS (fieldAt nW RR) wN oN b A g.2 := by
  unfold leaf leafS
  simp only [mkGD, shlZ_eq, foldl_add_sum, zero_add]
  refine congrArg List.sum (List.map_congr_left fun s _ => ?_)
  rw [innerN_diff, psiB_eq]
  have key : ∀ t ∈ g.2, (((fieldAt wN (fieldAt nW RR s.2.1) t.2.1 : ℕ) : ℤ) - oN) * s.2.2 * t.2.2 *
      2 ^ (b * (s.1 + t.1)) =
      (s.2.2 * 2 ^ (b * s.1)) * (((fieldAt wN (fieldAt nW RR s.2.1) t.2.1 : ℕ) : ℤ) * t.2.2 * 2 ^ (b * t.1)) -
      (s.2.2 * 2 ^ (b * s.1)) * ((oN : ℤ) * (t.2.2 * 2 ^ (b * t.1))) := by
    intro t _
    rw [mul_add b s.1 t.1, pow_add]; ring
  rw [List.map_congr_left key, list_sum_sub]
  simp only [List.sum_map_mul_left]
  ring

/-! #### Symmetric group-pair rows, restricted to a set of slices -/

def triRowsK (keep : ℕ → Bool) (lf : GD → GD → ℤ) : List GD → List (List (ℕ × ℤ))
  | [] => []
  | a :: r => ((if keep (a.hk + a.hk) then [(a.hk + a.hk, lf a a)] else []) ++
      (r.filter (fun g => keep (a.hk + g.hk))).map (fun g => (a.hk + g.hk, 2 * lf a g))) ::
      triRowsK keep lf r

theorem sum_filter_ite {α : Type*} (r : List α) (p : α → Bool) (f : α → ℤ) :
    ((r.filter p).map f).sum = (r.map (fun x => if p x = true then f x else 0)).sum := by
  induction r with
  | nil => rfl
  | cons x r ih => by_cases h : p x = true <;> simp [h, ih]

theorem evalSlL_triRowsK (K b : ℕ) (keep : ℕ → Bool) (lf : GD → GD → ℤ) : ∀ L : List GD,
    (∀ x ∈ L, ∀ y ∈ L, lf x y = lf y x) →
    evalSlL K b (triRowsK keep lf L) =
      (L.map (fun x => (L.map (fun y => (if keep (x.hk + y.hk) = true then lf x y else 0) *
        2 ^ (b * (K * (x.hk + y.hk))))).sum)).sum
  | [], _ => by simp [triRowsK, evalSlL]
  | a :: r, hs => by
    have ih := evalSlL_triRowsK K b keep lf r
      (fun x hx y hy => hs x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
    have hsym : ∀ y ∈ r, lf y a = lf a y := fun y hy => hs y (List.mem_cons_of_mem _ hy) a (List.mem_cons_self)
    simp only [triRowsK, evalSlL, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    have e1 : evalSl K b ((if keep (a.hk + a.hk) then [(a.hk + a.hk, lf a a)] else []) ++
        (r.filter (fun g => keep (a.hk + g.hk))).map (fun g => (a.hk + g.hk, 2 * lf a g))) =
        (if keep (a.hk + a.hk) = true then lf a a else 0) * 2 ^ (b * (K * (a.hk + a.hk))) +
          2 * (r.map (fun y => (if keep (a.hk + y.hk) = true then lf a y else 0) *
            2 ^ (b * (K * (a.hk + y.hk))))).sum := by
      unfold evalSl
      rw [List.map_append, List.sum_append, List.map_map, sum_filter_ite, ← List.sum_map_mul_left]
      congr 1
      · by_cases hk : keep (a.hk + a.hk) = true <;> simp [hk]
      · refine congrArg List.sum (List.map_congr_left fun g _ => ?_)
        by_cases hk : keep (a.hk + g.hk) = true <;> simp [hk]; ring
    have e2 : (r.map (fun x => (if keep (x.hk + a.hk) = true then lf x a else 0) *
        2 ^ (b * (K * (x.hk + a.hk))))).sum =
        (r.map (fun y => (if keep (a.hk + y.hk) = true then lf a y else 0) *
          2 ^ (b * (K * (a.hk + y.hk))))).sum := by
      refine congrArg List.sum (List.map_congr_left fun y hy => ?_)
      rw [hsym y hy, add_comm y.hk a.hk]
    rw [e1, List.sum_map_add, e2]
    ring

/-! #### Slices of a block -/

theorem sum_pack_lt (w : ℕ) (d : ℕ → ℕ) (hd : ∀ j, d j < 2 ^ w) : ∀ n : ℕ,
    ∑ j ∈ range n, d j * 2 ^ (w * j) < 2 ^ (w * n) := by
  intro n
  induction n generalizing d with
  | zero => simp
  | succ n ih =>
    rw [pack_succ]
    have h2 := ih (fun j => d (j + 1)) (fun j => hd _)
    have h1 := hd 0
    calc d 0 + 2 ^ w * ∑ j ∈ range n, d (j + 1) * 2 ^ (w * j)
        < 2 ^ w + 2 ^ w * ∑ j ∈ range n, d (j + 1) * 2 ^ (w * j) := by omega
      _ = 2 ^ w * (1 + ∑ j ∈ range n, d (j + 1) * 2 ^ (w * j)) := by ring
      _ ≤ 2 ^ w * 2 ^ (w * n) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 ^ (w * (n + 1)) := by rw [mul_add, mul_one, pow_add, mul_comm]

theorem foldr_pack_list (w : ℕ) : ∀ l : List ℕ,
    l.foldr (fun r acc => r + (acc <<< w)) 0 = ∑ i ∈ range l.length, l.getD i 0 * 2 ^ (w * i)
  | [] => by simp
  | r :: t => by
    rw [List.foldr_cons, List.length_cons, pack_succ, foldr_pack_list w t, Nat.shiftLeft_eq, mul_comm]
    simp

/-- The matrix `N`, all rows packed into one number. -/
def Blk.rr (blk : Blk) : ℕ :=
  (buildFull blk.wN blk.Nl).foldr (fun r acc => r + (acc <<< (blk.wN * blk.n))) 0

def Blk.slicesC (blk : Blk) (keep : ℕ → Bool) (K b : ℕ) : List (ℕ × ℤ) :=
  let gd := (grp K blk.allT).map (mkGD b)
  mergeTree (gd.length + 1)
    (triRowsK keep (fun a g => leaf blk.rr (blk.wN * blk.n) blk.wN blk.oN b a.ts g) gd)

theorem Blk.rows_field (blk : Blk) (hnN : blk.Nl.length = blk.n) (o j : ℕ) (ho : o < blk.n)
    (hj : j < blk.n) :
    fieldAt blk.wN ((buildFull blk.wN blk.Nl).getD o 0) j = gN blk.wN blk.Nl o j := by
  rw [buildFull_eq, FF, hnN]
  have : ((List.range blk.n).map (fun i => ∑ j ∈ range blk.n, gN blk.wN blk.Nl i j * 2 ^ (blk.wN * j))).getD o 0
      = ∑ j ∈ range blk.n, gN blk.wN blk.Nl o j * 2 ^ (blk.wN * j) := by
    simp [List.getD_eq_getElem?_getD, ho]
  rw [this]
  exact fieldAt_pack _ _ (fun j => gN blk.wN blk.Nl o j) (fun j => fieldAt_lt _ _ _) j hj

theorem Blk.rr_field (blk : Blk) (hnN : blk.Nl.length = blk.n) (o j : ℕ) (ho : o < blk.n)
    (hj : j < blk.n) :
    fieldAt blk.wN (fieldAt (blk.wN * blk.n) blk.rr o) j = gN blk.wN blk.Nl o j := by
  have hbd : ∀ i, (buildFull blk.wN blk.Nl).getD i 0 < 2 ^ (blk.wN * blk.n) := by
    intro i
    rw [buildFull_eq, FF, hnN]
    by_cases hi : i < blk.n
    · have : ((List.range blk.n).map (fun i => ∑ j ∈ range blk.n, gN blk.wN blk.Nl i j *
          2 ^ (blk.wN * j))).getD i 0 = ∑ j ∈ range blk.n, gN blk.wN blk.Nl i j * 2 ^ (blk.wN * j) := by
        simp [List.getD_eq_getElem?_getD, hi]
      rw [this]
      exact sum_pack_lt blk.wN (fun j => gN blk.wN blk.Nl i j) (fun j => fieldAt_lt _ _ _) blk.n
    · simp [List.getD_eq_getElem?_getD, hi]
  have h1 : fieldAt (blk.wN * blk.n) blk.rr o = (buildFull blk.wN blk.Nl).getD o 0 := by
    have hlen : (buildFull blk.wN blk.Nl).length = blk.n := by
      rw [buildFull_eq, FF, List.length_map, List.length_range, hnN]
    unfold Blk.rr
    rw [foldr_pack_list, hlen]
    exact fieldAt_pack _ _ (fun i => (buildFull blk.wN blk.Nl).getD i 0) hbd o ho
  rw [h1]
  exact blk.rows_field hnN o j ho hj

/-- The summand of the double sum, in absolute keys. -/
def Blk.Fa (blk : Blk) (b : ℕ) (s t : Tm) : ℤ :=
  blk.Nz s.2.1 t.2.1 * s.2.2 * t.2.2 * 2 ^ (b * (s.1 + t.1))

theorem Blk.psiS'_double (blk : Blk) (b : ℕ) :
    blk.psiS' b = (blk.allT.map (fun s => (blk.allT.map (fun t => blk.Fa b s t)).sum)).sum := by
  unfold Blk.psiS' Blk.Uz
  refine congrArg List.sum (List.map_congr_left fun s _ => ?_)
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  have : (2 : ℤ) ^ (b * (s.1 + t.1)) = 2 ^ (b * s.1) * 2 ^ (b * t.1) := by
    rw [← pow_add, mul_add]
  unfold Blk.Fa
  rw [this]; ring

theorem leafS_comm (row : ℕ → ℕ) (wN oN b n : ℕ) (A B : List Tm)
    (hA : ∀ s ∈ A, s.2.1 < n) (hB : ∀ t ∈ B, t.2.1 < n)
    (hrow : ∀ i j, i < n → j < n → fieldAt wN (row i) j = fieldAt wN (row j) i) :
    leafS row wN oN b A B = leafS row wN oN b B A := by
  unfold leafS
  rw [list_sum_comm A B (fun s t => (((fieldAt wN (row s.2.1) t.2.1 : ℕ) : ℤ) - oN) * s.2.2 * t.2.2 *
      2 ^ (b * (s.1 + t.1)))]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  refine congrArg List.sum (List.map_congr_left fun s hs => ?_)
  rw [hrow _ _ (hA s hs) (hB t ht), add_comm s.1 t.1]
  ring

theorem Blk.leaf_term (blk : Blk) (K b : ℕ) (hnN : blk.Nl.length = blk.n) (a g : ℕ × List Tm)
    (ha : ∀ s ∈ a.2, s.2.1 < blk.n) (hg : ∀ t ∈ g.2, t.2.1 < blk.n) :
    leafS (fieldAt (blk.wN * blk.n) blk.rr) blk.wN blk.oN b a.2 g.2 * 2 ^ (b * (K * (a.1 + g.1))) =
      (a.2.map (fun s => (g.2.map (fun t =>
        blk.Fa b (a.1 * K + s.1, s.2) (g.1 * K + t.1, t.2))).sum)).sum := by
  unfold leafS
  rw [← List.sum_map_mul_right]
  refine congrArg List.sum (List.map_congr_left fun s hs => ?_)
  rw [← List.sum_map_mul_right]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  have e1 : fieldAt blk.wN (fieldAt (blk.wN * blk.n) blk.rr s.2.1) t.2.1 = gN blk.wN blk.Nl s.2.1 t.2.1 :=
    blk.rr_field hnN _ _ (ha s hs) (hg t ht)
  have e2 : (2 : ℤ) ^ (b * (a.1 * K + s.1 + (g.1 * K + t.1))) =
      2 ^ (b * (s.1 + t.1)) * 2 ^ (b * (K * (a.1 + g.1))) := by
    rw [← pow_add]; congr 1; ring
  unfold Blk.Fa Blk.Nz
  rw [e1, e2]
  ring

theorem Blk.slicesC_sum (blk : Blk) (keep : ℕ → Bool) (K b : ℕ) (hnN : blk.Nl.length = blk.n)
    (hgown : ∀ a ∈ grp K blk.allT, ∀ s ∈ a.2, s.2.1 < blk.n) :
    evalSl K b (blk.slicesC keep K b) = ((grp K blk.allT).map (fun a => ((grp K blk.allT).map (fun g =>
      (if keep (a.1 + g.1) = true then
        leafS (fieldAt (blk.wN * blk.n) blk.rr) blk.wN blk.oN b a.2 g.2 else 0) *
        2 ^ (b * (K * (a.1 + g.1))))).sum)).sum := by
  unfold Blk.slicesC
  rw [evalSl_mergeTree, evalSlL_triRowsK]
  · simp only [List.map_map, Function.comp_def]
    refine congrArg List.sum (List.map_congr_left fun a _ => ?_)
    refine congrArg List.sum (List.map_congr_left fun g _ => ?_)
    rw [leaf_eq]
    rfl
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hy
    have e1 := leaf_eq blk.rr (blk.wN * blk.n) blk.wN blk.oN b (mkGD b a).ts g
    have e2 := leaf_eq blk.rr (blk.wN * blk.n) blk.wN blk.oN b (mkGD b g).ts a
    simp only [mkGD] at e1 e2 ⊢
    rw [e1, e2]
    exact leafS_comm _ _ _ _ blk.n _ _ (hgown a ha) (hgown g hg) (fun i j hi hj => by
      rw [blk.rr_field hnN _ _ hi hj, blk.rr_field hnN _ _ hj hi]; exact gN_symm _ _ _ _)

theorem Blk.slices_double (blk : Blk) (K b : ℕ) (hnN : blk.Nl.length = blk.n)
    (hown : ∀ t ∈ blk.allT, t.2.1 < blk.n) :
    ((grp K blk.allT).map (fun a => ((grp K blk.allT).map (fun g =>
      leafS (fieldAt (blk.wN * blk.n) blk.rr) blk.wN blk.oN b a.2 g.2 *
        2 ^ (b * (K * (a.1 + g.1))))).sum)).sum = blk.psiS' b := by
  have hgown : ∀ a ∈ grp K blk.allT, ∀ s ∈ a.2, s.2.1 < blk.n := grp_owner K (· < blk.n) blk.allT hown
  rw [blk.psiS'_double b]
  have h1 : ∀ a ∈ grp K blk.allT, ((grp K blk.allT).map (fun g =>
      leafS (fieldAt (blk.wN * blk.n) blk.rr) blk.wN blk.oN b a.2 g.2 *
        2 ^ (b * (K * (a.1 + g.1))))).sum =
      (a.2.map (fun s => (blk.allT.map (blk.Fa b (a.1 * K + s.1, s.2))).sum)).sum := by
    intro a ha
    rw [List.map_congr_left (fun g hg => blk.leaf_term K b hnN a g (hgown a ha) (hgown g hg))]
    rw [list_sum_comm (grp K blk.allT) a.2 (fun g s => (g.2.map (fun t =>
      blk.Fa b (a.1 * K + s.1, s.2) (g.1 * K + t.1, t.2))).sum)]
    refine congrArg List.sum (List.map_congr_left fun s _ => ?_)
    exact grp_sum K (blk.Fa b (a.1 * K + s.1, s.2)) blk.allT
  rw [List.map_congr_left h1]
  exact grp_sum K (fun s => (blk.allT.map (fun t => blk.Fa b s t)).sum) blk.allT

/-- the slices `σ ≡ c (mod m)` -/
def chunk (m c σ : ℕ) : Bool := decide (σ % m = c)

theorem sum_chunk (m : ℕ) (hm : 0 < m) (σ : ℕ) (X : ℤ) :
    ((List.range m).map (fun c => if chunk m c σ = true then X else 0)).sum = X := by
  rw [list_range_sum']
  simp [chunk, Finset.sum_ite_eq, Nat.mod_lt _ hm]

theorem sum_range_comm {α : Type*} (m : ℕ) (L : List α) (f : ℕ → α → ℤ) :
    (((List.range m).map (fun c => (L.map (fun a => f c a)).sum)).sum) =
      (L.map (fun a => ((List.range m).map (fun c => f c a)).sum)).sum :=
  list_sum_comm (List.range m) L f

theorem Blk.slicesC_total (blk : Blk) (m K b : ℕ) (hm : 0 < m) (hnN : blk.Nl.length = blk.n)
    (hown : ∀ t ∈ blk.allT, t.2.1 < blk.n) :
    ((List.range m).map (fun c => evalSl K b (blk.slicesC (chunk m c) K b))).sum = blk.psiS' b := by
  have hgown : ∀ a ∈ grp K blk.allT, ∀ s ∈ a.2, s.2.1 < blk.n := grp_owner K (· < blk.n) blk.allT hown
  rw [← blk.slices_double K b hnN hown]
  rw [List.map_congr_left (fun c _ => blk.slicesC_sum (chunk m c) K b hnN hgown)]
  rw [sum_range_comm m (grp K blk.allT) (fun c a => ((grp K blk.allT).map (fun g =>
    (if chunk m c (a.1 + g.1) = true then
      leafS (fieldAt (blk.wN * blk.n) blk.rr) blk.wN blk.oN b a.2 g.2 else 0) *
      2 ^ (b * (K * (a.1 + g.1))))).sum)]
  refine congrArg List.sum (List.map_congr_left fun a _ => ?_)
  rw [sum_range_comm m (grp K blk.allT) (fun c g =>
    (if chunk m c (a.1 + g.1) = true then
      leafS (fieldAt (blk.wN * blk.n) blk.rr) blk.wN blk.oN b a.2 g.2 else 0) *
      2 ^ (b * (K * (a.1 + g.1))))]
  refine congrArg List.sum (List.map_congr_left fun g _ => ?_)
  rw [List.sum_map_mul_right, sum_chunk m hm]
/-! ### The target polynomial as data -/

def polyT (p : ℕ × ℤ) : Tm := (p.1, 0, p.2)

/-- Absolute keys of a gap-encoded sparse polynomial `[(gap, coef)]`. -/
def Poly.terms (poly : List (ℕ × ℤ)) : List Tm := scanT 0 (poly.map polyT)

def Poly.l1 (poly : List (ℕ × ℤ)) : ℕ := ((Poly.terms poly).map (fun t => t.2.2.natAbs)).sum

noncomputable def Poly.pol (D v : ℕ) (poly : List (ℕ × ℤ)) : MP v :=
  ((Poly.terms poly).map (fun t => MvPolynomial.C ((t.2.2 : ℤ) : Gi) * mon D v t.1)).sum


/-! ### The Gram side of the check -/

def Blk.termsOK (blk : Blk) (D v dm : ℕ) : Bool :=
  (blk.allT).all (fun t => decide (t.1 < D ^ v) && decide (t.2.1 < blk.n) &&
    (List.range v).all (fun l => decide (digit D t.1 l ≤ dm)))

def Blk.nB (blk : Blk) : ℕ := blk.mu * (blk.A * (blk.oN * blk.A))

def scaleL (m : ℤ) (l : List (ℕ × ℤ)) : List (ℕ × ℤ) := l.map (fun p => (p.1, m * p.2))

def allSlicesC (m c K b : ℕ) (blocks : List Blk) : List (ℕ × ℤ) :=
  mergeTree (blocks.length + 1)
    (blocks.map (fun blk => scaleL (blk.mu : ℤ) (blk.slicesC (chunk m c) K b)))

def polySlices (K b lcm : ℕ) (poly : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  (grp K (Poly.terms poly)).map (fun g => (g.1, g.2.foldl (fun acc t =>
    acc + shlZ ((lcm : ℤ) * t.2.2) (b * t.1)) 0))

def nzL (l : List (ℕ × ℤ)) : List (ℕ × ℤ) := l.filter (fun p => decide (p.2 ≠ 0))

theorem evalSl_nzL (K b : ℕ) : ∀ l : List (ℕ × ℤ), evalSl K b (nzL l) = evalSl K b l
  | [] => rfl
  | p :: r => by
    have ih := evalSl_nzL K b r
    by_cases h : p.2 = 0
    · have e : nzL (p :: r) = nzL r := by simp [nzL, h]
      rw [e, ih]; simp [evalSl, h]
    · have e : nzL (p :: r) = p :: nzL r := by simp [nzL, h]
      rw [e]
      simp only [evalSl, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]

theorem evalSl_scaleL (K b : ℕ) (m : ℤ) (l : List (ℕ × ℤ)) :
    evalSl K b (scaleL m l) = m * evalSl K b l := by
  unfold scaleL evalSl
  rw [List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  simp only [Function.comp_apply]; ring

theorem evalSl_polySlices (K b lcm : ℕ) (poly : List (ℕ × ℤ)) :
    evalSl K b (polySlices K b lcm poly) =
      (lcm : ℤ) * ((Poly.terms poly).map (fun t => t.2.2 * 2 ^ (b * t.1))).sum := by
  have h := grp_sum K (fun t => (lcm : ℤ) * (t.2.2 * 2 ^ (b * t.1))) (Poly.terms poly)
  rw [← List.sum_map_mul_left]
  rw [← h]
  unfold polySlices evalSl
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun g _ => ?_)
  simp only [Function.comp_apply]
  rw [foldl_add_sum, zero_add, ← List.sum_map_mul_right]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  have : (2 : ℤ) ^ (b * (g.1 * K + t.1)) = 2 ^ (b * t.1) * 2 ^ (b * (K * g.1)) := by
    rw [← pow_add]; congr 1; ring
  rw [shlZ_eq, this]; ring

theorem evalSl_allSlicesC (m c K b : ℕ) (blocks : List Blk) :
    evalSl K b (allSlicesC m c K b blocks) =
      (blocks.map (fun blk => (blk.mu : ℤ) * evalSl K b (blk.slicesC (chunk m c) K b))).sum := by
  unfold allSlicesC
  rw [evalSl_mergeTree]
  unfold evalSlL
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun blk hb => ?_)
  simp only [Function.comp_apply]
  rw [evalSl_scaleL]

theorem evalSl_allSlicesC_total (m K b : ℕ) (hm : 0 < m) (blocks : List Blk)
    (h : ∀ blk ∈ blocks, blk.Nl.length = blk.n ∧ ∀ t ∈ blk.allT, t.2.1 < blk.n) :
    ((List.range m).map (fun c => evalSl K b (allSlicesC m c K b blocks))).sum =
      (blocks.map (fun blk => (blk.mu : ℤ) * blk.psiS' b)).sum := by
  simp only [evalSl_allSlicesC]
  rw [sum_range_comm m blocks (fun c blk => (blk.mu : ℤ) * evalSl K b (blk.slicesC (chunk m c) K b))]
  refine congrArg List.sum (List.map_congr_left fun blk hb => ?_)
  rw [List.sum_map_mul_left, blk.slicesC_total m K b hm (h blk hb).1 (h blk hb).2]

theorem evalSl_polyChunks (m K b lcm : ℕ) (hm : 0 < m) (poly : List (ℕ × ℤ)) :
    ((List.range m).map (fun c => evalSl K b
      ((polySlices K b lcm poly).filter (fun p => chunk m c p.1)))).sum =
      evalSl K b (polySlices K b lcm poly) := by
  unfold evalSl
  simp only [sum_filter_ite]
  refine (sum_range_comm m (polySlices K b lcm poly)
    (fun c x => if chunk m c x.1 = true then x.2 * 2 ^ (b * (K * x.1)) else 0)).trans ?_
  exact congrArg List.sum (List.map_congr_left fun x _ => sum_chunk m hm x.1 _)

/-- The slice check restricted to the slices `σ ≡ c (mod m)`. -/
def sliceOK (m c K b lcm : ℕ) (blocks : List Blk) (poly : List (ℕ × ℤ)) : Bool :=
  decide (nzL (allSlicesC m c K b blocks) =
    nzL ((polySlices K b lcm poly).filter (fun p => chunk m c p.1)))

namespace Maj
variable {v : ℕ}

theorem pow {d : Fin v → ℕ} {n : ℕ} {p : MP v} (hp : Maj d n p) (e : ℕ) :
    Maj (fun l => e * d l) (n ^ e) (p ^ e) := by
  induction e with
  | zero => simpa using (one : Maj (fun _ : Fin v => 0) 1 (1 : MP v))
  | succ e ih =>
    rw [_root_.pow_succ]
    refine (ih.mul hp).mono (fun l => ?_) le_rfl
    simp [Nat.succ_mul]

theorem listSum {α : Type*} (d : Fin v → ℕ) (l : List α) (f : α → MP v) (n : α → ℕ)
    (h : ∀ x ∈ l, Maj d (n x) (f x)) : Maj d ((l.map n).sum) ((l.map f).sum) := by
  induction l with
  | nil => simpa using (zero : Maj (fun _ : Fin v => 0) 0 (0 : MP v)).mono (fun l => Nat.zero_le _) le_rfl
  | cons x r ih =>
    simp only [List.map_cons, List.sum_cons]
    have := (h x (by simp)).add (ih fun y hy => h y (by simp [hy]))
    exact this.mono (fun l => by simp) le_rfl

end Maj

theorem mon_maj {v : ℕ} (D k dm : ℕ) (hd : ∀ l : Fin v, digit D k l ≤ dm) :
    Maj (fun _ => dm) 1 (mon D v k) := by
  classical
  unfold mon
  have h1 : ∀ l ∈ (Finset.univ : Finset (Fin v)),
      Maj (fun l' => digit D k l * (if l' = l then 1 else 0)) (1 ^ digit D k l)
        ((MvPolynomial.X l : MP v) ^ digit D k l) := fun l _ => (Maj.X l).pow _
  have := Maj.prod (Finset.univ : Finset (Fin v)) (fun l => (MvPolynomial.X l : MP v) ^ digit D k l)
    (fun l l' => digit D k l * (if l' = l then 1 else 0)) (fun l => 1 ^ digit D k l) h1
  refine this.mono (fun l' => ?_) (by simp)
  simp only [mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq]
  simpa using hd l'

theorem Blk.uP_maj {v : ℕ} (blk : Blk) (hN : 1 ≤ blk.wN) (D i dm : ℕ)
    (hd : ∀ t ∈ blk.allT, ∀ l : Fin v, digit D t.1 l ≤ dm) :
    Maj (fun _ => dm) (blk.oN * blk.A) (blk.uP D v i) := by
  unfold Blk.uP Blk.A
  have := Maj.listSum (fun _ : Fin v => dm) (blk.allT)
    (fun t => MvPolynomial.C ((blk.Nz i t.2.1 * t.2.2 : ℤ) : Gi) * mon D v t.1)
    (fun t => nrmG ((blk.Nz i t.2.1 * t.2.2 : ℤ) : Gi) * 1) (fun t ht =>
      ((Maj.C ((blk.Nz i t.2.1 * t.2.2 : ℤ) : Gi)).mul (mon_maj D t.1 dm (hd t ht))).mono
        (fun l => by simp) le_rfl)
  refine this.mono (fun l => le_rfl) ?_
  rw [← List.sum_map_mul_left]
  refine List.sum_le_sum fun t _ => ?_
  rw [mul_one, nrmG_int, Int.natAbs_mul]
  have h := blk.N_bound hN i t.2.1
  rw [abs_le] at h
  have : (blk.Nz i t.2.1).natAbs ≤ blk.oN := by omega
  nlinarith [Nat.mul_le_mul_right t.2.2.natAbs this]

theorem Blk.Sp_maj {v : ℕ} (blk : Blk) (hN : 1 ≤ blk.wN) (D dm : ℕ)
    (hd : ∀ t ∈ blk.allT, ∀ l : Fin v, digit D t.1 l ≤ dm) :
    Maj (fun _ => dm + dm) (blk.A * (blk.oN * blk.A)) (blk.Sp D v) := by
  unfold Blk.Sp
  have := Maj.listSum (fun _ : Fin v => dm + dm) (blk.allT)
    (fun t => MvPolynomial.C ((t.2.2 : ℤ) : Gi) * mon D v t.1 * blk.uP D v t.2.1)
    (fun t => (t.2.2.natAbs * 1) * (blk.oN * blk.A)) (fun t ht =>
      (((Maj.C ((t.2.2 : ℤ) : Gi)).mul (mon_maj D t.1 dm (hd t ht))).mul
        (blk.uP_maj hN D t.2.1 dm hd)).mono (fun l => by simp) (by rw [nrmG_int]))
  refine this.mono (fun l => le_rfl) (le_of_eq ?_)
  have e : ∀ t : ℕ × ℕ × ℤ, t.2.2.natAbs * 1 * (blk.oN * blk.A) = t.2.2.natAbs * (blk.oN * blk.A) := fun t => by rw [mul_one]
  simp only [e]
  rw [List.sum_map_mul_right]
  rfl

/-! ### Real evaluation of the Gram polynomial -/

noncomputable def ev {v : ℕ} (t : Fin v → ℝ) : MP v →+* ℂ :=
  MvPolynomial.eval₂Hom Gi.toC (fun l => ((t l : ℝ) : ℂ))

noncomputable def mr (D v : ℕ) (t : Fin v → ℝ) (k : ℕ) : ℝ := ∏ l : Fin v, t l ^ digit D k l

theorem ev_C {v : ℕ} (t : Fin v → ℝ) (a : Gi) : ev t (MvPolynomial.C a) = Gi.toC a := by
  simp [ev]

theorem ev_C_int {v : ℕ} (t : Fin v → ℝ) (z : ℤ) :
    ev t (MvPolynomial.C (z : Gi)) = ((z : ℝ) : ℂ) := by
  rw [ev_C]; simp [Gi.toC]

theorem ev_mon {v : ℕ} (t : Fin v → ℝ) (D k : ℕ) : ev t (mon D v k) = ((mr D v t k : ℝ) : ℂ) := by
  unfold mon mr
  rw [map_prod]
  simp [ev]

theorem ofReal_list_sum {α : Type*} (L : List α) (f : α → ℝ) :
    (L.map (fun x => ((f x : ℝ) : ℂ))).sum = (((L.map f).sum : ℝ) : ℂ) := by
  induction L with
  | nil => simp
  | cons x r ih => simp [ih]

theorem Blk.ev_uP {v : ℕ} (blk : Blk) (D : ℕ) (t : Fin v → ℝ) (i : ℕ) :
    ev t (blk.uP D v i) = (((blk.allT).map (fun s =>
      (blk.Nz i s.2.1 : ℝ) * ((s.2.2 : ℝ) * mr D v t s.1))).sum : ℝ) := by
  unfold Blk.uP
  rw [map_list_sum, List.map_map, ← ofReal_list_sum]
  congr 1
  refine List.map_congr_left fun s _ => ?_
  simp only [Function.comp_apply, map_mul, ev_C_int, ev_mon]
  push_cast; ring

theorem Blk.ev_Sp {v : ℕ} (blk : Blk) (D : ℕ) (t : Fin v → ℝ) :
    ev t (blk.Sp D v) = (((blk.allT).map (fun p =>
      ((p.2.2 : ℝ) * mr D v t p.1) * ((blk.allT).map (fun s =>
      (blk.Nz p.2.1 s.2.1 : ℝ) * ((s.2.2 : ℝ) * mr D v t s.1))).sum)).sum : ℝ) := by
  unfold Blk.Sp
  rw [map_list_sum, List.map_map, ← ofReal_list_sum]
  congr 1
  refine List.map_congr_left fun s _ => ?_
  simp only [Function.comp_apply, map_mul, ev_C_int, ev_mon, Blk.ev_uP]
  push_cast; ring

theorem rowsum {n : ℕ} (ts : List (ℕ × ℝ)) (hts : ∀ p ∈ ts, p.1 < n) (f : ℕ → ℝ) :
    ∑ j ∈ range n, f j * (ts.map (fun p => if p.1 = j then p.2 else 0)).sum
      = (ts.map (fun q => f q.1 * q.2)).sum := by
  induction ts with
  | nil => simp
  | cons q r ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, sum_add_distrib]
    rw [ih fun p hp => hts p (by simp [hp])]
    have : ∀ j, f j * (if q.1 = j then q.2 else 0) = if q.1 = j then f q.1 * q.2 else 0 := by
      intro j; by_cases h : q.1 = j
      · subst h; simp
      · simp [h]
    simp_rw [this]
    rw [sum_ite_eq, if_pos (mem_range.mpr (hts q (by simp)))]

theorem quad_regroup {n : ℕ} (Nf : ℕ → ℕ → ℝ) (ts : List (ℕ × ℝ)) (hts : ∀ p ∈ ts, p.1 < n) :
    (ts.map (fun p => p.2 * (ts.map (fun q => Nf p.1 q.1 * q.2)).sum)).sum =
      ∑ i ∈ range n, ∑ j ∈ range n, Nf i j * (ts.map (fun p => if p.1 = i then p.2 else 0)).sum *
        (ts.map (fun p => if p.1 = j then p.2 else 0)).sum := by
  have h1 : ∀ i, ∑ j ∈ range n, Nf i j * (ts.map (fun p => if p.1 = i then p.2 else 0)).sum *
        (ts.map (fun p => if p.1 = j then p.2 else 0)).sum
      = (ts.map (fun p => if p.1 = i then p.2 else 0)).sum * (ts.map (fun q => Nf i q.1 * q.2)).sum := by
    intro i
    rw [← rowsum ts hts (Nf i), mul_sum]
    exact sum_congr rfl fun j _ => by ring
  rw [sum_congr rfl fun i _ => h1 i]
  have h2 : ∑ i ∈ range n, (ts.map (fun p => if p.1 = i then p.2 else 0)).sum *
        (ts.map (fun q => Nf i q.1 * q.2)).sum =
      ∑ i ∈ range n, (ts.map (fun q => Nf i q.1 * q.2)).sum *
        (ts.map (fun p => if p.1 = i then p.2 else 0)).sum :=
    sum_congr rfl fun i _ => mul_comm _ _
  rw [h2, rowsum ts hts (fun i => (ts.map (fun q => Nf i q.1 * q.2)).sum)]
  congr 1
  exact List.map_congr_left fun p _ => mul_comm _ _

theorem Blk.ev_Sp_nonneg {v : ℕ} (blk : Blk) (D wd : ℕ)
    (hown : ∀ s ∈ blk.allT, s.2.1 < blk.n) (hp : blk.psdOK wd = true)
    (t : Fin v → ℝ) : ∃ q : ℝ, 0 ≤ q ∧ ev t (blk.Sp D v) = (q : ℂ) := by
  refine ⟨_, ?_, blk.ev_Sp D t⟩
  have := quad_regroup (fun i j => (blk.Nz i j : ℝ))
    ((blk.allT).map (fun s => (s.2.1, (s.2.2 : ℝ) * mr D v t s.1)))
    (by intro p hp; simp only [List.mem_map] at hp; obtain ⟨s, hs, rfl⟩ := hp; exact hown s hs)
  simp only [List.map_map, Function.comp_def] at this
  rw [this]
  exact blk.psd_sound wd hp _

theorem Poly.psi_pol {v : ℕ} (D b : ℕ) (poly : List (ℕ × ℤ))
    (hk : ∀ t ∈ Poly.terms poly, t.1 < D ^ v) :
    psi (v := v) D b (Poly.pol D v poly) =
      ((((Poly.terms poly).map (fun t => t.2.2 * 2 ^ (b * t.1))).sum : ℤ) : Gi) := by
  unfold Poly.pol
  rw [map_list_sum, List.map_map, Int.cast_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  simp only [Function.comp_apply]
  rw [psi_term D b t.1 _ (hk t ht)]
  simp

theorem Poly.pol_maj {v : ℕ} (D dpoly : ℕ) (poly : List (ℕ × ℤ))
    (hd : ∀ t ∈ Poly.terms poly, ∀ l : Fin v, digit D t.1 l ≤ dpoly) :
    Maj (fun _ => dpoly) (Poly.l1 poly) (Poly.pol D v poly) := by
  unfold Poly.pol Poly.l1
  have := Maj.listSum (fun _ : Fin v => dpoly) (Poly.terms poly)
    (fun t => MvPolynomial.C ((t.2.2 : ℤ) : Gi) * mon D v t.1) (fun t => t.2.2.natAbs * 1)
    (fun t ht => ((Maj.C ((t.2.2 : ℤ) : Gi)).mul (mon_maj D t.1 dpoly (hd t ht))).mono
      (fun l => by simp) (by rw [nrmG_int]))
  simpa only [mul_one] using this.mono (fun l => le_rfl) le_rfl

def checkP (v D b vL : ℕ) (dP : Fin v → ℕ) (nP dpoly : ℕ) (poly : List (ℕ × ℤ)) (Pval : Gi) : Bool :=
  decide (1 ≤ D ∧ 1 ≤ b ∧ (∀ l, dP l < D) ∧ dpoly < D) &&
  decide (Pval.im = 0 ∧ Pval.re = evalSlK (D ^ vL) b (polySlices (D ^ vL) b 1 poly)) &&
  decide ((nP + Poly.l1 poly) * 2 < 2 ^ b) &&
  (Poly.terms poly).all (fun t => decide (t.1 < D ^ v) &&
    (List.range v).all (fun l => decide (digit D t.1 l ≤ dpoly)))

theorem Poly.facts_of_check {v D b vL nP dpoly : ℕ} {dP : Fin v → ℕ} {poly : List (ℕ × ℤ)} {Pval : Gi}
    (hc : checkP v D b vL dP nP dpoly poly Pval = true) :
    (∀ t ∈ Poly.terms poly, t.1 < D ^ v) ∧
      (∀ t ∈ Poly.terms poly, ∀ l : Fin v, digit D t.1 l ≤ dpoly) := by
  unfold checkP at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨_, hterms⟩ := hc
  exact ⟨fun t ht => (hterms t ht).1, fun t ht l => (hterms t ht).2 l (List.mem_range.mpr l.2)⟩

theorem Poly.eq_of_check {v D b vL nP dpoly : ℕ} {dP : Fin v → ℕ} {poly : List (ℕ × ℤ)} {Pval : Gi}
    (hc : checkP v D b vL dP nP dpoly poly Pval = true) (P : MP v) (hψ : psi D b P = Pval)
    (hM : Maj dP nP P) : P = Poly.pol D v poly := by
  obtain ⟨hk, hdig⟩ := Poly.facts_of_check hc
  unfold checkP at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨hD, hb, hdP, hdp⟩, hPv, hPre⟩, hnorm⟩, _⟩ := hc
  have hpol := Poly.pol_maj D dpoly poly hdig
  have hh : Maj (fun l => max (dP l) dpoly) (nP + Poly.l1 poly) (P - Poly.pol D v poly) :=
    hM.sub hpol
  have hz : P - Poly.pol D v poly = 0 := by
    refine psi_inj (D := D) (b := b) hD hb _ (fun l => ?_) ?_ ?_
    · exact lt_of_le_of_lt (hh.1 l) (max_lt (hdP l) hdp)
    · exact lt_of_le_of_lt (Nat.mul_le_mul_right 2 hh.2) hnorm
    · rw [map_sub, hψ, Poly.psi_pol D b poly hk]
      have h1 := evalSl_polySlices (D ^ vL) b 1 poly
      rw [← evalSlK_eq] at h1
      rw [← one_mul (((Poly.terms poly).map (fun t => t.2.2 * 2 ^ (b * t.1))).sum), ← Nat.cast_one (R := ℤ), ← h1, ← hPre]
      refine Gi.ext ?_ ?_ <;> simp [hPv]
  exact sub_eq_zero.mp hz

theorem Maj.nat {v : ℕ} (n : ℕ) : Maj (fun _ : Fin v => 0) n (n : MP v) := by
  have := Maj.C (v := v) (n : Gi)
  rw [← map_natCast (MvPolynomial.C : Gi →+* MP v) n] at *
  exact ⟨this.1, this.2.trans (by simp [nrmG])⟩

theorem list_re_nonneg {α : Type*} (l : List α) (f : α → ℂ) (h : ∀ x ∈ l, 0 ≤ (f x).re) :
    0 ≤ ((l.map f).sum).re := by
  induction l with
  | nil => simp
  | cons x r ih =>
    simp only [List.map_cons, List.sum_cons, Complex.add_re]
    exact add_nonneg (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

/-- The kernel check of the Gram side of a certificate: `lcm * P = ∑ μ_h S_h` on sliced Kronecker
values, the coefficient bounds, and positivity of every Gram block. -/
def Blk.sameN (a b : Blk) : Bool :=
  decide (a.n = b.n ∧ a.wN = b.wN ∧ a.wC = b.wC ∧ a.Nl = b.Nl ∧ a.Cl = b.Cl)

theorem Blk.psdOK_of_same (a b : Blk) (h : a.sameN b = true) (wd : ℕ) : a.psdOK wd = b.psdOK wd := by
  obtain ⟨n1, mu1, wN1, wC1, Nl1, Cl1, tm1⟩ := a
  obtain ⟨n2, mu2, wN2, wC2, Nl2, Cl2, tm2⟩ := b
  simp only [Blk.sameN, decide_eq_true_eq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

def checkSa (v D b dm dpoly lcm : ℕ) (blocks psdBlocks : List Blk) (poly : List (ℕ × ℤ)) : Bool :=
  decide (0 < lcm ∧ 1 ≤ D ∧ 1 ≤ b ∧ dm + dm < D ∧ dpoly < D) &&
  decide ((lcm * Poly.l1 poly + (blocks.map Blk.nB).sum) * 2 < 2 ^ b) &&
  blocks.all (fun blk => blk.termsOK D v dm && psdBlocks.any (fun p => p.sameN blk))

/-- The full Gram-side check; the slice identity is split into `m` chunks `σ ≡ c (mod m)` so that
each can be verified by a separate kernel call (`checkS_iff`). -/
def checkS (m v D b dm dpoly lcm wd vL : ℕ) (blocks psdBlocks : List Blk) (poly : List (ℕ × ℤ)) : Bool :=
  decide (0 < m) && checkSa v D b dm dpoly lcm blocks psdBlocks poly &&
  (List.range m).all (fun c => sliceOK m c (D ^ vL) b lcm blocks poly) &&
  psdBlocks.all (fun p => p.psdOK wd)

theorem checkS_iff {m v D b dm dpoly lcm wd vL : ℕ} {blocks psdBlocks : List Blk} {poly : List (ℕ × ℤ)} :
    checkS m v D b dm dpoly lcm wd vL blocks psdBlocks poly = true ↔
      0 < m ∧ checkSa v D b dm dpoly lcm blocks psdBlocks poly = true ∧
      (∀ c < m, sliceOK m c (D ^ vL) b lcm blocks poly = true) ∧
      ∀ p ∈ psdBlocks, p.psdOK wd = true := by
  unfold checkS
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  tauto

theorem forall_mem_of_getD {α : Type*} [Inhabited α] (l : List α) (f : α → Bool)
    (h : ∀ i < l.length, f (l.getD i default) = true) : ∀ x ∈ l, f x = true := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  simpa [List.getD_eq_getElem?_getD, hi] using h i hi

theorem forall_lt_zero {P : ℕ → Prop} : ∀ c < 0, P c := fun c hc => absurd hc (Nat.not_lt_zero c)

theorem forall_lt_succ {P : ℕ → Prop} {n : ℕ} (h : ∀ c < n, P c) (hn : P n) : ∀ c < n + 1, P c := by
  intro c hc
  rcases Nat.lt_succ_iff_lt_or_eq.mp hc with h' | rfl
  · exact h c h'
  · exact hn

/-- `checkS` from its separately verified parts. -/
theorem checkS_of_parts {m k v D b dm dpoly lcm wd vL : ℕ} {blocks psdBlocks : List Blk}
    {poly : List (ℕ × ℤ)} (hm : 0 < m)
    (ha : checkSa v D b dm dpoly lcm blocks psdBlocks poly = true)
    (hs : ∀ c < m, sliceOK m c (D ^ vL) b lcm blocks poly = true)
    (hk : psdBlocks.length ≤ k)
    (hp : ∀ i < k, (psdBlocks.getD i default).psdOK wd = true) :
    checkS m v D b dm dpoly lcm wd vL blocks psdBlocks poly = true :=
  checkS_iff.mpr ⟨hm, ha, hs, forall_mem_of_getD _ _ (fun i hi => hp i (lt_of_lt_of_le hi hk))⟩

theorem checkS_blocks {m v D b dm dpoly lcm wd vL : ℕ} {blocks psdBlocks : List Blk} {poly : List (ℕ × ℤ)}
    (hc : checkS m v D b dm dpoly lcm wd vL blocks psdBlocks poly = true) :
    ∀ blk ∈ blocks, blk.termsOK D v dm = true ∧ blk.psdOK wd = true := by
  obtain ⟨_, hSa, _, hpsd⟩ := checkS_iff.mp hc
  unfold checkSa at hSa
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true] at hSa
  obtain ⟨_, hblk⟩ := hSa
  intro blk hb
  obtain ⟨h1, p, hp, hsame⟩ := hblk blk hb
  refine ⟨h1, ?_⟩
  rw [← Blk.psdOK_of_same p blk hsame wd]
  exact hpsd p hp

theorem checkS_facts {m v D b dm dpoly lcm wd vL : ℕ} {blocks psdBlocks : List Blk} {poly : List (ℕ × ℤ)}
    (hc : checkS m v D b dm dpoly lcm wd vL blocks psdBlocks poly = true) :
    (∀ blk ∈ blocks, ∀ t ∈ blk.allT, t.1 < D ^ v) ∧
    (∀ blk ∈ blocks, ∀ t ∈ blk.allT, t.2.1 < blk.n) ∧
    (∀ blk ∈ blocks, 1 ≤ blk.wN ∧ blk.Nl.length = blk.n) ∧
    (∀ blk ∈ blocks, ∀ s ∈ blk.allT, ∀ l : Fin v, digit D s.1 l ≤ dm) := by
  have hblk' := checkS_blocks hc
  refine ⟨fun blk hb s hs => ?_, fun blk hb s hs => ?_, fun blk hb => ?_, fun blk hb s hs l => ?_⟩
  · have := (hblk' blk hb).1
    unfold Blk.termsOK at this
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    exact (this s hs).1.1
  · have := (hblk' blk hb).1
    unfold Blk.termsOK at this
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    exact (this s hs).1.2
  · exact blk.psdOK_params wd (hblk' blk hb).2
  · have := (hblk' blk hb).1
    unfold Blk.termsOK at this
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    exact (this s hs).2 l (List.mem_range.mpr l.2)

theorem checkS_sound {m v D b dm dpoly lcm wd vL : ℕ} {blocks psdBlocks : List Blk} {poly : List (ℕ × ℤ)}
    (hc : checkS m v D b dm dpoly lcm wd vL blocks psdBlocks poly = true)
    (hk : ∀ t ∈ Poly.terms poly, t.1 < D ^ v)
    (hdig : ∀ t ∈ Poly.terms poly, ∀ l : Fin v, digit D t.1 l ≤ dpoly) :
    (lcm : MP v) * Poly.pol D v poly = (blocks.map (fun blk => (blk.mu : MP v) * blk.Sp D v)).sum := by
  obtain ⟨hkB, hown, hpar, hdigB⟩ := checkS_facts hc
  obtain ⟨hm, hSa, hsl, _⟩ := checkS_iff.mp hc
  unfold checkSa at hSa
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true] at hSa
  obtain ⟨⟨⟨hlcm, hD, hb, hdm, hdp⟩, hnorm⟩, _⟩ := hSa
  let S : MP v := (blocks.map (fun blk => (blk.mu : MP v) * blk.Sp D v)).sum
  have hS : Maj (fun _ => dm + dm) ((blocks.map Blk.nB).sum) S := by
    have := Maj.listSum (fun _ : Fin v => dm + dm) blocks (fun blk => (blk.mu : MP v) * blk.Sp D v)
      Blk.nB (fun blk hb => by
        have h1 := (Maj.nat (v := v) blk.mu).mul (blk.Sp_maj (hpar blk hb).1 D dm (hdigB blk hb))
        exact h1.mono (fun l => by simp) (by simp [Blk.nB]))
    exact this
  have hpol := Poly.pol_maj D dpoly poly hdig
  have hh : Maj (fun l => max (0 + dpoly) (dm + dm)) (lcm * Poly.l1 poly + (blocks.map Blk.nB).sum)
      ((lcm : MP v) * Poly.pol D v poly - S) := ((Maj.nat (v := v) lcm).mul hpol).sub hS
  have hint : ((blocks.map (fun blk => (blk.mu : ℤ) * blk.psiS' (b))).sum : ℤ) =
      (lcm : ℤ) * ((Poly.terms poly).map (fun t => t.2.2 * 2 ^ (b * t.1))).sum := by
    have h1 := evalSl_allSlicesC_total m (D ^ vL) b hm blocks
      (fun blk hbk => ⟨(hpar blk hbk).2, hown blk hbk⟩)
    have h2 := evalSl_polySlices (D ^ vL) b lcm poly
    have h3 : ((List.range m).map (fun c => evalSl (D ^ vL) b (allSlicesC m c (D ^ vL) b blocks))).sum =
        ((List.range m).map (fun c => evalSl (D ^ vL) b
          ((polySlices (D ^ vL) b lcm poly).filter (fun p => chunk m c p.1)))).sum :=
      congrArg List.sum (List.map_congr_left fun c hc' => by
        have := hsl c (List.mem_range.mp hc')
        unfold sliceOK at this
        simp only [decide_eq_true_eq] at this
        rw [← evalSl_nzL, this, evalSl_nzL])
    rw [h1, evalSl_polyChunks m (D ^ vL) b lcm hm, h2] at h3
    exact h3
  have hzero : (lcm : MP v) * Poly.pol D v poly - S = 0 := by
    refine psi_inj (D := D) (b := b) hD hb _ (fun l => ?_) ?_ ?_
    · exact lt_of_le_of_lt (hh.1 l) (max_lt (by simpa using hdp) hdm)
    · exact lt_of_le_of_lt (Nat.mul_le_mul_right 2 hh.2) hnorm
    · rw [map_sub, map_mul, map_natCast, Poly.psi_pol D b poly hk]
      have hS' : psi D b S = (((blocks.map (fun blk => (blk.mu : ℤ) * blk.psiS' b)).sum : ℤ) : Gi) := by
        simp only [S]
        rw [map_list_sum, List.map_map, Int.cast_list_sum, List.map_map]
        congr 1
        refine List.map_congr_left fun blk hbk => ?_
        simp only [Function.comp_apply]
        rw [map_mul, map_natCast, blk.psi_Sp D b (hkB blk hbk)]
        push_cast; rfl
      rw [hS', hint]
      push_cast; ring
  exact sub_eq_zero.mp hzero

theorem checkS_nonneg {m v D b dm dpoly lcm wd vL : ℕ} {blocks psdBlocks : List Blk} {poly : List (ℕ × ℤ)}
    (hc : checkS m v D b dm dpoly lcm wd vL blocks psdBlocks poly = true) (t : Fin v → ℝ) :
    0 ≤ (ev t ((blocks.map (fun blk => (blk.mu : MP v) * blk.Sp D v)).sum)).re := by
  obtain ⟨hkB, hown, hpar, hdigB⟩ := checkS_facts hc
  have hblk' := checkS_blocks hc
  rw [map_list_sum, List.map_map]
  refine list_re_nonneg _ _ fun blk hbk => ?_
  obtain ⟨q, hq, hev⟩ := blk.ev_Sp_nonneg D wd (hown blk hbk) (hblk' blk hbk).2 t
  simp only [Function.comp_apply, map_mul, map_natCast, hev]
  simp [Complex.mul_re]
  exact mul_nonneg (Nat.cast_nonneg _) hq

theorem cert_core_of_eq {m v D bS dm dpoly lcm wd vL : ℕ} {blocks psdBlocks : List Blk} {poly : List (ℕ × ℤ)}
    (hS : checkS m v D bS dm dpoly lcm wd vL blocks psdBlocks poly = true)
    (P : MP v) (hPeq : P = Poly.pol D v poly) (hk : ∀ t ∈ Poly.terms poly, t.1 < D ^ v)
    (hdig : ∀ t ∈ Poly.terms poly, ∀ l : Fin v, digit D t.1 l ≤ dpoly) (t : Fin v → ℝ) :
    0 ≤ (ev t P).re := by
  have heq := checkS_sound hS hk hdig
  rw [← hPeq] at heq
  have hSre := checkS_nonneg hS t
  have hlcm : 0 < lcm := by
    obtain ⟨_, hSa, _⟩ := checkS_iff.mp hS
    unfold checkSa at hSa
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hSa
    exact hSa.1.1.1
  have h2 := congrArg (fun p => (ev t p).re) heq
  simp only [map_mul, map_natCast] at h2
  have h3 : (lcm : ℝ) * (ev t P).re = (ev t ((blocks.map (fun blk => (blk.mu : MP v) * blk.Sp D v)).sum)).re := by
    simpa [Complex.mul_re] using h2
  have hl : (0 : ℝ) < lcm := by exact_mod_cast hlcm
  by_contra hneg
  have : (lcm : ℝ) * (ev t P).re < 0 := mul_neg_of_pos_of_neg hl (not_le.mp hneg)
  linarith

theorem cert_core {m v D bP bS dm dpoly lcm wd vL nP : ℕ} {blocks psdBlocks : List Blk} {poly : List (ℕ × ℤ)}
    {Pval : Gi} {dP : Fin v → ℕ}
    (hP : checkP v D bP vL dP nP dpoly poly Pval = true)
    (hS : checkS m v D bS dm dpoly lcm wd vL blocks psdBlocks poly = true)
    (P : MP v) (hψ : psi D bP P = Pval) (hM : Maj dP nP P) (t : Fin v → ℝ) :
    0 ≤ (ev t P).re := by
  obtain ⟨hk, hdig⟩ := Poly.facts_of_check hP
  exact cert_core_of_eq hS P (Poly.eq_of_check hP P hψ hM) hk hdig t

end Kron
end Results.SoulesPotOrderFour
