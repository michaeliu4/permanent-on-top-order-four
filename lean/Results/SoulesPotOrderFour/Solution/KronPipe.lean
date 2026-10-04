import Results.SoulesPotOrderFour.Solution.Kron
import Results.SoulesPotOrderFour.Solution.Charts

open Finset Matrix Equiv

/-!
# From the polynomial pipeline to the matrices of `Basic.lean`

Ring homomorphisms commute with `Matrix.permanent`, `Matrix.det`, `cofactorPermMatrix`, `signCofactorMatrix`,
`pairingMatrix`, `K31`, `K22`, `e1`, `e2` (`map_*`), so the Kronecker value of the target polynomial of a chart
can be computed by kernel evaluation over `Gi` (`Tgt`, `cert_poly`).  `Bd` mirrors the majorant calculus `Maj`
and certifies the degree and norm bounds.  `cert_V1`, `cert_Vz`, `cert_V2`, `cert_VR` are the chart wrappers
(complex rank-three, zero, rank-two, real chart); `cert_checkS` proves the Gram side by separate kernel calls.
-/

namespace Results.SoulesPotOrderFour
namespace Kron

section Natural
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

theorem map_permanent {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    f A.permanent = (A.map f).permanent := by
  simp [Matrix.permanent, map_sum, map_prod]

theorem map_det' {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    f A.det = (A.map f).det := RingHom.map_det f A

theorem map_Q3 : (Q3 : Matrix (Fin 4) (Fin 3) R).map f = Q3 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Q3]

theorem map_Q2 : (Q2 : Matrix (Fin 3) (Fin 2) R).map f = Q2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Q2]

theorem map_permMinor (A : Matrix (Fin 4) (Fin 4) R) (i j : Fin 4) :
    f (permMinor A i j) = permMinor (A.map f) i j := by
  unfold permMinor
  rw [map_permanent]; rfl

theorem map_F (A : Matrix (Fin 4) (Fin 4) R) :
    (cofactorPermMatrix A).map f = cofactorPermMatrix (A.map f) := by
  ext i j; simp [cofactorPermMatrix, map_permMinor]

theorem map_lamsub {n : ℕ} (lam : R) (M : Matrix (Fin n) (Fin n) R) :
    (lam • (1 : Matrix (Fin n) (Fin n) R) - M).map f = f lam • (1 : Matrix (Fin n) (Fin n) S) - M.map f := by
  ext i j; simp [Matrix.one_apply]; split_ifs <;> simp

theorem map_G (A : Matrix (Fin 4) (Fin 4) R) :
    (signCofactorMatrix A).map f = signCofactorMatrix (A.map f) := by
  ext i j
  simp [signCofactorMatrix, map_det' f, Matrix.submatrix_map]

theorem map_H (A : Matrix (Fin 4) (Fin 4) R) :
    (pairingMatrix A).map f = pairingMatrix (A.map f) := by
  ext i j
  simp [pairingMatrix, map_sum, phi, map_prod]

theorem map_K31 (lam : R) (A : Matrix (Fin 4) (Fin 4) R) :
    (K31 lam A).map f = K31 (f lam) (A.map f) := by
  unfold K31
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, map_Q3, map_lamsub, map_F]

theorem map_K22 (lam : R) (A : Matrix (Fin 4) (Fin 4) R) :
    (K22 lam A).map f = K22 (f lam) (A.map f) := by
  unfold K22
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, map_Q2, map_lamsub, map_H]

theorem map_e1 (K : Matrix (Fin 3) (Fin 3) R) : f (e1 K) = e1 (K.map f) := by
  simp [e1]

theorem map_e2 (K : Matrix (Fin 3) (Fin 3) R) : f (e2 K) = e2 (K.map f) := by
  simp [e2]

theorem map_e2four (G : Matrix (Fin 4) (Fin 4) R) : f (e2four G) = e2four (G.map f) := by
  simp [e2four, map_sum, apply_ite f]

theorem map_trace' {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    f A.trace = (A.map f).trace := by
  simp [Matrix.trace, map_sum]

end Natural/-! ### Bound pairs: a bookkeeping algebra mirroring `Maj` -/

/-- Per-variable degree bounds and an `L¹`-norm bound. -/
structure Bd (v : ℕ) where
  d : Fin v → ℕ
  n : ℕ

namespace Bd
variable {v : ℕ}

instance : Add (Bd v) := ⟨fun a b => ⟨fun l => max (a.d l) (b.d l), a.n + b.n⟩⟩
instance : Mul (Bd v) := ⟨fun a b => ⟨fun l => a.d l + b.d l, a.n * b.n⟩⟩
instance : Zero (Bd v) := ⟨⟨fun _ => 0, 0⟩⟩
instance : One (Bd v) := ⟨⟨fun _ => 0, 1⟩⟩

theorem ext' {a b : Bd v} (h1 : ∀ l, a.d l = b.d l) (h2 : a.n = b.n) : a = b := by
  cases a; cases b; simp only at h2; simp only [mk.injEq]; exact ⟨funext h1, h2⟩

instance : AddCommMonoid (Bd v) where
  add_assoc a b c := ext' (fun l => Nat.max_assoc _ _ _) (Nat.add_assoc _ _ _)
  zero_add a := ext' (fun l => Nat.zero_max _) (Nat.zero_add _)
  add_zero a := ext' (fun l => Nat.max_zero _) (Nat.add_zero _)
  add_comm a b := ext' (fun l => Nat.max_comm _ _) (Nat.add_comm _ _)
  nsmul := nsmulRec

instance : CommMonoid (Bd v) where
  mul_assoc a b c := ext' (fun l => Nat.add_assoc _ _ _) (Nat.mul_assoc _ _ _)
  one_mul a := ext' (fun l => Nat.zero_add _) (Nat.one_mul _)
  mul_one a := ext' (fun l => Nat.add_zero _) (Nat.mul_one _)
  mul_comm a b := ext' (fun l => Nat.add_comm _ _) (Nat.mul_comm _ _)

/-- `b` bounds the polynomial `p`. -/
def Ok (b : Bd v) (p : MP v) : Prop := Maj b.d b.n p

theorem Ok.add {b b' : Bd v} {p q : MP v} (h : b.Ok p) (h' : b'.Ok q) : (b + b').Ok (p + q) :=
  Maj.add h h'
theorem Ok.sub {b b' : Bd v} {p q : MP v} (h : b.Ok p) (h' : b'.Ok q) : (b + b').Ok (p - q) :=
  Maj.sub h h'
theorem Ok.mul {b b' : Bd v} {p q : MP v} (h : b.Ok p) (h' : b'.Ok q) : (b * b').Ok (p * q) :=
  Maj.mul h h'
theorem Ok.neg {b : Bd v} {p : MP v} (h : b.Ok p) : b.Ok (-p) := Maj.neg h
theorem Ok.zero : (0 : Bd v).Ok 0 := Maj.zero
theorem Ok.one : (1 : Bd v).Ok 1 := Maj.one
theorem Ok.mono {b : Bd v} {p : MP v} (h : b.Ok p) (b' : Bd v) (hd : ∀ l, b.d l ≤ b'.d l) (hn : b.n ≤ b'.n) :
    b'.Ok p := Maj.mono h hd hn

theorem Ok.sum {ι : Type*} (s : Finset ι) (b : ι → Bd v) (f : ι → MP v)
    (h : ∀ i ∈ s, (b i).Ok (f i)) : (∑ i ∈ s, b i).Ok (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Ok.zero : (0 : Bd v).Ok 0)
  | insert a s has ih =>
    rw [sum_insert has, sum_insert has]
    exact (h a (mem_insert_self _ _)).add (ih fun i hi => h i (mem_insert_of_mem hi))

theorem Ok.prod {ι : Type*} (s : Finset ι) (b : ι → Bd v) (f : ι → MP v)
    (h : ∀ i ∈ s, (b i).Ok (f i)) : (∏ i ∈ s, b i).Ok (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Ok.one : (1 : Bd v).Ok 1)
  | insert a s has ih =>
    rw [prod_insert has, prod_insert has]
    exact (h a (mem_insert_self _ _)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

end Bd

/-- Entrywise bound of a polynomial matrix. -/
def MOk {v : ℕ} {m n : Type*} (B : Matrix m n (Bd v)) (M : Matrix m n (MP v)) : Prop :=
  ∀ i j, (B i j).Ok (M i j)

theorem MOk.mul {v : ℕ} {l m n : Type*} [Fintype m] {B₁ : Matrix l m (Bd v)} {B₂ : Matrix m n (Bd v)}
    {M₁ : Matrix l m (MP v)} {M₂ : Matrix m n (MP v)} (h₁ : MOk B₁ M₁) (h₂ : MOk B₂ M₂) :
    MOk (B₁ * B₂) (M₁ * M₂) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Bd.Ok.sum _ _ _ fun k _ => (h₁ i k).mul (h₂ k j)

theorem MOk.transpose {v : ℕ} {m n : Type*} {B : Matrix m n (Bd v)} {M : Matrix m n (MP v)}
    (h : MOk B M) : MOk Bᵀ Mᵀ := fun i j => h j i

theorem MOk.submatrix {v : ℕ} {m n m' n' : Type*} {B : Matrix m n (Bd v)} {M : Matrix m n (MP v)}
    (h : MOk B M) (f : m' → m) (g : n' → n) : MOk (B.submatrix f g) (M.submatrix f g) :=
  fun i j => h (f i) (g j)

/-- Bound of a permanent (and, with signs absorbed, of a determinant). -/
def bperm {v : ℕ} {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n (Bd v)) : Bd v :=
  ∑ σ : Perm n, ∏ i, B (σ i) i

theorem MOk.perm {v : ℕ} {n : Type*} [Fintype n] [DecidableEq n] {B : Matrix n n (Bd v)}
    {M : Matrix n n (MP v)} (h : MOk B M) : (bperm B).Ok M.permanent :=
  Bd.Ok.sum _ _ _ fun _ _ => Bd.Ok.prod _ _ _ fun _ _ => h _ _

theorem MOk.det {v : ℕ} {n : Type*} [Fintype n] [DecidableEq n] {B : Matrix n n (Bd v)}
    {M : Matrix n n (MP v)} (h : MOk B M) : (bperm B).Ok M.det := by
  rw [Matrix.det_apply]
  refine Bd.Ok.sum _ _ _ fun σ _ => ?_
  have hp : (∏ i, B (σ i) i).Ok (∏ i, M (σ i) i) := Bd.Ok.prod _ _ _ fun i _ => h _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
  · simpa using hp
  · simpa using hp.neg

/-! ### Bounds for the paper's matrices -/

section Mirror
variable {v : ℕ}

def bnat (k : ℕ) : Bd v := ⟨fun _ => 0, k⟩

theorem Bd.Ok.nat (k : ℕ) : (bnat k : Bd v).Ok (k : MP v) := Maj.nat k

def bF (B : Matrix (Fin 4) (Fin 4) (Bd v)) : Matrix (Fin 4) (Fin 4) (Bd v) :=
  Matrix.of fun i j => B i j * bperm (B.submatrix i.succAbove j.succAbove)

theorem MOk.F {B : Matrix (Fin 4) (Fin 4) (Bd v)} {A : Matrix (Fin 4) (Fin 4) (MP v)}
    (h : MOk B A) : MOk (bF B) (cofactorPermMatrix A) := fun i j => by
  simp only [bF, cofactorPermMatrix, of_apply, permMinor]
  exact (h i j).mul (h.submatrix _ _).perm

theorem MOk.G {B : Matrix (Fin 4) (Fin 4) (Bd v)} {A : Matrix (Fin 4) (Fin 4) (MP v)}
    (h : MOk B A) : MOk (bF B) (signCofactorMatrix A) := fun i j => by
  simp only [bF, signCofactorMatrix, of_apply]
  refine (h i j).mul ?_
  have h1 : (1 : Bd v).Ok ((-1 : MP v) ^ (i.val + j.val)) := by
    have := (Maj.pow (Maj.neg (Maj.one : Maj (fun _ : Fin v => 0) 1 (1 : MP v))) (i.val + j.val))
    exact this.mono (fun l => by simp) (by rw [one_pow]; exact le_rfl)
  have := h1.mul (h.submatrix i.succAbove j.succAbove).det
  rwa [one_mul] at this

def bH (B : Matrix (Fin 4) (Fin 4) (Bd v)) : Matrix (Fin 3) (Fin 3) (Bd v) :=
  Matrix.of fun i j => ∑ g ∈ Finset.univ.filter
    (fun g : Perm (Fin 4) => ∀ x y, pairRel j x y = pairRel i (g x) (g y)), ∏ k, B k (g k)

theorem MOk.H {B : Matrix (Fin 4) (Fin 4) (Bd v)} {A : Matrix (Fin 4) (Fin 4) (MP v)}
    (h : MOk B A) : MOk (bH B) (pairingMatrix A) := fun i j => by
  simp only [bH, pairingMatrix, of_apply, phi]
  exact Bd.Ok.sum _ _ _ fun g _ => Bd.Ok.prod _ _ _ fun k _ => h _ _

def bQ3 : Matrix (Fin 4) (Fin 3) (Bd v) := !![1, 0, 0; 0, 1, 0; 0, 0, 1; 1, 1, 1]
def bQ2 : Matrix (Fin 3) (Fin 2) (Bd v) := !![1, 0; 0, 1; 1, 1]

theorem MOk.Q3 : MOk (bQ3 : Matrix (Fin 4) (Fin 3) (Bd v)) (Q3 : Matrix (Fin 4) (Fin 3) (MP v)) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [bQ3] <;>
    first | exact Bd.Ok.zero | exact Bd.Ok.one | exact Bd.Ok.one.neg

theorem MOk.Q2 : MOk (bQ2 : Matrix (Fin 3) (Fin 2) (Bd v)) (Q2 : Matrix (Fin 3) (Fin 2) (MP v)) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [bQ2] <;>
    first | exact Bd.Ok.zero | exact Bd.Ok.one | exact Bd.Ok.one.neg

def bLam {n : ℕ} (l : Bd v) (F : Matrix (Fin n) (Fin n) (Bd v)) : Matrix (Fin n) (Fin n) (Bd v) :=
  Matrix.of fun i j => (if i = j then l else 0) + F i j

theorem MOk.lam {n : ℕ} {l : Bd v} {lam : MP v} {F : Matrix (Fin n) (Fin n) (Bd v)}
    {F' : Matrix (Fin n) (Fin n) (MP v)} (hl : l.Ok lam) (h : MOk F F') :
    MOk (bLam l F) (lam • (1 : Matrix (Fin n) (Fin n) (MP v)) - F') := fun i j => by
  simp only [bLam, of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · simpa [hij] using hl.sub (h i j)
  · simpa [hij] using (Bd.Ok.zero : (0 : Bd v).Ok 0).sub (h i j)

def bK31 (l : Bd v) (F : Matrix (Fin 4) (Fin 4) (Bd v)) : Matrix (Fin 3) (Fin 3) (Bd v) :=
  bQ3ᵀ * bLam l F * bQ3

def bK22 (l : Bd v) (H : Matrix (Fin 3) (Fin 3) (Bd v)) : Matrix (Fin 2) (Fin 2) (Bd v) :=
  bQ2ᵀ * bLam l H * bQ2

theorem MOk.K31 {l : Bd v} {lam : MP v} {F : Matrix (Fin 4) (Fin 4) (Bd v)}
    {A : Matrix (Fin 4) (Fin 4) (MP v)} (hl : l.Ok lam) (h : MOk F (cofactorPermMatrix A)) :
    MOk (bK31 l F) (K31 lam A) :=
  (MOk.Q3.transpose.mul (MOk.lam hl h)).mul MOk.Q3

theorem MOk.K22 {l : Bd v} {lam : MP v} {F : Matrix (Fin 3) (Fin 3) (Bd v)}
    {A : Matrix (Fin 4) (Fin 4) (MP v)} (hl : l.Ok lam) (h : MOk F (pairingMatrix A)) :
    MOk (bK22 l F) (K22 lam A) :=
  (MOk.Q2.transpose.mul (MOk.lam hl h)).mul MOk.Q2

def be1 (K : Matrix (Fin 3) (Fin 3) (Bd v)) : Bd v := K 0 0 + K 1 1 + K 2 2

theorem MOk.e1 {K : Matrix (Fin 3) (Fin 3) (Bd v)} {K' : Matrix (Fin 3) (Fin 3) (MP v)}
    (h : MOk K K') : (be1 K).Ok (e1 K') := ((h 0 0).add (h 1 1)).add (h 2 2)

def be2 (K : Matrix (Fin 3) (Fin 3) (Bd v)) : Bd v :=
  (K 0 0 * K 1 1 + K 0 1 * K 1 0) + (K 0 0 * K 2 2 + K 0 2 * K 2 0) + (K 1 1 * K 2 2 + K 1 2 * K 2 1)

theorem MOk.e2 {K : Matrix (Fin 3) (Fin 3) (Bd v)} {K' : Matrix (Fin 3) (Fin 3) (MP v)}
    (h : MOk K K') : (be2 K).Ok (e2 K') :=
  ((((h 0 0).mul (h 1 1)).sub ((h 0 1).mul (h 1 0))).add
    (((h 0 0).mul (h 2 2)).sub ((h 0 2).mul (h 2 0)))).add
    (((h 1 1).mul (h 2 2)).sub ((h 1 2).mul (h 2 1)))

def be2four (G : Matrix (Fin 4) (Fin 4) (Bd v)) : Bd v :=
  ∑ i : Fin 4, ∑ j : Fin 4, if i < j then G i i * G j j + G i j * G j i else 0

theorem MOk.e2four {G : Matrix (Fin 4) (Fin 4) (Bd v)} {G' : Matrix (Fin 4) (Fin 4) (MP v)}
    (h : MOk G G') : (be2four G).Ok (e2four G') := by
  unfold be2four _root_.Results.SoulesPotOrderFour.e2four
  refine Bd.Ok.sum _ _ _ fun i _ => Bd.Ok.sum _ _ _ fun j _ => ?_
  split_ifs
  · exact ((h i i).mul (h j j)).sub ((h i j).mul (h j i))
  · exact Bd.Ok.zero

def btrace {n : ℕ} (B : Matrix (Fin n) (Fin n) (Bd v)) : Bd v := ∑ i, B i i

theorem MOk.trace {n : ℕ} {B : Matrix (Fin n) (Fin n) (Bd v)} {M : Matrix (Fin n) (Fin n) (MP v)}
    (h : MOk B M) : (btrace B).Ok M.trace :=
  Bd.Ok.sum _ _ _ fun i _ => h i i

end Mirror

/-! ### Targets and the generic certificate theorem -/

/-- A target polynomial `Φ(A)` of a Gram matrix, with its naturality and its bound pipeline. -/
structure Tgt where
  Φ : (R : Type) → [CommRing R] → Matrix (Fin 4) (Fin 4) R → R
  nat : ∀ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (A : Matrix (Fin 4) (Fin 4) R),
    f (Φ R A) = Φ S (A.map f)
  bd : ∀ {v : ℕ}, Matrix (Fin 4) (Fin 4) (Bd v) → Bd v
  ok : ∀ {v : ℕ} (B : Matrix (Fin 4) (Fin 4) (Bd v)) (A : Matrix (Fin 4) (Fin 4) (MP v)),
    MOk B A → (bd B).Ok (Φ (MP v) A)

theorem cert_poly (T : Tgt) {m v r D bP bS dm dpoly lcm wd vL : ℕ} {blocks : List Blk}
    {poly : List (ℕ × ℤ)} {dP : Fin v → ℕ} {nP : ℕ}
    (Vq Vp : Matrix (Fin r) (Fin 4) (MP v)) (Vqv Vpv : Matrix (Fin r) (Fin 4) Gi)
    (hq : Vq.map (psi D bP) = Vqv) (hp : Vp.map (psi D bP) = Vpv)
    (BV : Matrix (Fin r) (Fin 4) (Bd v)) (hbq : MOk BV Vq) (hbp : MOk BV Vp)
    (hcP : checkP v D bP vL dP nP dpoly poly (T.Φ Gi (Vqvᵀ * Vpv)) = true)
    (hcS : checkS m v D bS dm dpoly lcm wd vL blocks psdBlocks poly = true)
    (hd : ∀ l, (T.bd (BVᵀ * BV)).d l ≤ dP l) (hn : (T.bd (BVᵀ * BV)).n ≤ nP) (t : Fin v → ℝ) :
    0 ≤ (ev t (T.Φ (MP v) (Vqᵀ * Vp))).re := by
  refine cert_core hcP hcS _ ?_ ?_ t
  · rw [T.nat (psi D bP), Matrix.map_mul, Matrix.transpose_map, hq, hp]
  · exact Maj.mono (T.ok _ _ (MOk.mul hbq.transpose hbp)) (fun l => hd l) hn

/-- The chart `V₁` (complex, rank three), over any ring. -/
def chartP {R : Type*} [Add R] [Mul R] [Zero R] [One R] (x a b z c d e f I : R) :
    Matrix (Fin 3) (Fin 4) R :=
  !![1, 1, 1, 1; 0, x, a + b * I, c + d * I; 0, 0, z, e + f * I]

theorem map_chartP {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] (g : R →+* S)
    (x a b z c d e f I : R) :
    (chartP x a b z c d e f I).map g = chartP (g x) (g a) (g b) (g z) (g c) (g d) (g e) (g f) (g I) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [chartP]

theorem chartP_ok {v : ℕ} {bx ba bb bz bc bd be bf bI : Bd v} {x a b z c d e f I : MP v}
    (hx : bx.Ok x) (ha : ba.Ok a) (hb : bb.Ok b) (hz : bz.Ok z) (hc : bc.Ok c) (hd : bd.Ok d)
    (he : be.Ok e) (hf : bf.Ok f) (hI : bI.Ok I) :
    MOk (chartP bx ba bb bz bc bd be bf bI) (chartP x a b z c d e f I) := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact Bd.Ok.one
  · exact Bd.Ok.one
  · exact Bd.Ok.one
  · exact Bd.Ok.one
  · exact Bd.Ok.zero
  · exact hx
  · exact ha.add (hb.mul hI)
  · exact hc.add (hd.mul hI)
  · exact Bd.Ok.zero
  · exact Bd.Ok.zero
  · exact hz
  · exact he.add (hf.mul hI)

/-! ### The chart `V₁` -/

def Xv (v D b : ℕ) (l : Fin v) : Gi := ((p2 (b * D ^ (l : ℕ)) : ℕ) : Gi)

theorem psi_X {v : ℕ} (D b : ℕ) (l : Fin v) : psi D b (MvPolynomial.X l : MP v) = Xv v D b l := by
  simp [psi, Xv]

theorem Gi.toC_I : Gi.toC Gi.I = Complex.I := by simp [Gi.toC, Gi.I]

theorem ev_X {v : ℕ} (t : Fin v → ℝ) (l : Fin v) : ev t (MvPolynomial.X l) = (t l : ℂ) := by
  simp [ev]

theorem ev_I {v : ℕ} (t : Fin v → ℝ) : ev t (MvPolynomial.C Gi.I : MP v) = Complex.I := by
  rw [ev_C, Gi.toC_I]

def bX {v : ℕ} (l : Fin v) : Bd v := ⟨fun l' => if l' = l then 1 else 0, 1⟩

theorem Bd.Ok.X {v : ℕ} (l : Fin v) : (bX l).Ok (MvPolynomial.X l : MP v) := Maj.X l

theorem Bd.Ok.I {v : ℕ} : (1 : Bd v).Ok (MvPolynomial.C Gi.I : MP v) :=
  (Maj.C Gi.I).mono (fun l => le_rfl) (by show nrmG Gi.I ≤ 1; decide)

section V1
open MvPolynomial
noncomputable section

def V1p (I : MP 8) : Matrix (Fin 3) (Fin 4) (MP 8) :=
  chartP (X 0) (X 1) (X 2) (X 3) (X 4) (X 5) (X 6) (X 7) I

def V1v (D b : ℕ) (I : Gi) : Matrix (Fin 3) (Fin 4) Gi :=
  chartP (Xv 8 D b 0) (Xv 8 D b 1) (Xv 8 D b 2) (Xv 8 D b 3) (Xv 8 D b 4) (Xv 8 D b 5) (Xv 8 D b 6) (Xv 8 D b 7) I

def bV1 : Matrix (Fin 3) (Fin 4) (Bd 8) :=
  chartP (bX 0) (bX 1) (bX 2) (bX 3) (bX 4) (bX 5) (bX 6) (bX 7) 1

theorem V1p_psi (D b : ℕ) (I : MP 8) : (V1p I).map (psi D b) = V1v D b (psi D b I) := by
  unfold V1p V1v; rw [map_chartP]; simp only [psi_X]

theorem V1p_ok (I : MP 8) (hI : (1 : Bd 8).Ok I) : MOk bV1 (V1p I) :=
  chartP_ok (Bd.Ok.X _) (Bd.Ok.X _) (Bd.Ok.X _) (Bd.Ok.X _) (Bd.Ok.X _) (Bd.Ok.X _) (Bd.Ok.X _)
    (Bd.Ok.X _) hI

theorem V1p_ev (x a b z c d e f : ℝ) :
    (V1p (C Gi.I)).map (ev ![x, a, b, z, c, d, e, f]) = chartV1 x a b z c d e f := by
  unfold V1p; rw [map_chartP]; simp only [ev_X, ev_I]; rfl

theorem V1p_ev' (x a b z c d e f : ℝ) :
    ((V1p (-C Gi.I)).map (ev ![x, a, b, z, c, d, e, f]))ᵀ = (chartV1 x a b z c d e f)ᴴ := by
  unfold V1p; rw [map_chartP]; simp only [ev_X, map_neg, ev_I]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chartP, chartV1, Matrix.conjTranspose_apply]

theorem cert_V1 (T : Tgt) {m D bP bS dm dpoly lcm wd vL : ℕ} {blocks psdBlocks : List Blk} {poly : List (ℕ × ℤ)} {dP : Fin 8 → ℕ} {nP : ℕ}
    (hcP : checkP 8 D bP vL dP nP dpoly poly (T.Φ Gi ((V1v D bP (-Gi.I))ᵀ * V1v D bP Gi.I)) = true)
    (hcS : checkS m 8 D bS dm dpoly lcm wd vL blocks psdBlocks poly = true)
    (hd : ∀ l, (T.bd (bV1ᵀ * bV1)).d l ≤ dP l) (hn : (T.bd (bV1ᵀ * bV1)).n ≤ nP)
    (x a b' z c d e f : ℝ) :
    0 ≤ (T.Φ ℂ ((chartV1 x a b' z c d e f)ᴴ * chartV1 x a b' z c d e f)).re := by
  have h := cert_poly T (V1p (-C Gi.I)) (V1p (C Gi.I)) _ _ (by rw [V1p_psi]; simp [psi_C])
    (by rw [V1p_psi, psi_C]) bV1 (V1p_ok _ (Bd.Ok.I.neg)) (V1p_ok _ Bd.Ok.I) hcP hcS hd hn
    ![x, a, b', z, c, d, e, f]
  rwa [T.nat (ev ![x, a, b', z, c, d, e, f]), Matrix.map_mul, Matrix.transpose_map, V1p_ev',
    V1p_ev] at h
end
end V1

/-! ### The other charts -/

/-- Zero chart over any ring. -/
def chartPz {R : Type*} [Add R] [Mul R] [Zero R] [One R] (a b c d e f I : R) :
    Matrix (Fin 3) (Fin 4) R :=
  !![1, 0, a, c + d * I; 0, 1, b, e + f * I; 0, 0, 1, 1]

/-- Rank-two chart over any ring. -/
def chartP2 {R : Type*} [Add R] [Mul R] [Zero R] [One R] (r a b c d I : R) :
    Matrix (Fin 2) (Fin 4) R :=
  !![1, 1, 1, 1; 0, r, a + b * I, c + d * I]

/-- Real chart over any ring. -/
def chartPR {R : Type*} [Zero R] [One R] (x y z u v : R) : Matrix (Fin 3) (Fin 4) R :=
  !![1, 1, 1, 1; 0, x, y, u; 0, 0, z, v]

theorem map_chartPz {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] (g : R →+* S)
    (a b c d e f I : R) :
    (chartPz a b c d e f I).map g = chartPz (g a) (g b) (g c) (g d) (g e) (g f) (g I) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [chartPz]

theorem map_chartP2 {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] (g : R →+* S)
    (r a b c d I : R) :
    (chartP2 r a b c d I).map g = chartP2 (g r) (g a) (g b) (g c) (g d) (g I) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [chartP2]

theorem map_chartPR {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] (g : R →+* S)
    (x y z u v : R) :
    (chartPR x y z u v).map g = chartPR (g x) (g y) (g z) (g u) (g v) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [chartPR]

theorem chartPz_ok {v : ℕ} {ba bb bc bd be bf bI : Bd v} {a b c d e f I : MP v}
    (ha : ba.Ok a) (hb : bb.Ok b) (hc : bc.Ok c) (hd : bd.Ok d)
    (he : be.Ok e) (hf : bf.Ok f) (hI : bI.Ok I) :
    MOk (chartPz ba bb bc bd be bf bI) (chartPz a b c d e f I) := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact Bd.Ok.one
  · exact Bd.Ok.zero
  · exact ha
  · exact hc.add (hd.mul hI)
  · exact Bd.Ok.zero
  · exact Bd.Ok.one
  · exact hb
  · exact he.add (hf.mul hI)
  · exact Bd.Ok.zero
  · exact Bd.Ok.zero
  · exact Bd.Ok.one
  · exact Bd.Ok.one

theorem chartP2_ok {v : ℕ} {br ba bb bc bd bI : Bd v} {r a b c d I : MP v}
    (hr : br.Ok r) (ha : ba.Ok a) (hb : bb.Ok b) (hc : bc.Ok c) (hd : bd.Ok d) (hI : bI.Ok I) :
    MOk (chartP2 br ba bb bc bd bI) (chartP2 r a b c d I) := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact Bd.Ok.one
  · exact Bd.Ok.one
  · exact Bd.Ok.one
  · exact Bd.Ok.one
  · exact Bd.Ok.zero
  · exact hr
  · exact ha.add (hb.mul hI)
  · exact hc.add (hd.mul hI)

theorem chartPR_ok {v : ℕ} {bx by' bz bu bv : Bd v} {x y z u w : MP v}
    (hx : bx.Ok x) (hy : by'.Ok y) (hz : bz.Ok z) (hu : bu.Ok u) (hw : bv.Ok w) :
    MOk (chartPR bx by' bz bu bv) (chartPR x y z u w) := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact Bd.Ok.one
  · exact Bd.Ok.one
  · exact Bd.Ok.one
  · exact Bd.Ok.one
  · exact Bd.Ok.zero
  · exact hx
  · exact hy
  · exact hu
  · exact Bd.Ok.zero
  · exact Bd.Ok.zero
  · exact hz
  · exact hw

section Charts
open MvPolynomial
noncomputable section

def Vzp (I : MP 6) : Matrix (Fin 3) (Fin 4) (MP 6) :=
  chartPz (X 0) (X 1) (X 2) (X 3) (X 4) (X 5) I
def Vzv (D b : ℕ) (I : Gi) : Matrix (Fin 3) (Fin 4) Gi :=
  chartPz (Xv 6 D b 0) (Xv 6 D b 1) (Xv 6 D b 2) (Xv 6 D b 3) (Xv 6 D b 4) (Xv 6 D b 5) I
def bVz : Matrix (Fin 3) (Fin 4) (Bd 6) :=
  chartPz (bX 0) (bX 1) (bX 2) (bX 3) (bX 4) (bX 5) 1

theorem Vzp_psi (D b : ℕ) (I : MP 6) : (Vzp I).map (psi D b) = Vzv D b (psi D b I) := by
  unfold Vzp Vzv; rw [map_chartPz]; simp only [psi_X]

theorem Vzp_ok (I : MP 6) (hI : (1 : Bd 6).Ok I) : MOk bVz (Vzp I) :=
  chartPz_ok (Bd.Ok.X _) (Bd.Ok.X _) (Bd.Ok.X _) (Bd.Ok.X _) (Bd.Ok.X _) (Bd.Ok.X _) hI

theorem Vzp_ev (a b c d e f : ℝ) :
    (Vzp (C Gi.I)).map (ev ![a, b, c, d, e, f]) = chartVz a b c d e f := by
  unfold Vzp; rw [map_chartPz]; simp only [ev_X, ev_I]; rfl

theorem Vzp_ev' (a b c d e f : ℝ) :
    ((Vzp (-C Gi.I)).map (ev ![a, b, c, d, e, f]))ᵀ = (chartVz a b c d e f)ᴴ := by
  unfold Vzp; rw [map_chartPz]; simp only [ev_X, map_neg, ev_I]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chartPz, chartVz, Matrix.conjTranspose_apply]

theorem cert_Vz (T : Tgt) {m D bP bS dm dpoly lcm wd vL : ℕ} {blocks psdBlocks : List Blk} {poly : List (ℕ × ℤ)} {dP : Fin 6 → ℕ} {nP : ℕ}
    (hcP : checkP 6 D bP vL dP nP dpoly poly (T.Φ Gi ((Vzv D bP (-Gi.I))ᵀ * Vzv D bP Gi.I)) = true)
    (hcS : checkS m 6 D bS dm dpoly lcm wd vL blocks psdBlocks poly = true)
    (hd : ∀ l, (T.bd (bVzᵀ * bVz)).d l ≤ dP l) (hn : (T.bd (bVzᵀ * bVz)).n ≤ nP)
    (a b' c d e f : ℝ) :
    0 ≤ (T.Φ ℂ ((chartVz a b' c d e f)ᴴ * chartVz a b' c d e f)).re := by
  have h := cert_poly T (Vzp (-C Gi.I)) (Vzp (C Gi.I)) _ _ (by rw [Vzp_psi]; simp [psi_C])
    (by rw [Vzp_psi, psi_C]) bVz (Vzp_ok _ (Bd.Ok.I.neg)) (Vzp_ok _ Bd.Ok.I) hcP hcS hd hn
    ![a, b', c, d, e, f]
  rwa [T.nat (ev ![a, b', c, d, e, f]), Matrix.map_mul, Matrix.transpose_map, Vzp_ev',
    Vzp_ev] at h

def V2p (I : MP 5) : Matrix (Fin 2) (Fin 4) (MP 5) :=
  chartP2 (X 0) (X 1) (X 2) (X 3) (X 4) I
def V2v (D b : ℕ) (I : Gi) : Matrix (Fin 2) (Fin 4) Gi :=
  chartP2 (Xv 5 D b 0) (Xv 5 D b 1) (Xv 5 D b 2) (Xv 5 D b 3) (Xv 5 D b 4) I
def bV2 : Matrix (Fin 2) (Fin 4) (Bd 5) :=
  chartP2 (bX 0) (bX 1) (bX 2) (bX 3) (bX 4) 1

theorem V2p_psi (D b : ℕ) (I : MP 5) : (V2p I).map (psi D b) = V2v D b (psi D b I) := by
  unfold V2p V2v; rw [map_chartP2]; simp only [psi_X]

theorem V2p_ok (I : MP 5) (hI : (1 : Bd 5).Ok I) : MOk bV2 (V2p I) :=
  chartP2_ok (Bd.Ok.X _) (Bd.Ok.X _) (Bd.Ok.X _) (Bd.Ok.X _) (Bd.Ok.X _) hI

theorem V2p_ev (r a b c d : ℝ) :
    (V2p (C Gi.I)).map (ev ![r, a, b, c, d]) = chartV2 r a b c d := by
  unfold V2p; rw [map_chartP2]; simp only [ev_X, ev_I]; rfl

theorem V2p_ev' (r a b c d : ℝ) :
    ((V2p (-C Gi.I)).map (ev ![r, a, b, c, d]))ᵀ = (chartV2 r a b c d)ᴴ := by
  unfold V2p; rw [map_chartP2]; simp only [ev_X, map_neg, ev_I]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chartP2, chartV2, Matrix.conjTranspose_apply]

theorem cert_V2 (T : Tgt) {m D bP bS dm dpoly lcm wd vL : ℕ} {blocks psdBlocks : List Blk} {poly : List (ℕ × ℤ)} {dP : Fin 5 → ℕ} {nP : ℕ}
    (hcP : checkP 5 D bP vL dP nP dpoly poly (T.Φ Gi ((V2v D bP (-Gi.I))ᵀ * V2v D bP Gi.I)) = true)
    (hcS : checkS m 5 D bS dm dpoly lcm wd vL blocks psdBlocks poly = true)
    (hd : ∀ l, (T.bd (bV2ᵀ * bV2)).d l ≤ dP l) (hn : (T.bd (bV2ᵀ * bV2)).n ≤ nP)
    (r a b' c d : ℝ) :
    0 ≤ (T.Φ ℂ ((chartV2 r a b' c d)ᴴ * chartV2 r a b' c d)).re := by
  have h := cert_poly T (V2p (-C Gi.I)) (V2p (C Gi.I)) _ _ (by rw [V2p_psi]; simp [psi_C])
    (by rw [V2p_psi, psi_C]) bV2 (V2p_ok _ (Bd.Ok.I.neg)) (V2p_ok _ Bd.Ok.I) hcP hcS hd hn
    ![r, a, b', c, d]
  rwa [T.nat (ev ![r, a, b', c, d]), Matrix.map_mul, Matrix.transpose_map, V2p_ev',
    V2p_ev] at h

def VRp : Matrix (Fin 3) (Fin 4) (MP 5) := chartPR (X 0) (X 1) (X 2) (X 3) (X 4)
def VRv (D b : ℕ) : Matrix (Fin 3) (Fin 4) Gi :=
  chartPR (Xv 5 D b 0) (Xv 5 D b 1) (Xv 5 D b 2) (Xv 5 D b 3) (Xv 5 D b 4)
def bVR : Matrix (Fin 3) (Fin 4) (Bd 5) := chartPR (bX 0) (bX 1) (bX 2) (bX 3) (bX 4)

theorem VRp_psi (D b : ℕ) : VRp.map (psi D b) = VRv D b := by
  unfold VRp VRv; rw [map_chartPR]; simp only [psi_X]

theorem VRp_ok : MOk bVR VRp :=
  chartPR_ok (Bd.Ok.X _) (Bd.Ok.X _) (Bd.Ok.X _) (Bd.Ok.X _) (Bd.Ok.X _)

theorem VRp_ev (x y z u v : ℝ) :
    VRp.map (ev ![x, y, z, u, v]) = (chartVR x y z u v).map ((↑) : ℝ → ℂ) := by
  unfold VRp; rw [map_chartPR]; simp only [ev_X]
  ext i j; fin_cases i <;> fin_cases j <;> simp [chartPR, chartVR]

theorem cert_VR (T : Tgt) {m D bP bS dm dpoly lcm wd vL : ℕ} {blocks psdBlocks : List Blk} {poly : List (ℕ × ℤ)} {dP : Fin 5 → ℕ} {nP : ℕ}
    (hcP : checkP 5 D bP vL dP nP dpoly poly (T.Φ Gi ((VRv D bP)ᵀ * VRv D bP)) = true)
    (hcS : checkS m 5 D bS dm dpoly lcm wd vL blocks psdBlocks poly = true)
    (hd : ∀ l, (T.bd (bVRᵀ * bVR)).d l ≤ dP l) (hn : (T.bd (bVRᵀ * bVR)).n ≤ nP)
    (x y z u v : ℝ) :
    0 ≤ T.Φ ℝ ((chartVR x y z u v)ᵀ * chartVR x y z u v) := by
  have h := cert_poly T VRp VRp _ _ (VRp_psi D bP) (VRp_psi D bP) bVR VRp_ok VRp_ok hcP hcS hd hn
    ![x, y, z, u, v]
  have e1 : (VRp.map (ev ![x, y, z, u, v]))ᵀ * VRp.map (ev ![x, y, z, u, v]) =
      ((chartVR x y z u v)ᵀ * chartVR x y z u v).map Complex.ofRealHom := by
    rw [VRp_ev, Matrix.map_mul, Matrix.transpose_map]; rfl
  rw [T.nat (ev ![x, y, z, u, v]), Matrix.map_mul, Matrix.transpose_map, e1,
    ← T.nat Complex.ofRealHom] at h
  simpa using h

end
end Charts

/-! ### The targets -/

section Targets
variable {v : ℕ}

theorem Bd.Ok.natC (k : ℕ) [k.AtLeastTwo] : (bnat k : Bd v).Ok (OfNat.ofNat k : MP v) := by
  have := Bd.Ok.nat (v := v) k
  rwa [← Nat.cast_ofNat (R := MP v) (n := k)] at *

/-- `det K₃₁` -/
def tDet31 : Tgt where
  Φ := fun _ _ A => (K31 A.permanent A).det
  nat := fun f A => by
    show _ = _; rw [map_det' f, map_K31 f, map_permanent f]
  bd := fun B => bperm (bK31 (bperm B) (bF B))
  ok := fun B A h => (MOk.K31 h.perm (MOk.F h)).det

/-- `tr K₃₁` -/
def tTr31 : Tgt where
  Φ := fun _ _ A => e1 (K31 A.permanent A)
  nat := fun f A => by
    show _ = _; rw [map_e1 f, map_K31 f, map_permanent f]
  bd := fun B => be1 (bK31 (bperm B) (bF B))
  ok := fun B A h => (MOk.K31 h.perm (MOk.F h)).e1

/-- `e₂ K₃₁` -/
def tE2 : Tgt where
  Φ := fun _ _ A => e2 (K31 A.permanent A)
  nat := fun f A => by
    show _ = _; rw [map_e2 f, map_K31 f, map_permanent f]
  bd := fun B => be2 (bK31 (bperm B) (bF B))
  ok := fun B A h => (MOk.K31 h.perm (MOk.F h)).e2

/-- `tr K₂₂` -/
def tTr22 : Tgt where
  Φ := fun _ _ A => Matrix.trace (K22 A.permanent A)
  nat := fun f A => by
    show _ = _; rw [map_trace' f, map_K22 f, map_permanent f]
  bd := fun B => btrace (bK22 (bperm B) (bH B))
  ok := fun B A h => (MOk.K22 h.perm (MOk.H h)).trace

/-- `det K₂₂` -/
def tDet22 : Tgt where
  Φ := fun _ _ A => (K22 A.permanent A).det
  nat := fun f A => by
    show _ = _; rw [map_det' f, map_K22 f, map_permanent f]
  bd := fun B => bperm (bK22 (bperm B) (bH B))
  ok := fun B A h => (MOk.K22 h.perm (MOk.H h)).det

/-- `8 p - 5 T` -/
def t8p5T : Tgt where
  Φ := fun _ _ A => 8 * A.permanent - 5 * Matrix.trace (signCofactorMatrix A)
  nat := fun f A => by
    simp only [map_sub, map_mul, map_ofNat, map_permanent f, map_trace' f, map_G f]
  bd := fun B => bnat 8 * bperm B + bnat 5 * btrace (bF B)
  ok := fun B A h => ((Bd.Ok.natC 8).mul h.perm).sub ((Bd.Ok.natC 5).mul (MOk.G h).trace)

/-- `3p² - 2pT - T² + 4E` -/
def tMoment : Tgt where
  Φ := fun _ _ A => 3 * A.permanent ^ 2 - 2 * A.permanent * Matrix.trace (signCofactorMatrix A)
    - Matrix.trace (signCofactorMatrix A) ^ 2 + 4 * e2four (signCofactorMatrix A)
  nat := fun f A => by
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_permanent f, map_trace' f,
      map_G f, map_e2four f]
  bd := fun B => bnat 3 * (bperm B * bperm B) + (bnat 2 * bperm B) * btrace (bF B) +
    btrace (bF B) * btrace (bF B) + bnat 4 * be2four (bF B)
  ok := fun B A h => by
    have hp := h.perm
    have hT := (MOk.G h).trace
    have hE := (MOk.G h).e2four
    simp only [pow_two]
    exact ((((Bd.Ok.natC 3).mul (hp.mul hp)).sub (((Bd.Ok.natC 2).mul hp).mul hT)).sub
      (hT.mul hT)).add ((Bd.Ok.natC 4).mul hE)

end Targets

end Kron
end Results.SoulesPotOrderFour

/-- `cert_checkS name m k v D b dm dpoly lcm wd vL blocks psdBlocks poly` proves
`name : checkS m v D b dm dpoly lcm wd vL blocks psdBlocks poly = true` by separate kernel calls (each in
its own theorem, so that every call has its own memory and heartbeat budget): the side conditions
(`name_a`), each of the `m` slice chunks (`name_s0`, ...) and the positivity of each of the `k` Gram blocks
(`name_p0`, ...). -/
syntax (name := certCheckS) "cert_checkS " ident num num term:max term:max term:max term:max term:max
  term:max term:max term:max term:max term:max term:max : command

open Lean in
macro_rules
  | `(cert_checkS $nm:ident $m:num $k:num $v $D $b $dm $dpoly $lcm $wd $vL $blocks $psd $poly) => do
    let mut cmds : Array (TSyntax `command) := #[]
    let nmA := mkIdent (nm.getId.appendAfter "_a")
    cmds := cmds.push (← `(theorem $nmA : Results.SoulesPotOrderFour.Kron.checkSa $v $D $b $dm $dpoly
      $lcm $blocks $psd $poly = true := by decide +kernel))
    let mut sPf ← `(Results.SoulesPotOrderFour.Kron.forall_lt_zero)
    for c in List.range m.getNat do
      let nmC := mkIdent (nm.getId.appendAfter s!"_s{c}")
      cmds := cmds.push (← `(theorem $nmC : Results.SoulesPotOrderFour.Kron.sliceOK $m
        $(Syntax.mkNumLit (toString c)) ($D ^ $vL) $b $lcm $blocks $poly = true := by decide +kernel))
      sPf ← `(Results.SoulesPotOrderFour.Kron.forall_lt_succ $sPf $nmC)
    let mut pPf ← `(Results.SoulesPotOrderFour.Kron.forall_lt_zero)
    for i in List.range k.getNat do
      let nmP := mkIdent (nm.getId.appendAfter s!"_p{i}")
      cmds := cmds.push (← `(theorem $nmP : (List.getD $psd $(Syntax.mkNumLit (toString i)) default).psdOK
        $wd = true := by decide +kernel))
      pPf ← `(Results.SoulesPotOrderFour.Kron.forall_lt_succ $pPf $nmP)
    cmds := cmds.push (← `(theorem $nm : Results.SoulesPotOrderFour.Kron.checkS $m $v $D $b $dm $dpoly
      $lcm $wd $vL $blocks $psd $poly = true :=
      Results.SoulesPotOrderFour.Kron.checkS_of_parts (k := $k) (by decide) $nmA $sPf (by decide +kernel) $pPf))
    return mkNullNode (cmds.map (·.raw))
