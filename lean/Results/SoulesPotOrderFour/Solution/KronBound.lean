import Results.SoulesPotOrderFour.Solution.KronPipe

open Finset Matrix Equiv

/-!
# The `19/18` quadratic form in 14 variables

`Kb A = Q₃ᵀ (19 p - 18 F) Q₃ = 18 K₃₁((19/18) p, A)`.  With `y = q + i q'` the form `Θ = ȳᵀ Kb y` is a polynomial
in the 14 real variables (8 of the chart, 6 for `y`).  Its Kronecker value is assembled from the 36 `q`-channels
of the entries of `Kb A` (`chanRe`, `chanIm`, `psi_Theta`), so only 8-variable values are computed
(`checkPq`); `cert_bound_core` then gives `0 ≤ Re (y* K₃₁((19/18) p) y)`.
-/

namespace Results.SoulesPotOrderFour
namespace Kron

section Kbound
variable {R S : Type*} [CommRing R] [CommRing S]

/-- `18 · K₃₁((19/18) p)`: the matrix of the `19/18` bound, scaled to integer coefficients. -/
def Kb (A : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 3) (Fin 3) R :=
  (Q3 : Matrix (Fin 4) (Fin 3) R)ᵀ * (((19 : R) * A.permanent) • (1 : Matrix (Fin 4) (Fin 4) R) -
    (18 : R) • cofactorPermMatrix A) * Q3

theorem map_Kb (f : R →+* S) (A : Matrix (Fin 4) (Fin 4) R) : (Kb A).map f = Kb (A.map f) := by
  unfold Kb
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, map_Q3]
  congr 2
  ext i j
  have hF := congrFun (congrFun (map_F f A) i) j
  simp only [Matrix.map_apply] at hF
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    map_sub, map_mul, map_ofNat, hF, map_permanent f A]
  split_ifs <;> simp

theorem K31_eq_Kb (A : Matrix (Fin 4) (Fin 4) ℂ) :
    K31 ((19 / 18 : ℂ) * A.permanent) A = (1 / 18 : ℂ) • Kb A := by
  unfold K31 Kb
  rw [← Matrix.smul_mul, ← Matrix.mul_smul]
  congr 2
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> ring

end Kbound


section Mirror
variable {v : ℕ}

def bKb (B : Matrix (Fin 4) (Fin 4) (Bd v)) : Matrix (Fin 3) (Fin 3) (Bd v) :=
  bQ3ᵀ * bLam (bnat 19 * bperm B) (Matrix.of fun i j => bnat 18 * bF B i j) * bQ3

theorem MOk.Kb {B : Matrix (Fin 4) (Fin 4) (Bd v)} {A : Matrix (Fin 4) (Fin 4) (MP v)}
    (h : MOk B A) : MOk (bKb B) (Kb A) := by
  have hF : MOk (Matrix.of fun i j => bnat 18 * bF B i j) ((18 : MP v) • cofactorPermMatrix A) :=
    fun i j => by simpa using (Bd.Ok.natC 18).mul ((MOk.F h) i j)
  exact (MOk.Q3.transpose.mul (MOk.lam ((Bd.Ok.natC 19).mul h.perm) hF)).mul MOk.Q3

end Mirror

/-! ### The `ȳᵀ K y` form in 14 variables -/

section Theta
open MvPolynomial
noncomputable section

@[simp] theorem Gi.I_re : Gi.I.re = 0 := rfl
@[simp] theorem Gi.I_im : Gi.I.im = 1 := rfl

/-- `y_k = q_k + I q_{k+3}` as a polynomial in the variables `8 .. 13`. -/
def yp14 (I : MP 14) (k : Fin 3) : MP 14 := X ⟨8 + k.val, by omega⟩ + I * X ⟨11 + k.val, by omega⟩

def Theta (K : Matrix (Fin 3) (Fin 3) (MP 14)) : MP 14 :=
  yp14 (-C Gi.I) ⬝ᵥ (K *ᵥ yp14 (C Gi.I))

def ygv (b : ℕ) (I : Gi) (k : Fin 3) : Gi :=
  Xv 14 3 b ⟨8 + k.val, by omega⟩ + I * Xv 14 3 b ⟨11 + k.val, by omega⟩

theorem psi_yp14 (b : ℕ) (I : MP 14) (k : Fin 3) : psi 3 b (yp14 I k) = ygv b (psi 3 b I) k := by
  simp [yp14, ygv, psi_X]

/-- the four real (`chanE`) and imaginary (`chanF`) channel terms of the entry `a + b i` of `K` at `(i, j)` -/
def chanE (i j : ℕ) (a b : ℤ) : List (ℕ × ℤ) :=
  [(3 ^ i + 3 ^ j, a), (3 ^ (i + 3) + 3 ^ (j + 3), a), (3 ^ i + 3 ^ (j + 3), -b), (3 ^ (i + 3) + 3 ^ j, b)]

def chanF (i j : ℕ) (a b : ℤ) : List (ℕ × ℤ) :=
  [(3 ^ i + 3 ^ j, b), (3 ^ (i + 3) + 3 ^ (j + 3), b), (3 ^ i + 3 ^ (j + 3), a), (3 ^ (i + 3) + 3 ^ j, -a)]

def chanRe (Kv : Matrix (Fin 3) (Fin 3) Gi) : List (ℕ × ℤ) :=
  chanE 0 0 (Kv 0 0).re (Kv 0 0).im ++ chanE 0 1 (Kv 0 1).re (Kv 0 1).im ++
  chanE 0 2 (Kv 0 2).re (Kv 0 2).im ++ chanE 1 0 (Kv 1 0).re (Kv 1 0).im ++
  chanE 1 1 (Kv 1 1).re (Kv 1 1).im ++ chanE 1 2 (Kv 1 2).re (Kv 1 2).im ++
  chanE 2 0 (Kv 2 0).re (Kv 2 0).im ++ chanE 2 1 (Kv 2 1).re (Kv 2 1).im ++
  chanE 2 2 (Kv 2 2).re (Kv 2 2).im

def chanIm (Kv : Matrix (Fin 3) (Fin 3) Gi) : List (ℕ × ℤ) :=
  chanF 0 0 (Kv 0 0).re (Kv 0 0).im ++ chanF 0 1 (Kv 0 1).re (Kv 0 1).im ++
  chanF 0 2 (Kv 0 2).re (Kv 0 2).im ++ chanF 1 0 (Kv 1 0).re (Kv 1 0).im ++
  chanF 1 1 (Kv 1 1).re (Kv 1 1).im ++ chanF 1 2 (Kv 1 2).re (Kv 1 2).im ++
  chanF 2 0 (Kv 2 0).re (Kv 2 0).im ++ chanF 2 1 (Kv 2 1).re (Kv 2 1).im ++
  chanF 2 2 (Kv 2 2).re (Kv 2 2).im

/-- aggregation of an unsorted list of `(σ, x)` by merging singletons -/
def aggL (l : List (ℕ × ℤ)) : List (ℕ × ℤ) := mergeTree (l.length + 1) (l.map (fun p => [p]))

theorem evalSl_aggL (K b : ℕ) (l : List (ℕ × ℤ)) : evalSl K b (aggL l) = evalSl K b l := by
  unfold aggL
  rw [evalSl_mergeTree]
  unfold evalSlL evalSl
  rw [List.map_map]
  simp [Function.comp_def]

theorem two_pow_chan (b m n : ℕ) :
    (2 : ℤ) ^ (b * (3 ^ 8 * (3 ^ m + 3 ^ n))) = 2 ^ (b * 3 ^ (8 + m)) * 2 ^ (b * 3 ^ (8 + n)) := by
  rw [← pow_add]; congr 1; ring

theorem evalSl_chanE (b : ℕ) (i j : ℕ) (a b' : ℤ) :
    evalSl (3 ^ 8) b (chanE i j a b') =
      a * ((2 : ℤ) ^ (b * 3 ^ (8 + i)) * 2 ^ (b * 3 ^ (8 + j)) +
        2 ^ (b * 3 ^ (8 + (i + 3))) * 2 ^ (b * 3 ^ (8 + (j + 3)))) -
      b' * (2 ^ (b * 3 ^ (8 + i)) * 2 ^ (b * 3 ^ (8 + (j + 3))) -
        2 ^ (b * 3 ^ (8 + (i + 3))) * 2 ^ (b * 3 ^ (8 + j))) := by
  simp only [chanE, evalSl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    two_pow_chan]
  ring

theorem evalSl_chanF (b : ℕ) (i j : ℕ) (a b' : ℤ) :
    evalSl (3 ^ 8) b (chanF i j a b') =
      b' * ((2 : ℤ) ^ (b * 3 ^ (8 + i)) * 2 ^ (b * 3 ^ (8 + j)) +
        2 ^ (b * 3 ^ (8 + (i + 3))) * 2 ^ (b * 3 ^ (8 + (j + 3)))) +
      a * (2 ^ (b * 3 ^ (8 + i)) * 2 ^ (b * 3 ^ (8 + (j + 3))) -
        2 ^ (b * 3 ^ (8 + (i + 3))) * 2 ^ (b * 3 ^ (8 + j))) := by
  simp only [chanF, evalSl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    two_pow_chan]
  ring

theorem evalSl_append (K b : ℕ) (l1 l2 : List (ℕ × ℤ)) :
    evalSl K b (l1 ++ l2) = evalSl K b l1 + evalSl K b l2 := by
  simp [evalSl]

theorem psi_Theta (b : ℕ) (Kp : Matrix (Fin 3) (Fin 3) (MP 14)) :
    psi 3 b (Theta Kp) = ⟨evalSl (3 ^ 8) b (chanRe (Kp.map (psi 3 b))),
      evalSl (3 ^ 8) b (chanIm (Kp.map (psi 3 b)))⟩ := by
  unfold Theta
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, map_add, map_mul, map_neg,
    psi_yp14, psi_C]
  unfold chanRe chanIm
  simp only [evalSl_append, evalSl_chanE, evalSl_chanF]
  refine Gi.ext ?_ ?_ <;>
  · simp only [ygv, Xv, Gi.add_re, Gi.add_im, Gi.mul_re, Gi.mul_im, Gi.neg_re, Gi.neg_im,
      Gi.natCast_re, Gi.natCast_im, Gi.I_re, Gi.I_im, p2_eq, Matrix.map_apply, Fin.val_zero,
      Fin.val_one, Fin.val_two]
    push_cast
    ring


/-! ### The polynomial side of the check -/

/-- The check of the target polynomial against the channel representation of `Θ = ȳᵀ K y`. -/
def checkPq (b : ℕ) (dP : Fin 14 → ℕ) (nP dpoly : ℕ) (poly : List (ℕ × ℤ))
    (Kv : Matrix (Fin 3) (Fin 3) Gi) : Bool :=
  decide (1 ≤ b ∧ (∀ l, dP l < 3) ∧ dpoly < 3) &&
  decide (nzL (aggL (chanIm Kv)) = [] ∧
    nzL (aggL (chanRe Kv)) = nzL (polySlices (3 ^ 8) b 1 poly)) &&
  decide ((nP + Poly.l1 poly) * 2 < 2 ^ b) &&
  (Poly.terms poly).all (fun t => decide (t.1 < 3 ^ 14) &&
    (List.range 14).all (fun l => decide (digit 3 t.1 l ≤ dpoly)))

theorem Poly.facts_of_checkq {b nP dpoly : ℕ} {dP : Fin 14 → ℕ} {poly : List (ℕ × ℤ)}
    {Kv : Matrix (Fin 3) (Fin 3) Gi} (hc : checkPq b dP nP dpoly poly Kv = true) :
    (∀ t ∈ Poly.terms poly, t.1 < 3 ^ 14) ∧
      (∀ t ∈ Poly.terms poly, ∀ l : Fin 14, digit 3 t.1 l ≤ dpoly) := by
  unfold checkPq at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨_, hterms⟩ := hc
  exact ⟨fun t ht => (hterms t ht).1, fun t ht l => (hterms t ht).2 l (List.mem_range.mpr l.2)⟩

theorem Poly.eq_of_checkq {b nP dpoly : ℕ} {dP : Fin 14 → ℕ} {poly : List (ℕ × ℤ)}
    {Kv : Matrix (Fin 3) (Fin 3) Gi} (hc : checkPq b dP nP dpoly poly Kv = true) (P : MP 14)
    (hψ : psi 3 b P = ⟨evalSl (3 ^ 8) b (chanRe Kv), evalSl (3 ^ 8) b (chanIm Kv)⟩)
    (hM : Maj dP nP P) : P = Poly.pol 3 14 poly := by
  obtain ⟨hk, hdig⟩ := Poly.facts_of_checkq hc
  unfold checkPq at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨hb, hdP, hdp⟩, him, hre⟩, hnorm⟩, _⟩ := hc
  have hpol := Poly.pol_maj 3 dpoly poly hdig
  have hh : Maj (fun l => max (dP l) dpoly) (nP + Poly.l1 poly) (P - Poly.pol 3 14 poly) :=
    hM.sub hpol
  have hz : P - Poly.pol 3 14 poly = 0 := by
    refine psi_inj (D := 3) (b := b) (by norm_num) hb _ (fun l => ?_) ?_ ?_
    · exact lt_of_le_of_lt (hh.1 l) (max_lt (hdP l) hdp)
    · exact lt_of_le_of_lt (Nat.mul_le_mul_right 2 hh.2) hnorm
    · have h1 := evalSl_polySlices (3 ^ 8) b 1 poly
      have hre' : evalSl (3 ^ 8) b (chanRe Kv) = evalSl (3 ^ 8) b (polySlices (3 ^ 8) b 1 poly) := by
        rw [← evalSl_aggL, ← evalSl_nzL, hre, evalSl_nzL]
      have him' : evalSl (3 ^ 8) b (chanIm Kv) = 0 := by
        rw [← evalSl_aggL, ← evalSl_nzL, him]; rfl
      rw [map_sub, hψ, Poly.psi_pol 3 b poly hk]
      refine Gi.ext ?_ ?_
      · simp only [Gi.sub_re, Gi.intCast_re, Gi.zero_re]
        rw [hre', h1]; simp
      · simp only [Gi.sub_im, Gi.intCast_im, Gi.zero_im]
        rw [him']; simp
  exact sub_eq_zero.mp hz

/-! ### Bounds for `Θ` -/

def byp (k : Fin 3) : Bd 14 := bX ⟨8 + k.val, by omega⟩ + 1 * bX ⟨11 + k.val, by omega⟩

theorem yp14_ok (I : MP 14) (hI : (1 : Bd 14).Ok I) (k : Fin 3) : (byp k).Ok (yp14 I k) :=
  (Bd.Ok.X _).add (hI.mul (Bd.Ok.X _))

def bTheta (B : Matrix (Fin 3) (Fin 3) (Bd 14)) : Bd 14 :=
  ∑ i, byp i * ∑ j, B i j * byp j

theorem Theta_ok {B : Matrix (Fin 3) (Fin 3) (Bd 14)} {K : Matrix (Fin 3) (Fin 3) (MP 14)}
    (h : MOk B K) : (bTheta B).Ok (Theta K) := by
  unfold Theta bTheta
  simp only [dotProduct, Matrix.mulVec]
  exact Bd.Ok.sum _ _ _ fun i _ => (yp14_ok _ Bd.Ok.I.neg i).mul
    (Bd.Ok.sum _ _ _ fun j _ => (h i j).mul (yp14_ok _ Bd.Ok.I j))

/-! ### The chart in 14 variables -/

def V1q (I : MP 14) : Matrix (Fin 3) (Fin 4) (MP 14) :=
  chartP (X 0) (X 1) (X 2) (X 3) (X 4) (X 5) (X 6) (X 7) I

def V1v14 (D b : ℕ) (I : Gi) : Matrix (Fin 3) (Fin 4) Gi :=
  chartP (Xv 14 D b 0) (Xv 14 D b 1) (Xv 14 D b 2) (Xv 14 D b 3) (Xv 14 D b 4) (Xv 14 D b 5)
    (Xv 14 D b 6) (Xv 14 D b 7) I

def bV14 : Matrix (Fin 3) (Fin 4) (Bd 14) :=
  chartP (bX 0) (bX 1) (bX 2) (bX 3) (bX 4) (bX 5) (bX 6) (bX 7) 1

theorem V1q_psi (D b : ℕ) (I : MP 14) : (V1q I).map (psi D b) = V1v14 D b (psi D b I) := by
  unfold V1q V1v14; rw [map_chartP]; simp only [psi_X]

theorem V1q_ok (I : MP 14) (hI : (1 : Bd 14).Ok I) : MOk bV14 (V1q I) :=
  chartP_ok (Bd.Ok.X _) (Bd.Ok.X _) (Bd.Ok.X _) (Bd.Ok.X _) (Bd.Ok.X _) (Bd.Ok.X _) (Bd.Ok.X _)
    (Bd.Ok.X _) hI

/-- the 14 real parameters -/
def zz14 (x a b z c d e f q0 q1 q2 q3 q4 q5 : ℝ) : Fin 14 → ℝ :=
  ![x, a, b, z, c, d, e, f, q0, q1, q2, q3, q4, q5]

theorem V1q_ev (x a b z c d e f q0 q1 q2 q3 q4 q5 : ℝ) :
    (V1q (C Gi.I)).map (ev (zz14 x a b z c d e f q0 q1 q2 q3 q4 q5)) = chartV1 x a b z c d e f := by
  unfold V1q; rw [map_chartP]; simp only [ev_X, ev_I]; rfl

theorem V1q_ev' (x a b z c d e f q0 q1 q2 q3 q4 q5 : ℝ) :
    ((V1q (-C Gi.I)).map (ev (zz14 x a b z c d e f q0 q1 q2 q3 q4 q5)))ᵀ = (chartV1 x a b z c d e f)ᴴ := by
  unfold V1q; rw [map_chartP]; simp only [ev_X, map_neg, ev_I]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chartP, chartV1, Matrix.conjTranspose_apply, zz14]

theorem ev_Theta (zz : Fin 14 → ℝ) (K : Matrix (Fin 3) (Fin 3) (MP 14)) :
    ev zz (Theta K) = (fun k => ev zz (yp14 (-C Gi.I) k)) ⬝ᵥ
      ((K.map (ev zz)) *ᵥ (fun k => ev zz (yp14 (C Gi.I) k))) := by
  unfold Theta
  simp [dotProduct, Matrix.mulVec, map_sum, map_mul]

theorem ev_yp14 (x a b z c d e f q0 q1 q2 q3 q4 q5 : ℝ) :
    (fun k => ev (zz14 x a b z c d e f q0 q1 q2 q3 q4 q5) (yp14 (C Gi.I) k)) =
      ![(q0 : ℂ) + (q3 : ℂ) * Complex.I, (q1 : ℂ) + (q4 : ℂ) * Complex.I,
        (q2 : ℂ) + (q5 : ℂ) * Complex.I] := by
  ext k
  fin_cases k <;> simp [yp14, ev_X, ev_I, zz14] <;> ring

theorem ev_yp14' (x a b z c d e f q0 q1 q2 q3 q4 q5 : ℝ) :
    (fun k => ev (zz14 x a b z c d e f q0 q1 q2 q3 q4 q5) (yp14 (-C Gi.I) k)) =
      star ![(q0 : ℂ) + (q3 : ℂ) * Complex.I, (q1 : ℂ) + (q4 : ℂ) * Complex.I,
        (q2 : ℂ) + (q5 : ℂ) * Complex.I] := by
  ext k
  fin_cases k <;> simp [yp14, ev_X, ev_I, zz14] <;> ring


theorem cert_bound_core {m bP bS dm dpoly lcm wd nP : ℕ} {blocks psdBlocks : List Blk}
    {poly : List (ℕ × ℤ)}
    (hcP : checkPq bP (fun _ => 2) nP dpoly poly
      (Kb ((V1v14 3 bP (-Gi.I))ᵀ * V1v14 3 bP Gi.I)) = true)
    (hcS : checkS m 14 3 bS dm dpoly lcm wd 8 blocks psdBlocks poly = true)
    (hd : ∀ l, (bTheta (bKb (bV14ᵀ * bV14))).d l ≤ 2) (hn : (bTheta (bKb (bV14ᵀ * bV14))).n ≤ nP)
    (x a b z c d e f q0 q1 q2 q3 q4 q5 : ℝ) :
    0 ≤ (star ![(q0 : ℂ) + (q3 : ℂ) * Complex.I, (q1 : ℂ) + (q4 : ℂ) * Complex.I,
        (q2 : ℂ) + (q5 : ℂ) * Complex.I] ⬝ᵥ
      (K31 ((19 / 18 : ℂ) * ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f).permanent)
        ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f) *ᵥ
        ![(q0 : ℂ) + (q3 : ℂ) * Complex.I, (q1 : ℂ) + (q4 : ℂ) * Complex.I,
          (q2 : ℂ) + (q5 : ℂ) * Complex.I])).re := by
  have hmap : (Kb ((V1q (-C Gi.I))ᵀ * V1q (C Gi.I))).map (psi 3 bP) =
      Kb ((V1v14 3 bP (-Gi.I))ᵀ * V1v14 3 bP Gi.I) := by
    rw [map_Kb, Matrix.map_mul, Matrix.transpose_map, V1q_psi, V1q_psi, psi_C, map_neg, psi_C]
  have hψ : psi 3 bP (Theta (Kb ((V1q (-C Gi.I))ᵀ * V1q (C Gi.I)))) =
      ⟨evalSl (3 ^ 8) bP (chanRe (Kb ((V1v14 3 bP (-Gi.I))ᵀ * V1v14 3 bP Gi.I))),
        evalSl (3 ^ 8) bP (chanIm (Kb ((V1v14 3 bP (-Gi.I))ᵀ * V1v14 3 bP Gi.I)))⟩ := by
    rw [psi_Theta, hmap]
  have hM : Maj (fun _ => 2) nP (Theta (Kb ((V1q (-C Gi.I))ᵀ * V1q (C Gi.I)))) :=
    Maj.mono (Theta_ok (MOk.Kb (MOk.mul (V1q_ok _ Bd.Ok.I.neg).transpose (V1q_ok _ Bd.Ok.I))))
      hd hn
  have hPeq := Poly.eq_of_checkq hcP _ hψ hM
  obtain ⟨hk, hdig⟩ := Poly.facts_of_checkq hcP
  have h0 := cert_core_of_eq hcS _ hPeq hk hdig (zz14 x a b z c d e f q0 q1 q2 q3 q4 q5)
  rw [ev_Theta, ev_yp14, ev_yp14', map_Kb, Matrix.map_mul, Matrix.transpose_map, V1q_ev,
    V1q_ev'] at h0
  rw [K31_eq_Kb, Matrix.smul_mulVec, dotProduct_smul]
  simpa using h0

end
end Theta

end Kron
end Results.SoulesPotOrderFour
