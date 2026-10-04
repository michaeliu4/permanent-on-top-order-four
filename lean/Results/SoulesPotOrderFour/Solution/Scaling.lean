import Results.SoulesPotOrderFour.Solution.Basic
import Results.SoulesPotOrderFour.Solution.Charts

/-!
# Scaling laws, continuity and transfer wrappers

For `d : Fin 4 → ℂ` write `scaleA d A = diag(star d) * A * diag d` and `gam d = ∏ ‖d i‖²`.
All identities hold for **all** `d` (no nonvanishing needed).

* Scaling: `phi_scaleA`, `permanent_scaleA`, `det_scaleA`, `cofactor_scaleA`, `signCofactor_scaleA`,
  `pairing_scaleA`, `K31_scaleA`, `K211_scaleA`, `K22_scaleA` (with a constant factor `κ * per A`)
  and the `κ = 1` forms `K31_scaleA_perm`, `K211_scaleA_perm`, `K22_scaleA_perm`;
  `e1_smul`, `e2_smul`, `e2four_smul`, `trace_smul'`, `det_smul'`.
* Continuity (`@[fun_prop]`): `continuous_permanent`, `continuous_cofactorPermMatrix`,
  `continuous_signCofactorMatrix`, `continuous_pairingMatrix`, `continuous_K31`, `continuous_K211`,
  `continuous_K22`, `continuous_e1`, `continuous_e2`, `continuous_e2four`; so e.g.
  `by fun_prop : Continuous fun A => (Matrix.det (K31 A.permanent A)).re` works.
* `Homog X j`: `X : Matrix (Fin 4) (Fin 4) ℂ → ℂ` is continuous and
  `X (scaleA d A) = gam d ^ j * X A`; combinators `Homog.add/sub/mul/const_mul`; ready-made
  `homog_permanent`, `homog_det`, `homog_trace_F/G`, `homog_e2four_F/G`,
  `homog_trace_K22`, `homog_det_K22`, `homog_e1_K31`, `homog_e2_K31`, `homog_det_K31`,
  `homog_e1_K211`, ... (and `_mul κ` versions with `K (κ * A.permanent) A`), `homog_quad_K31/K211/K22`
  (quadratic forms at a fixed vector).
* Wrappers `transfer_rank3_of`, `transfer_zero_of`, `transfer_rank2_of`, `transfer_real_of`,
  `transfer_real0_of`, `transfer_real_of_V1`: from a chart inequality `0 ≤ (X chart).re` to
  `0 ≤ (X A).re`.
-/

open Matrix Equiv
open scoped ComplexOrder

namespace Results.SoulesPotOrderFour

/-! ### Definitions and basic scaling -/

/-- The diagonal congruence `A ↦ D* A D`. -/
abbrev scaleA (d : Fin 4 → ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  diagonal (star d) * A * diagonal d

/-- `γ(d) = ∏ ‖d i‖²` (a real number; use `((gam d : ℝ) : ℂ)` in complex formulas). -/
noncomputable def gam (d : Fin 4 → ℂ) : ℝ := ∏ i, ‖d i‖ ^ 2

theorem gam_cast (d : Fin 4 → ℂ) : ((gam d : ℝ) : ℂ) = (∏ i, star (d i)) * ∏ i, d i := by
  rw [← Finset.prod_mul_distrib]
  unfold gam
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [mul_comm]
  exact (Complex.mul_conj' (d i)).symm

theorem gam_nonneg (d : Fin 4 → ℂ) : 0 ≤ gam d := Finset.prod_nonneg fun i _ => by positivity

theorem dmd_apply {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
    {R : Type*} [CommRing R]
    (u : m → R) (B : Matrix m n R) (v : n → R) (i : m) (j : n) :
    (diagonal u * B * diagonal v) i j = u i * B i j * v j := by
  simp [diagonal_mul, mul_diagonal]

theorem scaleA_apply (d : Fin 4 → ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    scaleA d A i j = star (d i) * A i j * d j := by
  simp

theorem permanent_dmd {m : Type*} [DecidableEq m] [Fintype m] {R : Type*} [CommRing R]
    (u v : m → R) (B : Matrix m m R) :
    (diagonal u * B * diagonal v).permanent = (∏ i, u i) * (∏ i, v i) * B.permanent := by
  simp only [permanent, dmd_apply, Finset.prod_mul_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Equiv.prod_comp σ u]
  ring

theorem det_dmd {m : Type*} [DecidableEq m] [Fintype m] {R : Type*} [CommRing R]
    (u v : m → R) (B : Matrix m m R) :
    (diagonal u * B * diagonal v).det = (∏ i, u i) * (∏ i, v i) * B.det := by
  rw [det_mul, det_mul, det_diagonal, det_diagonal]; ring

theorem phi_scaleA (d : Fin 4 → ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) (g : Perm (Fin 4)) :
    phi (scaleA d A) g = (gam d : ℂ) * phi A g := by
  simp only [phi, scaleA_apply, Finset.prod_mul_distrib, gam_cast]
  rw [Equiv.prod_comp g d]
  ring

theorem permanent_scaleA (d : Fin 4 → ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    (scaleA d A).permanent = (gam d : ℂ) * A.permanent := by
  rw [permanent_dmd, gam_cast]; rfl

theorem det_scaleA (d : Fin 4 → ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    (scaleA d A).det = (gam d : ℂ) * A.det := by
  rw [det_dmd, gam_cast]; rfl

theorem submatrix_dmd {l m n p : Type*} [DecidableEq m] [DecidableEq n] [DecidableEq l]
    [DecidableEq p] [Fintype m] [Fintype n] [Fintype l] [Fintype p]
    {R : Type*} [CommRing R] (u : m → R) (B : Matrix m n R) (v : n → R) (f : l → m) (g : p → n) :
    (diagonal u * B * diagonal v).submatrix f g =
      diagonal (fun a => u (f a)) * B.submatrix f g * diagonal (fun b => v (g b)) := by
  ext a b
  simp

theorem scaleA_minor (d : Fin 4 → ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    (scaleA d A).submatrix i.succAbove j.succAbove =
      diagonal (fun k => star (d (i.succAbove k))) * A.submatrix i.succAbove j.succAbove *
        diagonal (fun k => d (j.succAbove k)) :=
  submatrix_dmd _ _ _ _ _

theorem prod_succAbove_cast (d : Fin 4 → ℂ) (i j : Fin 4) :
    ((gam d : ℝ) : ℂ) = (star (d i) * ∏ k : Fin 3, star (d (i.succAbove k))) *
      (d j * ∏ k : Fin 3, d (j.succAbove k)) := by
  rw [gam_cast, Fin.prod_univ_succAbove (fun k => star (d k)) i,
    Fin.prod_univ_succAbove d j]

theorem permMinor_scaleA (d : Fin 4 → ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    permMinor (scaleA d A) i j =
      (∏ k : Fin 3, star (d (i.succAbove k))) * (∏ k : Fin 3, d (j.succAbove k)) *
        permMinor A i j := by
  rw [permMinor, scaleA_minor, permanent_dmd]; rfl

theorem det_minor_scaleA (d : Fin 4 → ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    ((scaleA d A).submatrix i.succAbove j.succAbove).det =
      (∏ k : Fin 3, star (d (i.succAbove k))) * (∏ k : Fin 3, d (j.succAbove k)) *
        (A.submatrix i.succAbove j.succAbove).det := by
  rw [scaleA_minor, det_dmd]

theorem cofactor_scaleA (d : Fin 4 → ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    cofactorPermMatrix (scaleA d A) = (gam d : ℂ) • cofactorPermMatrix A := by
  ext i j
  simp only [cofactorPermMatrix, of_apply, Matrix.smul_apply, smul_eq_mul, permMinor_scaleA,
    scaleA_apply, prod_succAbove_cast d i j]
  ring

theorem signCofactor_scaleA (d : Fin 4 → ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    signCofactorMatrix (scaleA d A) = (gam d : ℂ) • signCofactorMatrix A := by
  ext i j
  simp only [signCofactorMatrix, of_apply, Matrix.smul_apply, smul_eq_mul, det_minor_scaleA,
    scaleA_apply, prod_succAbove_cast d i j]
  ring

theorem pairing_scaleA (d : Fin 4 → ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    pairingMatrix (scaleA d A) = (gam d : ℂ) • pairingMatrix A := by
  ext i j
  simp only [pairingMatrix, of_apply, Matrix.smul_apply, smul_eq_mul, phi_scaleA, Finset.mul_sum]

/-! ### Homogeneity of the derived quantities -/

theorem K_smul_aux {m n : ℕ} (Q : Matrix (Fin m) (Fin n) ℂ) (c p : ℂ)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    Qᵀ * ((c * p) • (1 : Matrix (Fin m) (Fin m) ℂ) - c • X) * Q =
      c • (Qᵀ * (p • (1 : Matrix (Fin m) (Fin m) ℂ) - X) * Q) := by
  have : (c * p) • (1 : Matrix (Fin m) (Fin m) ℂ) - c • X = c • (p • 1 - X) := by
    rw [mul_smul, smul_sub]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem K31_scaleA (κ : ℂ) (d : Fin 4 → ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    K31 (κ * (scaleA d A).permanent) (scaleA d A) = (gam d : ℂ) • K31 (κ * A.permanent) A := by
  unfold K31
  rw [cofactor_scaleA, permanent_scaleA, mul_left_comm]
  exact K_smul_aux _ _ _ _

theorem K211_scaleA (κ : ℂ) (d : Fin 4 → ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    K211 (κ * (scaleA d A).permanent) (scaleA d A) = (gam d : ℂ) • K211 (κ * A.permanent) A := by
  unfold K211
  rw [signCofactor_scaleA, permanent_scaleA, mul_left_comm]
  exact K_smul_aux _ _ _ _

theorem K22_scaleA (κ : ℂ) (d : Fin 4 → ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    K22 (κ * (scaleA d A).permanent) (scaleA d A) = (gam d : ℂ) • K22 (κ * A.permanent) A := by
  unfold K22
  rw [pairing_scaleA, permanent_scaleA, mul_left_comm]
  exact K_smul_aux _ _ _ _

theorem K31_scaleA_perm (d : Fin 4 → ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    K31 (scaleA d A).permanent (scaleA d A) = (gam d : ℂ) • K31 A.permanent A := by
  simpa only [one_mul] using K31_scaleA 1 d A

theorem K211_scaleA_perm (d : Fin 4 → ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    K211 (scaleA d A).permanent (scaleA d A) = (gam d : ℂ) • K211 A.permanent A := by
  simpa only [one_mul] using K211_scaleA 1 d A

theorem K22_scaleA_perm (d : Fin 4 → ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    K22 (scaleA d A).permanent (scaleA d A) = (gam d : ℂ) • K22 A.permanent A := by
  simpa only [one_mul] using K22_scaleA 1 d A

section Hom

variable (c : ℂ)

theorem e1_smul (K : Matrix (Fin 3) (Fin 3) ℂ) : e1 (c • K) = c * e1 K := by
  simp [e1]; ring

theorem e2_smul (K : Matrix (Fin 3) (Fin 3) ℂ) : e2 (c • K) = c ^ 2 * e2 K := by
  simp [e2]; ring

theorem e2four_smul (G : Matrix (Fin 4) (Fin 4) ℂ) : e2four (c • G) = c ^ 2 * e2four G := by
  simp only [e2four, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem trace_smul' {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) : trace (c • K) = c * trace K := by
  simp

theorem det_smul' {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) : det (c • K) = c ^ n * det K := by
  simp

end Hom

/-! ### Continuity -/

section Cont

variable {α : Type*} [TopologicalSpace α] {R : Type*} [CommRing R] [TopologicalSpace R]
  [IsTopologicalRing R]

@[fun_prop]
theorem continuous_permanent {m : Type*} [Fintype m] [DecidableEq m]
    {A : α → Matrix m m R} (hA : Continuous A) : Continuous fun x => (A x).permanent := by
  simp_rw [Matrix.permanent]
  exact continuous_finsetSum _ fun σ _ =>
    continuous_finsetProd _ fun i _ => hA.matrix_elem _ _

@[fun_prop]
theorem continuous_cofactorPermMatrix {n : ℕ} {A : α → Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (hA : Continuous A) : Continuous fun x => cofactorPermMatrix (A x) :=
  continuous_matrix fun i j => (hA.matrix_elem i j).mul
    (continuous_permanent (hA.matrix_submatrix i.succAbove j.succAbove))

@[fun_prop]
theorem continuous_signCofactorMatrix {A : α → Matrix (Fin 4) (Fin 4) R}
    (hA : Continuous A) : Continuous fun x => signCofactorMatrix (A x) :=
  continuous_matrix fun i j => (hA.matrix_elem i j).mul
    (continuous_const.mul (Continuous.matrix_det (hA.matrix_submatrix i.succAbove j.succAbove)))

@[fun_prop]
theorem continuous_pairingMatrix {A : α → Matrix (Fin 4) (Fin 4) R}
    (hA : Continuous A) : Continuous fun x => pairingMatrix (A x) :=
  continuous_matrix fun i j => by
    simp only [Results.SoulesPotOrderFour.pairingMatrix, of_apply]
    exact continuous_finsetSum _ fun g _ => continuous_finsetProd _ fun k _ => hA.matrix_elem _ _

@[fun_prop]
theorem continuous_K31 {l : α → R} {A : α → Matrix (Fin 4) (Fin 4) R}
    (hl : Continuous l) (hA : Continuous A) : Continuous fun x => K31 (l x) (A x) := by
  unfold Results.SoulesPotOrderFour.K31
  have h1 : Continuous fun x => l x • (1 : Matrix (Fin 4) (Fin 4) R) - cofactorPermMatrix (A x) :=
    (hl.smul continuous_const).sub (continuous_cofactorPermMatrix hA)
  exact (continuous_const.matrix_mul h1).matrix_mul continuous_const

@[fun_prop]
theorem continuous_K211 {l : α → R} {A : α → Matrix (Fin 4) (Fin 4) R}
    (hl : Continuous l) (hA : Continuous A) : Continuous fun x => K211 (l x) (A x) := by
  unfold Results.SoulesPotOrderFour.K211
  have h1 : Continuous fun x => l x • (1 : Matrix (Fin 4) (Fin 4) R) - signCofactorMatrix (A x) :=
    (hl.smul continuous_const).sub (continuous_signCofactorMatrix hA)
  exact (continuous_const.matrix_mul h1).matrix_mul continuous_const

@[fun_prop]
theorem continuous_K22 {l : α → R} {A : α → Matrix (Fin 4) (Fin 4) R}
    (hl : Continuous l) (hA : Continuous A) : Continuous fun x => K22 (l x) (A x) := by
  unfold Results.SoulesPotOrderFour.K22
  have h1 : Continuous fun x => l x • (1 : Matrix (Fin 3) (Fin 3) R) - pairingMatrix (A x) :=
    (hl.smul continuous_const).sub (continuous_pairingMatrix hA)
  exact (continuous_const.matrix_mul h1).matrix_mul continuous_const

@[fun_prop]
theorem continuous_e1 {K : α → Matrix (Fin 3) (Fin 3) R} (hK : Continuous K) :
    Continuous fun x => e1 (K x) := by
  unfold Results.SoulesPotOrderFour.e1
  exact (((hK.matrix_elem 0 0).add (hK.matrix_elem 1 1)).add (hK.matrix_elem 2 2))

@[fun_prop]
theorem continuous_e2 {K : α → Matrix (Fin 3) (Fin 3) R} (hK : Continuous K) :
    Continuous fun x => e2 (K x) := by
  unfold Results.SoulesPotOrderFour.e2
  have := fun i j => hK.matrix_elem i j
  fun_prop

@[fun_prop]
theorem continuous_e2four {K : α → Matrix (Fin 4) (Fin 4) R} (hK : Continuous K) :
    Continuous fun x => e2four (K x) := by
  unfold Results.SoulesPotOrderFour.e2four
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  split_ifs
  · exact ((hK.matrix_elem i i).mul (hK.matrix_elem j j)).sub
      ((hK.matrix_elem i j).mul (hK.matrix_elem j i))
  · exact continuous_const

end Cont

/-! ### Homogeneous functions and the transfer wrappers -/

/-- `X` is continuous and homogeneous of degree `j` under diagonal congruence. -/
structure Homog (X : Matrix (Fin 4) (Fin 4) ℂ → ℂ) (j : ℕ) : Prop where
  cont : Continuous X
  scale : ∀ (d : Fin 4 → ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ), X (scaleA d A) = (gam d : ℂ) ^ j * X A

namespace Homog

variable {X Y : Matrix (Fin 4) (Fin 4) ℂ → ℂ} {j k : ℕ}

theorem add (hX : Homog X j) (hY : Homog Y j) : Homog (fun A => X A + Y A) j :=
  ⟨hX.cont.add hY.cont, fun d A => by rw [hX.scale, hY.scale]; ring⟩

theorem sub (hX : Homog X j) (hY : Homog Y j) : Homog (fun A => X A - Y A) j :=
  ⟨hX.cont.sub hY.cont, fun d A => by rw [hX.scale, hY.scale]; ring⟩

theorem mul (hX : Homog X j) (hY : Homog Y k) : Homog (fun A => X A * Y A) (j + k) :=
  ⟨hX.cont.mul hY.cont, fun d A => by rw [hX.scale, hY.scale]; ring⟩

theorem const_mul (c : ℂ) (hX : Homog X j) : Homog (fun A => c * X A) j :=
  ⟨continuous_const.mul hX.cont, fun d A => by rw [hX.scale]; ring⟩

/-- The real part is continuous and satisfies the scaling law of `Charts.transfer_*`. -/
theorem re_cont (hX : Homog X j) : Continuous fun A => (X A).re :=
  Complex.continuous_re.comp hX.cont

theorem re_scale (hX : Homog X j) (d : Fin 4 → ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    (X (diagonal (star d) * A * diagonal d)).re = (∏ i, ‖d i‖ ^ 2) ^ j * (X A).re := by
  have := congrArg Complex.re (hX.scale d A)
  rw [← Complex.ofReal_pow, Complex.re_ofReal_mul] at this
  exact this

end Homog

section Wrappers

variable {X : Matrix (Fin 4) (Fin 4) ℂ → ℂ} {j : ℕ}

/-- Transfer of a chart inequality `0 ≤ (X Gram(chartV1)).re` to all PSD `A` of rank `≤ 3`. -/
theorem transfer_rank3_of (hX : Homog X j)
    (hchart : ∀ x a b z c d e f : ℝ,
      0 ≤ (X ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f)).re)
    (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef) (hrk : A.rank ≤ 3) : 0 ≤ (X A).re :=
  transfer_rank3 (f := fun A => (X A).re) hX.re_cont j (fun d _ => hX.re_scale d) hchart A hA hrk

/-- Same for the zero chart (`A 0 1 = 0`). -/
theorem transfer_zero_of (hX : Homog X j)
    (hchart : ∀ a b c d e f : ℝ,
      0 ≤ (X ((chartVz a b c d e f)ᴴ * chartVz a b c d e f)).re)
    (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef) (hrk : A.rank ≤ 3) (h01 : A 0 1 = 0) :
    0 ≤ (X A).re :=
  transfer_zero (f := fun A => (X A).re) hX.re_cont j (fun d _ => hX.re_scale d) hchart A hA hrk h01

/-- Same for the rank-two chart. -/
theorem transfer_rank2_of (hX : Homog X j)
    (hchart : ∀ r a b c d : ℝ, 0 ≤ (X ((chartV2 r a b c d)ᴴ * chartV2 r a b c d)).re)
    (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef) (hrk : A.rank ≤ 2) : 0 ≤ (X A).re :=
  transfer_rank2 (f := fun A => (X A).re) hX.re_cont j (fun d _ => hX.re_scale d) hchart A hA hrk

/-- Real matrices viewed as complex ones (chart `chartVR`). -/
theorem transfer_real_of (hX : Homog X j)
    (hchart : ∀ x y z u v : ℝ,
      0 ≤ (X (((chartVR x y z u v)ᵀ * chartVR x y z u v).map ((↑) : ℝ → ℂ))).re)
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.PosSemidef) (hrk : A.rank ≤ 3) :
    0 ≤ (X (A.map ((↑) : ℝ → ℂ))).re :=
  transfer_real (f := fun B => (X (B.map ((↑) : ℝ → ℂ))).re)
    (hX.re_cont.comp continuous_map_ofReal) j
    (fun d hd => scalesR_of_scalesC (f := fun A => (X A).re) (fun d _ => hX.re_scale d) d hd)
    hchart A hA hrk

/-- Real matrices viewed as complex ones (chart `chartVR0`). -/
theorem transfer_real0_of (hX : Homog X j)
    (hchart : ∀ x y z u v : ℝ,
      0 ≤ (X (((chartVR0 x y z u v)ᵀ * chartVR0 x y z u v).map ((↑) : ℝ → ℂ))).re)
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.PosSemidef) (hrk : A.rank ≤ 3) :
    0 ≤ (X (A.map ((↑) : ℝ → ℂ))).re :=
  transfer_real0 (f := fun B => (X (B.map ((↑) : ℝ → ℂ))).re)
    (hX.re_cont.comp continuous_map_ofReal) j
    (fun d hd => scalesR_of_scalesC (f := fun A => (X A).re) (fun d _ => hX.re_scale d) d hd)
    hchart A hA hrk

/-- Real matrices viewed as complex ones, with the real chart expressed through `chartV1`. -/
theorem transfer_real_of_V1 (hX : Homog X j)
    (hchart : ∀ x y z u v : ℝ,
      0 ≤ (X ((chartV1 x y 0 z u 0 v 0)ᴴ * chartV1 x y 0 z u 0 v 0)).re)
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.PosSemidef) (hrk : A.rank ≤ 3) :
    0 ≤ (X (A.map ((↑) : ℝ → ℂ))).re :=
  transfer_real_of hX (fun x y z u v => by
    rw [gram_map_ofReal, chartVR_map]; exact hchart x y z u v) A hA hrk

end Wrappers

/-! ### The basic homogeneous functions -/

theorem homog_permanent : Homog (fun A => A.permanent) 1 :=
  ⟨by fun_prop, fun d A => by rw [permanent_scaleA, pow_one]⟩

theorem homog_det : Homog (fun A => A.det) 1 :=
  ⟨by fun_prop, fun d A => by rw [det_scaleA, pow_one]⟩

theorem homog_trace_F : Homog (fun A => trace (cofactorPermMatrix A)) 1 :=
  ⟨by fun_prop, fun d A => by rw [cofactor_scaleA, trace_smul', pow_one]⟩

theorem homog_trace_G : Homog (fun A => trace (signCofactorMatrix A)) 1 :=
  ⟨by fun_prop, fun d A => by rw [signCofactor_scaleA, trace_smul', pow_one]⟩

theorem homog_e2four_G : Homog (fun A => e2four (signCofactorMatrix A)) 2 :=
  ⟨by fun_prop, fun d A => by rw [signCofactor_scaleA, e2four_smul]⟩

theorem homog_e2four_F : Homog (fun A => e2four (cofactorPermMatrix A)) 2 :=
  ⟨by fun_prop, fun d A => by rw [cofactor_scaleA, e2four_smul]⟩

theorem homog_trace_K22_mul (κ : ℂ) : Homog (fun A => trace (K22 (κ * A.permanent) A)) 1 :=
  ⟨by fun_prop, fun d A => by rw [K22_scaleA, trace_smul', pow_one]⟩

theorem homog_det_K22_mul (κ : ℂ) : Homog (fun A => det (K22 (κ * A.permanent) A)) 2 :=
  ⟨by fun_prop, fun d A => by rw [K22_scaleA, det_smul']⟩

theorem homog_e1_K31_mul (κ : ℂ) : Homog (fun A => e1 (K31 (κ * A.permanent) A)) 1 :=
  ⟨by fun_prop, fun d A => by rw [K31_scaleA, e1_smul, pow_one]⟩

theorem homog_e2_K31_mul (κ : ℂ) : Homog (fun A => e2 (K31 (κ * A.permanent) A)) 2 :=
  ⟨by fun_prop, fun d A => by rw [K31_scaleA, e2_smul]⟩

theorem homog_det_K31_mul (κ : ℂ) : Homog (fun A => det (K31 (κ * A.permanent) A)) 3 :=
  ⟨by fun_prop, fun d A => by rw [K31_scaleA, det_smul']⟩

theorem homog_e1_K211_mul (κ : ℂ) : Homog (fun A => e1 (K211 (κ * A.permanent) A)) 1 :=
  ⟨by fun_prop, fun d A => by rw [K211_scaleA, e1_smul, pow_one]⟩

theorem homog_e2_K211_mul (κ : ℂ) : Homog (fun A => e2 (K211 (κ * A.permanent) A)) 2 :=
  ⟨by fun_prop, fun d A => by rw [K211_scaleA, e2_smul]⟩

theorem homog_det_K211_mul (κ : ℂ) : Homog (fun A => det (K211 (κ * A.permanent) A)) 3 :=
  ⟨by fun_prop, fun d A => by rw [K211_scaleA, det_smul']⟩


section NoKappa

/-- The `κ = 1` forms, i.e. with `p = A.permanent` exactly as in the paper. -/
theorem homog_trace_K22 : Homog (fun A => trace (K22 A.permanent A)) 1 := by
  simpa only [one_mul] using homog_trace_K22_mul 1
theorem homog_det_K22 : Homog (fun A => det (K22 A.permanent A)) 2 := by
  simpa only [one_mul] using homog_det_K22_mul 1
theorem homog_e1_K31 : Homog (fun A => e1 (K31 A.permanent A)) 1 := by
  simpa only [one_mul] using homog_e1_K31_mul 1
theorem homog_e2_K31 : Homog (fun A => e2 (K31 A.permanent A)) 2 := by
  simpa only [one_mul] using homog_e2_K31_mul 1
theorem homog_det_K31 : Homog (fun A => det (K31 A.permanent A)) 3 := by
  simpa only [one_mul] using homog_det_K31_mul 1
theorem homog_e1_K211 : Homog (fun A => e1 (K211 A.permanent A)) 1 := by
  simpa only [one_mul] using homog_e1_K211_mul 1
theorem homog_e2_K211 : Homog (fun A => e2 (K211 A.permanent A)) 2 := by
  simpa only [one_mul] using homog_e2_K211_mul 1
theorem homog_det_K211 : Homog (fun A => det (K211 A.permanent A)) 3 := by
  simpa only [one_mul] using homog_det_K211_mul 1

end NoKappa

section Quad

/-- Quadratic forms of `K₃₁(κ p)`, `K₂₁₁(κ p)`, `K₂₂(κ p)` at a fixed vector are homogeneous of
degree one. -/
theorem homog_quad_K31 (κ : ℂ) (y : Fin 3 → ℂ) :
    Homog (fun A => star y ⬝ᵥ (K31 (κ * A.permanent) A *ᵥ y)) 1 :=
  ⟨by fun_prop, fun d A => by
    rw [K31_scaleA, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, pow_one]⟩

theorem homog_quad_K211 (κ : ℂ) (y : Fin 3 → ℂ) :
    Homog (fun A => star y ⬝ᵥ (K211 (κ * A.permanent) A *ᵥ y)) 1 :=
  ⟨by fun_prop, fun d A => by
    rw [K211_scaleA, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, pow_one]⟩

theorem homog_quad_K22 (κ : ℂ) (y : Fin 2 → ℂ) :
    Homog (fun A => star y ⬝ᵥ (K22 (κ * A.permanent) A *ᵥ y)) 1 :=
  ⟨by fun_prop, fun d A => by
    rw [K22_scaleA, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, pow_one]⟩

end Quad

end Results.SoulesPotOrderFour
