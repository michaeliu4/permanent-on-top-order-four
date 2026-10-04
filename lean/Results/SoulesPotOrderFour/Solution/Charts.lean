import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Topology.Instances.Matrix

/-!
# Chart transfer lemmas

The polynomial certificates only prove inequalities on explicit low-dimensional "charts" of Gram
matrices.  This file transfers them to *all* positive semidefinite matrices of the relevant rank.

The argument, for a continuous `f` with `f (D* A D) = (∏ |d i|²)^j f A` for diagonal `D`:

1. `exists_gram_factor`: a PSD `A` of rank `≤ r` is `Vᴴ V` with `V : r × 4`;
2. `exists_qr`: `Vᴴ V = Rᴴ R` with `R` upper triangular (Gram–Schmidt on the columns of `V`);
3. `*_core`: if the first row of `R` has no zero entry (resp. the analogous conditions for the
   zero chart), then `Rᴴ R = Dᴴ (Cᴴ C) D` for a chart matrix `C` (after row phases), hence
   `0 ≤ f (Rᴴ R)` by the scaling law and the chart hypothesis;
4. perturbing `R` by `s • W` (resp. `V`), such conditions hold for all small `s ≠ 0`, and
   `0 ≤ f (Rᴴ R)` follows by continuity.

Main results (all hypotheses of the form `hsc` are the scaling law, `hchart` the chart inequality):
* `transfer_rank3` (chart `chartV1`, complex PSD, rank `≤ 3`);
* `transfer_zero` (chart `chartVz`, complex PSD, rank `≤ 3`, `A 0 1 = 0`);
* `transfer_rank2` (chart `chartV2`, complex PSD, rank `≤ 2`);
* `transfer_real` (chart `chartVR`) and `transfer_real0` (chart `chartVR0`, the paper's `V₀`):
  real PSD, rank `≤ 3`;
* `scalesR_of_scalesC`, `continuous_map_ofReal`, `chartVR_map`, `gram_map_ofReal`: bridge from a
  complex `f` to real matrices.
-/

open Matrix Topology Filter
open scoped ComplexOrder InnerProductSpace

namespace Results.SoulesPotOrderFour

/-! ### Charts -/

/-- Chart for rank at most three (complex). -/
def chartV1 (x a b z c d e f : ℝ) : Matrix (Fin 3) (Fin 4) ℂ :=
  !![1,1,1,1; 0,(x:ℂ),(a:ℂ)+(b:ℂ)*Complex.I,(c:ℂ)+(d:ℂ)*Complex.I;
    0,0,(z:ℂ),(e:ℂ)+(f:ℂ)*Complex.I]

/-- Chart for a zero off-diagonal entry at position `(0,1)`. -/
def chartVz (a b c d e f : ℝ) : Matrix (Fin 3) (Fin 4) ℂ :=
  !![1,0,(a:ℂ),(c:ℂ)+(d:ℂ)*Complex.I; 0,1,(b:ℂ),(e:ℂ)+(f:ℂ)*Complex.I; 0,0,1,1]

/-- Chart for rank at most two. -/
def chartV2 (r a b c d : ℝ) : Matrix (Fin 2) (Fin 4) ℂ :=
  !![1,1,1,1; 0,(r:ℂ),(a:ℂ)+(b:ℂ)*Complex.I,(c:ℂ)+(d:ℂ)*Complex.I]

/-- Real chart for rank at most three. -/
def chartVR (x y z u v : ℝ) : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1,1,1,1; 0,x,y,u; 0,0,z,v]

/-- Second real chart (the paper's `V₀`), used for the first eight real certificates. -/
def chartVR0 (x y z u v : ℝ) : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1,x,y,u; 0,1,z,v; 0,0,1,1]

/-! ### Linear algebra: Gram factors and QR -/

section Factor

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A positive semidefinite `4 × 4` matrix of rank at most `r` is `Vᴴ V` with `V : r × 4`. -/
theorem exists_gram_factor {r : ℕ} (hr : r ≤ 4) {A : Matrix (Fin 4) (Fin 4) 𝕜}
    (hA : A.PosSemidef) (hrk : A.rank ≤ r) :
    ∃ V : Matrix (Fin r) (Fin 4) 𝕜, A = Vᴴ * V := by
  classical
  have hH := hA.isHermitian
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := hA.eigenvalues_nonneg
  let U : Matrix (Fin 4) (Fin 4) 𝕜 := hH.eigenvectorUnitary
  let s : Fin 4 → 𝕜 := fun i => ((Real.sqrt (hH.eigenvalues i) : ℝ) : 𝕜)
  let B : Matrix (Fin 4) (Fin 4) 𝕜 := diagonal s * Uᴴ
  have hs : ∀ i, star (s i) = s i := fun i => RCLike.conj_ofReal _
  have hss : ∀ i, s i * s i = ((hH.eigenvalues i : ℝ) : 𝕜) := fun i => by
    simp only [s]; rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (hnn i)]
  have hAB : A = Bᴴ * B := by
    have h1 : A = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * Uᴴ := by
      have := hH.spectral_theorem
      rwa [Unitary.conjStarAlgAut_apply] at this
    have hD : diagonal s * diagonal s = diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
      rw [diagonal_mul_diagonal]; congr 1; funext i; exact hss i
    have hBH : Bᴴ = U * diagonal s := by
      simp only [B, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
        show star s = s from funext hs]
    calc A = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * Uᴴ := h1
      _ = U * (diagonal s * diagonal s) * Uᴴ := by rw [hD]
      _ = Bᴴ * B := by rw [hBH]; simp only [B, Matrix.mul_assoc]
  -- the rows of `B` outside the set of nonzero eigenvalues vanish
  let N : Finset (Fin 4) := Finset.univ.filter fun i => hH.eigenvalues i ≠ 0
  have hN : N.card ≤ r := by
    rw [hH.rank_eq_card_non_zero_eigs] at hrk
    simpa [N, Fintype.card_subtype] using hrk
  obtain ⟨u, hNu, -, hu⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ N) hN
    (by simpa using hr)
  have hB0 : ∀ i ∉ u, ∀ j, B i j = 0 := by
    intro i hi j
    have : hH.eigenvalues i = 0 := by
      by_contra h; exact hi (hNu (by simp [N, h]))
    simp [B, s, this, diagonal_mul]
  refine ⟨B.submatrix (u.orderEmbOfFin hu) id, ?_⟩
  rw [hAB]
  ext a c
  simp only [mul_apply, conjTranspose_apply, submatrix_apply, id]
  rw [← Finset.sum_image (f := fun i => star (B i a) * B i c)
        (g := u.orderEmbOfFin hu) (s := Finset.univ)
        (fun x _ y _ h => (u.orderEmbOfFin hu).injective h),
      Finset.image_orderEmbOfFin_univ]
  symm
  refine Finset.sum_subset (Finset.subset_univ u) fun i _ hi => ?_
  simp [hB0 i hi]

/-- QR decomposition of the Gram matrix: `Vᴴ V = Rᴴ R` with `R` upper triangular. -/
theorem exists_qr {n : ℕ} (hn : n ≤ 4) (V : Matrix (Fin n) (Fin 4) 𝕜) :
    ∃ R : Matrix (Fin n) (Fin 4) 𝕜, Vᴴ * V = Rᴴ * R ∧
      ∀ (i : Fin n) (j : Fin 4), j.val < i.val → R i j = 0 := by
  classical
  let vc : Fin 4 → EuclideanSpace 𝕜 (Fin n) := fun j => WithLp.toLp 2 (fun i => V i j)
  have hd : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = Fintype.card (Fin n) := by simp
  let f : Fin n → EuclideanSpace 𝕜 (Fin n) := fun k => vc (Fin.castLE hn k)
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis hd f
  refine ⟨Matrix.of fun k j => ⟪b k, vc j⟫_𝕜, ?_, ?_⟩
  · ext a c
    have h2 : (Vᴴ * V) a c = ⟪vc a, vc c⟫_𝕜 := by
      simp [mul_apply, conjTranspose_apply, vc, EuclideanSpace.inner_toLp_toLp, dotProduct,
        mul_comm]
    rw [h2, ← b.sum_inner_mul_inner, mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [conjTranspose_apply, of_apply]
    congr 1
    exact (inner_conj_symm (vc a) (b k)).symm
  · intro i j hij
    exact InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular hd f
      (i := ⟨j.val, by omega⟩) (j := i) hij

end Factor

/-! ### Closure (continuity) -/

/-- If `Φ` is continuous and nonnegative at `R + s • W` for all small `s ≠ 0`, it is nonnegative
at `R`. -/
theorem nonneg_of_perturb {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [ContinuousAdd E] [ContinuousSMul ℝ E] (Φ : E → ℝ) (hΦ : Continuous Φ) (R W : E)
    (h : ∀ᶠ s : ℝ in 𝓝[≠] 0, 0 ≤ Φ (R + s • W)) : 0 ≤ Φ R := by
  have hc : Continuous fun s : ℝ => Φ (R + s • W) := hΦ.comp (by fun_prop)
  have ht : Tendsto (fun s : ℝ => Φ (R + s • W)) (𝓝[≠] 0) (𝓝 (Φ R)) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht h

/-- `c + s • e` is nonzero for all small `s ≠ 0`, provided `e ≠ 0` whenever `c = 0`. -/
theorem eventually_add_smul_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c e : E) (h : c = 0 → e ≠ 0) : ∀ᶠ s : ℝ in 𝓝[≠] 0, c + s • e ≠ 0 := by
  by_cases hc : c = 0
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simpa [hc] using smul_ne_zero hs (h hc)
  · have : ∀ᶠ s : ℝ in 𝓝 0, c + s • e ≠ 0 :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.eventually_ne
        (by simpa using hc)
    exact eventually_nhdsWithin_of_eventually_nhds this

/-- Perturbing the first row of an `R` by `s • 1` and continuity. -/
theorem firstRow_closure {𝕜 : Type*} [RCLike 𝕜] {m : ℕ}
    (Φ : Matrix (Fin (m + 1)) (Fin 4) 𝕜 → ℝ) (hΦ : Continuous Φ)
    (R : Matrix (Fin (m + 1)) (Fin 4) 𝕜)
    (h : ∀ R' : Matrix (Fin (m + 1)) (Fin 4) 𝕜, (∀ i, i ≠ 0 → R' i = R i) →
      (∀ j, R' 0 j ≠ 0) → 0 ≤ Φ R') : 0 ≤ Φ R := by
  refine nonneg_of_perturb Φ hΦ R (Matrix.of fun i _ => if i = 0 then 1 else 0) ?_
  filter_upwards [Filter.eventually_all.2 fun j =>
    eventually_add_smul_ne_zero (R 0 j) (1 : 𝕜) (fun _ => one_ne_zero)] with s hs
  refine h _ (fun i hi => ?_) fun j => ?_
  · funext j; simp [hi]
  · simpa using hs j

/-! ### Scaling and phases -/

theorem exists_phase (c : ℂ) : ∃ ω : ℂ, star ω * ω = 1 ∧ (ω * c).im = 0 := by
  by_cases hc : c = 0
  · exact ⟨1, by simp, by simp [hc]⟩
  · have hn : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hc
    have h1 : c * (starRingEnd ℂ) c = (‖c‖ : ℂ) ^ 2 := Complex.mul_conj' c
    refine ⟨star c / ‖c‖, ?_, ?_⟩
    · simp only [Complex.star_def, map_div₀, Complex.conj_ofReal, Complex.conj_conj]
      field_simp
      rw [h1]
    · have : (starRingEnd ℂ) c / ‖c‖ * c = ‖c‖ := by
        field_simp
        rw [mul_comm, h1]
      simp only [Complex.star_def, this]
      simp

theorem re_ofReal_eq {z : ℂ} (h : z.im = 0) : ((z.re : ℝ) : ℂ) = z :=
  Complex.ext (by simp) (by simp [h])

theorem phase_cancel {ω r s : ℂ} (hω : star ω * ω = 1) (hs : s ≠ 0) :
    star ω * (ω * (r / s)) * s = r := by
  field_simp
  linear_combination r * hω

theorem phase_ne_zero {ω : ℂ} (hω : star ω * ω = 1) : ω ≠ 0 := by
  rintro rfl
  simp at hω

theorem gram_scale {n : ℕ} (C R : Matrix (Fin n) (Fin 4) ℂ) (ω : Fin n → ℂ) (w : Fin 4 → ℂ)
    (hω : ∀ k, star (ω k) * ω k = 1) (hR : ∀ k j, R k j = star (ω k) * C k j * w j) :
    Rᴴ * R = diagonal (star w) * (Cᴴ * C) * diagonal w := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [conjTranspose_apply, conjTranspose_apply, hR k i, hR k j]
  simp only [star_mul, star_star, Pi.star_apply]
  linear_combination (star (w i) * star (C k i) * C k j * w j) * hω k

/-- The scaling law of the complex case, as a hypothesis. -/
def ScalesC (f : Matrix (Fin 4) (Fin 4) ℂ → ℝ) (j : ℕ) : Prop :=
  ∀ d : Fin 4 → ℂ, (∀ i, d i ≠ 0) → ∀ A,
    f (diagonal (star d) * A * diagonal d) = (∏ i, ‖d i‖ ^ 2) ^ j * f A

theorem transfer_core {n : ℕ} {f : Matrix (Fin 4) (Fin 4) ℂ → ℝ} {j : ℕ} (hsc : ScalesC f j)
    (C R : Matrix (Fin n) (Fin 4) ℂ) (ω : Fin n → ℂ) (w : Fin 4 → ℂ) (hw : ∀ i, w i ≠ 0)
    (hω : ∀ k, star (ω k) * ω k = 1) (hR : ∀ k j, R k j = star (ω k) * C k j * w j)
    (hC : 0 ≤ f (Cᴴ * C)) : 0 ≤ f (Rᴴ * R) := by
  rw [gram_scale C R ω w hω hR, hsc w hw]
  exact mul_nonneg (pow_nonneg (Finset.prod_nonneg fun i _ => by positivity) _) hC

/-! ### Chart reduction on the upper triangular level (complex) -/

theorem chart1_core {f : Matrix (Fin 4) (Fin 4) ℂ → ℝ} {j : ℕ} (hsc : ScalesC f j)
    (hchart : ∀ x a b z c d e f',
      0 ≤ f ((chartV1 x a b z c d e f')ᴴ * chartV1 x a b z c d e f'))
    (R : Matrix (Fin 3) (Fin 4) ℂ) (h10 : R 1 0 = 0) (h20 : R 2 0 = 0) (h21 : R 2 1 = 0)
    (h0 : ∀ j, R 0 j ≠ 0) : 0 ≤ f (Rᴴ * R) := by
  obtain ⟨ω1, hω1, him1⟩ := exists_phase (R 1 1 / R 0 1)
  obtain ⟨ω2, hω2, him2⟩ := exists_phase (R 2 2 / R 0 2)
  obtain ⟨x, hx⟩ : ∃ x : ℝ, (x : ℂ) = ω1 * (R 1 1 / R 0 1) := ⟨_, re_ofReal_eq him1⟩
  obtain ⟨z, hz⟩ : ∃ z : ℝ, (z : ℂ) = ω2 * (R 2 2 / R 0 2) := ⟨_, re_ofReal_eq him2⟩
  obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, (a : ℂ) + b * Complex.I = ω1 * (R 1 2 / R 0 2) :=
    ⟨_, _, Complex.re_add_im _⟩
  obtain ⟨c, d, hcd⟩ : ∃ c d : ℝ, (c : ℂ) + d * Complex.I = ω1 * (R 1 3 / R 0 3) :=
    ⟨_, _, Complex.re_add_im _⟩
  obtain ⟨e, f', hef⟩ : ∃ e f' : ℝ, (e : ℂ) + f' * Complex.I = ω2 * (R 2 3 / R 0 3) :=
    ⟨_, _, Complex.re_add_im _⟩
  refine transfer_core hsc (chartV1 x a b z c d e f') R ![1, ω1, ω2] (fun j => R 0 j) h0
    ?_ ?_ (hchart _ _ _ _ _ _ _ _)
  · intro k; fin_cases k
    · simp
    · simpa using hω1
    · simpa using hω2
  · intro k j
    fin_cases k <;> fin_cases j <;> simp [chartV1]
    · exact h10
    · rw [hx]; exact (phase_cancel hω1 (h0 1)).symm
    · rw [hab]; exact (phase_cancel hω1 (h0 2)).symm
    · rw [hcd]; exact (phase_cancel hω1 (h0 3)).symm
    · exact h20
    · exact h21
    · rw [hz]; exact (phase_cancel hω2 (h0 2)).symm
    · rw [hef]; exact (phase_cancel hω2 (h0 3)).symm

theorem chart2_core {f : Matrix (Fin 4) (Fin 4) ℂ → ℝ} {j : ℕ} (hsc : ScalesC f j)
    (hchart : ∀ r a b c d, 0 ≤ f ((chartV2 r a b c d)ᴴ * chartV2 r a b c d))
    (R : Matrix (Fin 2) (Fin 4) ℂ) (h10 : R 1 0 = 0) (h0 : ∀ j, R 0 j ≠ 0) :
    0 ≤ f (Rᴴ * R) := by
  obtain ⟨ω1, hω1, him1⟩ := exists_phase (R 1 1 / R 0 1)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, (r : ℂ) = ω1 * (R 1 1 / R 0 1) := ⟨_, re_ofReal_eq him1⟩
  obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, (a : ℂ) + b * Complex.I = ω1 * (R 1 2 / R 0 2) :=
    ⟨_, _, Complex.re_add_im _⟩
  obtain ⟨c, d, hcd⟩ : ∃ c d : ℝ, (c : ℂ) + d * Complex.I = ω1 * (R 1 3 / R 0 3) :=
    ⟨_, _, Complex.re_add_im _⟩
  refine transfer_core hsc (chartV2 r a b c d) R ![1, ω1] (fun j => R 0 j) h0
    ?_ ?_ (hchart _ _ _ _ _)
  · intro k; fin_cases k
    · simp
    · simpa using hω1
  · intro k j
    fin_cases k <;> fin_cases j <;> simp [chartV2]
    · exact h10
    · rw [hr]; exact (phase_cancel hω1 (h0 1)).symm
    · rw [hab]; exact (phase_cancel hω1 (h0 2)).symm
    · rw [hcd]; exact (phase_cancel hω1 (h0 3)).symm

theorem chartz_core {f : Matrix (Fin 4) (Fin 4) ℂ → ℝ} {j : ℕ} (hsc : ScalesC f j)
    (hchart : ∀ a b c d e f',
      0 ≤ f ((chartVz a b c d e f')ᴴ * chartVz a b c d e f'))
    (R : Matrix (Fin 3) (Fin 4) ℂ) (h10 : R 1 0 = 0) (h20 : R 2 0 = 0) (h21 : R 2 1 = 0)
    (h01 : R 0 1 = 0) (h00 : R 0 0 ≠ 0) (h11 : R 1 1 ≠ 0) (h22 : R 2 2 ≠ 0) (h23 : R 2 3 ≠ 0) :
    0 ≤ f (Rᴴ * R) := by
  obtain ⟨ω0, hω0, him0⟩ := exists_phase (R 0 2 / R 2 2)
  obtain ⟨ω1, hω1, him1⟩ := exists_phase (R 1 2 / R 2 2)
  obtain ⟨a, ha⟩ : ∃ a : ℝ, (a : ℂ) = ω0 * (R 0 2 / R 2 2) := ⟨_, re_ofReal_eq him0⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, (b : ℂ) = ω1 * (R 1 2 / R 2 2) := ⟨_, re_ofReal_eq him1⟩
  obtain ⟨c, d, hcd⟩ : ∃ c d : ℝ, (c : ℂ) + d * Complex.I = ω0 * (R 0 3 / R 2 3) :=
    ⟨_, _, Complex.re_add_im _⟩
  obtain ⟨e, f', hef⟩ : ∃ e f' : ℝ, (e : ℂ) + f' * Complex.I = ω1 * (R 1 3 / R 2 3) :=
    ⟨_, _, Complex.re_add_im _⟩
  have hw : ∀ i, (![ω0 * R 0 0, ω1 * R 1 1, R 2 2, R 2 3] : Fin 4 → ℂ) i ≠ 0 := by
    intro i; fin_cases i
    · exact mul_ne_zero (phase_ne_zero hω0) h00
    · exact mul_ne_zero (phase_ne_zero hω1) h11
    · exact h22
    · exact h23
  refine transfer_core hsc (chartVz a b c d e f') R ![ω0, ω1, 1]
    ![ω0 * R 0 0, ω1 * R 1 1, R 2 2, R 2 3] hw ?_ ?_ (hchart _ _ _ _ _ _)
  · intro k; fin_cases k
    · simpa using hω0
    · simpa using hω1
    · simp
  · intro k j
    fin_cases k <;> fin_cases j <;> simp [chartVz]
    · linear_combination (-(R 0 0)) * hω0
    · exact h01
    · rw [ha]; exact (phase_cancel hω0 h22).symm
    · rw [hcd]; exact (phase_cancel hω0 h23).symm
    · exact h10
    · linear_combination (-(R 1 1)) * hω1
    · rw [hb]; exact (phase_cancel hω1 h22).symm
    · rw [hef]; exact (phase_cancel hω1 h23).symm
    · exact h20
    · exact h21

/-! ### Real case -/

theorem gram_scale_real (C R : Matrix (Fin 3) (Fin 4) ℝ) (w : Fin 4 → ℝ)
    (hR : ∀ k j, R k j = C k j * w j) :
    Rᵀ * R = diagonal w * (Cᵀ * C) * diagonal w := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [transpose_apply, transpose_apply, hR k i, hR k j]
  ring

/-- The scaling law of the real case, as a hypothesis. -/
def ScalesR (f : Matrix (Fin 4) (Fin 4) ℝ → ℝ) (j : ℕ) : Prop :=
  ∀ d : Fin 4 → ℝ, (∀ i, d i ≠ 0) → ∀ A,
    f (diagonal d * A * diagonal d) = (∏ i, d i ^ 2) ^ j * f A

theorem chartR_core {f : Matrix (Fin 4) (Fin 4) ℝ → ℝ} {j : ℕ} (hsc : ScalesR f j)
    (hchart : ∀ x y z u v, 0 ≤ f ((chartVR x y z u v)ᵀ * chartVR x y z u v))
    (R : Matrix (Fin 3) (Fin 4) ℝ) (h10 : R 1 0 = 0) (h20 : R 2 0 = 0) (h21 : R 2 1 = 0)
    (h0 : ∀ j, R 0 j ≠ 0) : 0 ≤ f (Rᵀ * R) := by
  have hR : ∀ k j, R k j = chartVR (R 1 1 / R 0 1) (R 1 2 / R 0 2) (R 2 2 / R 0 2)
      (R 1 3 / R 0 3) (R 2 3 / R 0 3) k j * R 0 j := by
    intro k j
    fin_cases k <;> fin_cases j <;> simp [chartVR]
    · exact h10
    · exact (div_mul_cancel₀ _ (h0 1)).symm
    · exact (div_mul_cancel₀ _ (h0 2)).symm
    · exact (div_mul_cancel₀ _ (h0 3)).symm
    · exact h20
    · exact h21
    · exact (div_mul_cancel₀ _ (h0 2)).symm
    · exact (div_mul_cancel₀ _ (h0 3)).symm
  rw [gram_scale_real _ R (fun j => R 0 j) hR, hsc _ h0]
  exact mul_nonneg (pow_nonneg (Finset.prod_nonneg fun i _ => by positivity) _) (hchart _ _ _ _ _)

theorem chartR0_core {f : Matrix (Fin 4) (Fin 4) ℝ → ℝ} {j : ℕ} (hsc : ScalesR f j)
    (hchart : ∀ x y z u v, 0 ≤ f ((chartVR0 x y z u v)ᵀ * chartVR0 x y z u v))
    (R : Matrix (Fin 3) (Fin 4) ℝ) (h10 : R 1 0 = 0) (h20 : R 2 0 = 0) (h21 : R 2 1 = 0)
    (h00 : R 0 0 ≠ 0) (h11 : R 1 1 ≠ 0) (h22 : R 2 2 ≠ 0) (h23 : R 2 3 ≠ 0) :
    0 ≤ f (Rᵀ * R) := by
  have hw : ∀ i, (![R 0 0, R 1 1, R 2 2, R 2 3] : Fin 4 → ℝ) i ≠ 0 := by
    intro i; fin_cases i
    exacts [h00, h11, h22, h23]
  have hR : ∀ k j, R k j = chartVR0 (R 0 1 / R 1 1) (R 0 2 / R 2 2) (R 1 2 / R 2 2)
      (R 0 3 / R 2 3) (R 1 3 / R 2 3) k j * ![R 0 0, R 1 1, R 2 2, R 2 3] j := by
    intro k j
    fin_cases k <;> fin_cases j <;> simp [chartVR0]
    · exact (div_mul_cancel₀ _ h11).symm
    · exact (div_mul_cancel₀ _ h22).symm
    · exact (div_mul_cancel₀ _ h23).symm
    · exact h10
    · exact (div_mul_cancel₀ _ h22).symm
    · exact (div_mul_cancel₀ _ h23).symm
    · exact h20
    · exact h21
  rw [gram_scale_real _ R _ hR, hsc _ hw]
  exact mul_nonneg (pow_nonneg (Finset.prod_nonneg fun i _ => by positivity) _) (hchart _ _ _ _ _)

/-! ### The zero off-diagonal chart -/

theorem exists_orth (v : Fin 3 → ℂ) :
    ∃ e : Fin 3 → ℂ, e ≠ 0 ∧ star v ⬝ᵥ e = 0 ∧ star e ⬝ᵥ v = 0 := by
  by_cases h : v 0 = 0 ∧ v 1 = 0
  · refine ⟨Pi.single 0 1, ?_, ?_, ?_⟩
    · intro h0; simpa using congr_fun h0 0
    · simp [dotProduct, Fin.sum_univ_three, h.1]
    · simp [dotProduct, Fin.sum_univ_three, h.1]
  · refine ⟨![star (v 1), -star (v 0), 0], ?_, ?_, ?_⟩
    · intro h0
      exact h ⟨by simpa using congr_fun h0 1, by simpa using congr_fun h0 0⟩
    · simp [dotProduct, Fin.sum_univ_three]; ring
    · simp [dotProduct, Fin.sum_univ_three]; ring

/-- Zero chart at the level of `V`, when the first two columns are nonzero and orthogonal. -/
theorem zero_nondeg {f : Matrix (Fin 4) (Fin 4) ℂ → ℝ} {j : ℕ} (hf : Continuous f)
    (hsc : ScalesC f j)
    (hchart : ∀ a b c d e f',
      0 ≤ f ((chartVz a b c d e f')ᴴ * chartVz a b c d e f'))
    (V : Matrix (Fin 3) (Fin 4) ℂ) (h01 : (Vᴴ * V) 0 1 = 0) (h00 : (Vᴴ * V) 0 0 ≠ 0)
    (h11 : (Vᴴ * V) 1 1 ≠ 0) : 0 ≤ f (Vᴴ * V) := by
  obtain ⟨R, hVR, hpat⟩ := exists_qr (n := 3) (by norm_num) V
  rw [hVR] at h01 h00 h11 ⊢
  have h10 : R 1 0 = 0 := hpat 1 0 (by decide)
  have h20 : R 2 0 = 0 := hpat 2 0 (by decide)
  have h21 : R 2 1 = 0 := hpat 2 1 (by decide)
  have h00' : R 0 0 ≠ 0 := by
    intro h; apply h00; simp [mul_apply, Fin.sum_univ_three, h, h10, h20]
  have h01' : R 0 1 = 0 := by
    have : star (R 0 0) * R 0 1 = 0 := by
      simpa [mul_apply, Fin.sum_univ_three, h10, h20] using h01
    exact (mul_eq_zero.1 this).resolve_left (by simpa using h00')
  have h11' : R 1 1 ≠ 0 := by
    intro h; apply h11; simp [mul_apply, Fin.sum_univ_three, h, h01', h21]
  refine nonneg_of_perturb (fun R : Matrix (Fin 3) (Fin 4) ℂ => f (Rᴴ * R)) (by fun_prop) R
    (Matrix.of fun i j => if i = 2 ∧ 2 ≤ j.val then 1 else 0) ?_
  filter_upwards [eventually_add_smul_ne_zero (R 2 2) (1 : ℂ) (fun _ => one_ne_zero),
    eventually_add_smul_ne_zero (R 2 3) (1 : ℂ) (fun _ => one_ne_zero)] with s hs2 hs3
  refine chartz_core hsc hchart _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp [h10, h20, h21, h01', h00', h11']
  · simpa using hs2
  · simpa using hs3

/-- The zero chart for every `V` with orthogonal first two columns (nonzero or not). -/
theorem zero_vlevel {f : Matrix (Fin 4) (Fin 4) ℂ → ℝ} {j : ℕ} (hf : Continuous f)
    (hsc : ScalesC f j)
    (hchart : ∀ a b c d e f',
      0 ≤ f ((chartVz a b c d e f')ᴴ * chartVz a b c d e f'))
    (V : Matrix (Fin 3) (Fin 4) ℂ) (h01 : (Vᴴ * V) 0 1 = 0) : 0 ≤ f (Vᴴ * V) := by
  have hg : ∀ (M : Matrix (Fin 3) (Fin 4) ℂ) (a b : Fin 4),
      (Mᴴ * M) a b = star (fun k => M k a) ⬝ᵥ (fun k => M k b) := by
    intro M a b; simp [mul_apply, dotProduct, conjTranspose_apply]
  set c1 : Fin 3 → ℂ := fun k => V k 0 with hc1
  set c2 : Fin 3 → ℂ := fun k => V k 1 with hc2
  have h01' : star c1 ⬝ᵥ c2 = 0 := by rw [← hg]; exact h01
  obtain ⟨e1, e2, he1, he2, he12, hne1, hne2⟩ : ∃ e1 e2 : Fin 3 → ℂ, star e1 ⬝ᵥ c2 = 0 ∧
      star c1 ⬝ᵥ e2 = 0 ∧ star e1 ⬝ᵥ e2 = 0 ∧ (c1 = 0 → e1 ≠ 0) ∧ (c2 = 0 → e2 ≠ 0) := by
    by_cases hz1 : c1 = 0 <;> by_cases hz2 : c2 = 0
    · refine ⟨Pi.single 0 1, Pi.single 1 1, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hz2]
      · simp [hz1]
      · simp [dotProduct, Fin.sum_univ_three]
      · intro _ h0; simpa using congr_fun h0 0
      · intro _ h0; simpa using congr_fun h0 1
    · obtain ⟨e, hne, h1, h2⟩ := exists_orth c2
      exact ⟨e, 0, h2, by simp, by simp, fun _ => hne, fun h => absurd h hz2⟩
    · obtain ⟨e, hne, h1, h2⟩ := exists_orth c1
      exact ⟨0, e, by simp, h1, by simp, fun h => absurd h hz1, fun _ => hne⟩
    · exact ⟨0, 0, by simp, by simp, by simp, fun h => absurd h hz1, fun h => absurd h hz2⟩
  refine nonneg_of_perturb (fun V : Matrix (Fin 3) (Fin 4) ℂ => f (Vᴴ * V)) (by fun_prop) V
    (Matrix.of fun k j => ![e1 k, e2 k, 0, 0] j) ?_
  filter_upwards [eventually_add_smul_ne_zero c1 e1 hne1,
    eventually_add_smul_ne_zero c2 e2 hne2] with s hs1 hs2
  have hv1 : (fun k => (V + s • Matrix.of fun k j => ![e1 k, e2 k, 0, 0] j) k 0) = c1 + s • e1 := by
    funext k; simp [c1]
  have hv2 : (fun k => (V + s • Matrix.of fun k j => ![e1 k, e2 k, 0, 0] j) k 1) = c2 + s • e2 := by
    funext k; simp [c2]
  refine zero_nondeg hf hsc hchart _ ?_ ?_ ?_
  · rw [hg, hv1, hv2]
    simp [star_add, star_smul, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      h01', he1, he2, he12]
  · rw [hg, hv1]; exact fun h => hs1 (dotProduct_star_self_eq_zero.1 h)
  · rw [hg, hv2]; exact fun h => hs2 (dotProduct_star_self_eq_zero.1 h)

/-- **(T2)** Transfer from the chart `chartVz` to all PSD matrices of rank at most three with a zero
entry at position `(0,1)`. -/
theorem transfer_zero {f : Matrix (Fin 4) (Fin 4) ℂ → ℝ} (hf : Continuous f) (j : ℕ)
    (hsc : ∀ d : Fin 4 → ℂ, (∀ i, d i ≠ 0) → ∀ A,
      f (diagonal (star d) * A * diagonal d) = (∏ i, ‖d i‖ ^ 2) ^ j * f A)
    (hchart : ∀ a b c d e f',
      0 ≤ f ((chartVz a b c d e f')ᴴ * chartVz a b c d e f'))
    (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef) (hrk : A.rank ≤ 3) (h01 : A 0 1 = 0) :
    0 ≤ f A := by
  obtain ⟨V, rfl⟩ := exists_gram_factor (by norm_num) hA hrk
  exact zero_vlevel hf hsc hchart V h01

/-! ### The transfer theorems -/

/-- **(T1)** Transfer from the chart `chartV1` to all PSD matrices of rank at most three. -/
theorem transfer_rank3 {f : Matrix (Fin 4) (Fin 4) ℂ → ℝ} (hf : Continuous f) (j : ℕ)
    (hsc : ∀ d : Fin 4 → ℂ, (∀ i, d i ≠ 0) → ∀ A,
      f (diagonal (star d) * A * diagonal d) = (∏ i, ‖d i‖ ^ 2) ^ j * f A)
    (hchart : ∀ x a b z c d e f',
      0 ≤ f ((chartV1 x a b z c d e f')ᴴ * chartV1 x a b z c d e f'))
    (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef) (hrk : A.rank ≤ 3) : 0 ≤ f A := by
  obtain ⟨V, rfl⟩ := exists_gram_factor (by norm_num) hA hrk
  obtain ⟨R, hVR, hpat⟩ := exists_qr (n := 3) (by norm_num) V
  rw [hVR]
  refine firstRow_closure (fun R : Matrix (Fin 3) (Fin 4) ℂ => f (Rᴴ * R)) (by fun_prop) R
    fun R' hR' h0 => ?_
  refine chart1_core hsc hchart R' ?_ ?_ ?_ h0
  · rw [hR' 1 (by decide)]; exact hpat 1 0 (by decide)
  · rw [hR' 2 (by decide)]; exact hpat 2 0 (by decide)
  · rw [hR' 2 (by decide)]; exact hpat 2 1 (by decide)

/-- **(T3)** Transfer from the chart `chartV2` to all PSD matrices of rank at most two. -/
theorem transfer_rank2 {f : Matrix (Fin 4) (Fin 4) ℂ → ℝ} (hf : Continuous f) (j : ℕ)
    (hsc : ∀ d : Fin 4 → ℂ, (∀ i, d i ≠ 0) → ∀ A,
      f (diagonal (star d) * A * diagonal d) = (∏ i, ‖d i‖ ^ 2) ^ j * f A)
    (hchart : ∀ r a b c d, 0 ≤ f ((chartV2 r a b c d)ᴴ * chartV2 r a b c d))
    (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef) (hrk : A.rank ≤ 2) : 0 ≤ f A := by
  obtain ⟨V, rfl⟩ := exists_gram_factor (by norm_num) hA hrk
  obtain ⟨R, hVR, hpat⟩ := exists_qr (n := 2) (by norm_num) V
  rw [hVR]
  refine firstRow_closure (fun R : Matrix (Fin 2) (Fin 4) ℂ => f (Rᴴ * R)) (by fun_prop) R
    fun R' hR' h0 => ?_
  refine chart2_core hsc hchart R' ?_ h0
  rw [hR' 1 (by decide)]; exact hpat 1 0 (by decide)

/-- **(T4)** Real matrices: transfer from the real chart `chartVR` to all real PSD matrices of rank
at most three. -/
theorem transfer_real {f : Matrix (Fin 4) (Fin 4) ℝ → ℝ} (hf : Continuous f) (j : ℕ)
    (hsc : ∀ d : Fin 4 → ℝ, (∀ i, d i ≠ 0) → ∀ A,
      f (diagonal d * A * diagonal d) = (∏ i, d i ^ 2) ^ j * f A)
    (hchart : ∀ x y z u v, 0 ≤ f ((chartVR x y z u v)ᵀ * chartVR x y z u v))
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.PosSemidef) (hrk : A.rank ≤ 3) : 0 ≤ f A := by
  obtain ⟨V, rfl⟩ := exists_gram_factor (by norm_num) hA hrk
  obtain ⟨R, hVR, hpat⟩ := exists_qr (n := 3) (by norm_num) V
  rw [hVR]
  simp only [conjTranspose_eq_transpose_of_trivial]
  refine firstRow_closure (fun R : Matrix (Fin 3) (Fin 4) ℝ => f (Rᵀ * R)) (by fun_prop) R
    fun R' hR' h0 => ?_
  refine chartR_core hsc hchart R' ?_ ?_ ?_ h0
  · rw [hR' 1 (by decide)]; exact hpat 1 0 (by decide)
  · rw [hR' 2 (by decide)]; exact hpat 2 0 (by decide)
  · rw [hR' 2 (by decide)]; exact hpat 2 1 (by decide)

/-- **(T4')** Real matrices: transfer from the second real chart `chartVR0` to all real PSD
matrices of rank at most three. -/
theorem transfer_real0 {f : Matrix (Fin 4) (Fin 4) ℝ → ℝ} (hf : Continuous f) (j : ℕ)
    (hsc : ∀ d : Fin 4 → ℝ, (∀ i, d i ≠ 0) → ∀ A,
      f (diagonal d * A * diagonal d) = (∏ i, d i ^ 2) ^ j * f A)
    (hchart : ∀ x y z u v, 0 ≤ f ((chartVR0 x y z u v)ᵀ * chartVR0 x y z u v))
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.PosSemidef) (hrk : A.rank ≤ 3) : 0 ≤ f A := by
  obtain ⟨V, rfl⟩ := exists_gram_factor (by norm_num) hA hrk
  obtain ⟨R, hVR, hpat⟩ := exists_qr (n := 3) (by norm_num) V
  rw [hVR]
  simp only [conjTranspose_eq_transpose_of_trivial]
  have h10 : R 1 0 = 0 := hpat 1 0 (by decide)
  have h20 : R 2 0 = 0 := hpat 2 0 (by decide)
  have h21 : R 2 1 = 0 := hpat 2 1 (by decide)
  refine nonneg_of_perturb (fun R : Matrix (Fin 3) (Fin 4) ℝ => f (Rᵀ * R)) (by fun_prop) R
    (Matrix.of fun i j => if (i = 0 ∧ j = 0) ∨ (i = 1 ∧ j = 1) ∨ (i = 2 ∧ 2 ≤ j.val)
      then 1 else 0) ?_
  filter_upwards [eventually_add_smul_ne_zero (R 0 0) (1 : ℝ) (fun _ => one_ne_zero),
    eventually_add_smul_ne_zero (R 1 1) (1 : ℝ) (fun _ => one_ne_zero),
    eventually_add_smul_ne_zero (R 2 2) (1 : ℝ) (fun _ => one_ne_zero),
    eventually_add_smul_ne_zero (R 2 3) (1 : ℝ) (fun _ => one_ne_zero)] with s hs0 hs1 hs2 hs3
  refine chartR0_core hsc hchart _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp [h10, h20, h21]
  all_goals first | simpa using hs0 | simpa using hs1 | simpa using hs2 | simpa using hs3

/-! ### Bridge: real matrices viewed as complex ones -/

/-- The scaling law of the complex function `f` restricts to real diagonal scalings of real
matrices viewed as complex ones, so the same `f` can be reused in `transfer_real`:
use `fun B => f (B.map ((↑) : ℝ → ℂ))`. -/
theorem scalesR_of_scalesC {f : Matrix (Fin 4) (Fin 4) ℂ → ℝ} {j : ℕ}
    (hsc : ∀ d : Fin 4 → ℂ, (∀ i, d i ≠ 0) → ∀ A,
      f (diagonal (star d) * A * diagonal d) = (∏ i, ‖d i‖ ^ 2) ^ j * f A)
    (d : Fin 4 → ℝ) (hd : ∀ i, d i ≠ 0) (A : Matrix (Fin 4) (Fin 4) ℝ) :
    f ((diagonal d * A * diagonal d).map ((↑) : ℝ → ℂ)) =
      (∏ i, d i ^ 2) ^ j * f (A.map ((↑) : ℝ → ℂ)) := by
  have h := hsc (fun i => (d i : ℂ)) (fun i => by exact_mod_cast hd i) (A.map ((↑) : ℝ → ℂ))
  have e : (diagonal d * A * diagonal d).map ((↑) : ℝ → ℂ) =
      diagonal (star fun i => (d i : ℂ)) * A.map ((↑) : ℝ → ℂ) * diagonal fun i => (d i : ℂ) := by
    ext i k
    simp [mul_apply, diagonal_apply, Finset.sum_ite_eq]
  rw [e, h]
  simp

theorem continuous_map_ofReal :
    Continuous fun A : Matrix (Fin 4) (Fin 4) ℝ => A.map ((↑) : ℝ → ℂ) := by
  fun_prop

/-- The real chart `chartVR` is the complex chart `chartV1` with real parameters. -/
theorem chartVR_map (x y z u v : ℝ) :
    (chartVR x y z u v).map ((↑) : ℝ → ℂ) = chartV1 x y 0 z u 0 v 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chartVR, chartV1]

/-- Gram matrices of real matrices viewed as complex ones. -/
theorem gram_map_ofReal {m : ℕ} (R : Matrix (Fin m) (Fin 4) ℝ) :
    (Rᵀ * R).map ((↑) : ℝ → ℂ) = (R.map ((↑) : ℝ → ℂ))ᴴ * R.map ((↑) : ℝ → ℂ) := by
  ext i k
  simp [mul_apply, conjTranspose_apply]

end Results.SoulesPotOrderFour
