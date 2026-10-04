import Results.SoulesPotOrderFour.Solution.Scaling
import Results.SoulesPotOrderFour.Solution.Glue

/-!
# Complex rank-`≤ 3` sector theorems

* `ComplexCerts` collects the six chart inequalities delivered by the exact certificates.
* `posSemidef_fin_two`, `posSemidef_fin_three`: elementary criteria (trace/`e₂`/det ≥ 0).
* `permanent_nonneg`, `posSemidef_schurPower`: `per A ≥ 0` and `Π(A) ⪰ 0` (Schur product theorem).
* `K22_posSemidef` (R1), `K211_posSemidef` (R2), `e1_K31_nonneg`, `e2_K31_nonneg`,
  `K31_posSemidef_of_det` (R3, R4), `K31_mono`, `K211_mono`, `K22_mono` (R5).
-/

open Matrix Equiv
open scoped ComplexOrder

namespace Results.SoulesPotOrderFour

/-- The six chart inequalities (all variables real, `A = V(t)ᴴ V(t)`, `p = per A`,
`T = tr (signCofactorMatrix A)`), proved from the exact rational certificates. -/
structure ComplexCerts : Prop where
  tr22 : ∀ x a b z c d e f : ℝ,
    0 ≤ (Matrix.trace (K22 ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f).permanent
      ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f))).re
  det22 : ∀ x a b z c d e f : ℝ,
    0 ≤ (Matrix.det (K22 ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f).permanent
      ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f))).re
  tr31 : ∀ x a b z c d e f : ℝ,
    0 ≤ (e1 (K31 ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f).permanent
      ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f))).re
  e2_31 : ∀ x a b z c d e f : ℝ,
    0 ≤ (e2 (K31 ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f).permanent
      ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f))).re
  c8p5T : ∀ x a b z c d e f : ℝ,
    0 ≤ (8 * ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f).permanent -
      5 * Matrix.trace (signCofactorMatrix ((chartV1 x a b z c d e f)ᴴ *
        chartV1 x a b z c d e f))).re
  moment : ∀ x a b z c d e f : ℝ,
    0 ≤ (3 * ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f).permanent ^ 2 -
      2 * ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f).permanent *
        Matrix.trace (signCofactorMatrix ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f)) -
      Matrix.trace (signCofactorMatrix ((chartV1 x a b z c d e f)ᴴ *
        chartV1 x a b z c d e f)) ^ 2 +
      4 * e2four (signCofactorMatrix ((chartV1 x a b z c d e f)ᴴ *
        chartV1 x a b z c d e f))).re

/-! ### Elementary positivity criteria -/

/-- A Hermitian matrix with `det (s I + K) ≠ 0` (real part) for all `s > 0` is PSD. -/
theorem posSemidef_of_det_ne_zero {n : Type*} [Fintype n] [DecidableEq n] {K : Matrix n n ℂ}
    (hK : K.IsHermitian)
    (h : ∀ s : ℝ, 0 < s → (((s : ℂ) • (1 : Matrix n n ℂ) + K).det).re ≠ 0) : K.PosSemidef := by
  rw [hK.posSemidef_iff_eigenvalues_nonneg]
  refine fun i => ?_
  by_contra hneg
  have hlt : hK.eigenvalues i < 0 := not_le.1 hneg
  have hv0 : (⇑(hK.eigenvectorBasis i) : n → ℂ) ≠ 0 := fun h0 => by
    have h1 := OrthonormalBasis.norm_eq_one hK.eigenvectorBasis i
    have : hK.eigenvectorBasis i = 0 := by ext j; simpa using congrFun h0 j
    rw [this] at h1
    simp at h1
  have hv : ((((-hK.eigenvalues i : ℝ) : ℂ) • (1 : Matrix n n ℂ) + K) *ᵥ
      ⇑(hK.eigenvectorBasis i)) = 0 := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hK.mulVec_eigenvectorBasis,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    push_cast
    simp [neg_smul]
  have hdet := Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, hv0, hv⟩
  exact h (-hK.eigenvalues i) (by linarith) (by rw [hdet]; simp)

theorem posSemidef_fin_two {K : Matrix (Fin 2) (Fin 2) ℂ} (hK : K.IsHermitian)
    (h1 : 0 ≤ (Matrix.trace K).re) (h2 : 0 ≤ (Matrix.det K).re) : K.PosSemidef := by
  refine posSemidef_of_det_ne_zero hK fun s hs => ?_
  have e : (((s : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + K).det) =
      ((s ^ 2 : ℝ) : ℂ) + (s : ℂ) * Matrix.trace K + K.det := by
    simp only [det_fin_two, trace_fin_two]
    simp
    ring
  rw [e]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
  have : 0 < s ^ 2 := by positivity
  nlinarith [mul_nonneg hs.le h1]

theorem posSemidef_fin_three {K : Matrix (Fin 3) (Fin 3) ℂ} (hK : K.IsHermitian)
    (h1 : 0 ≤ (e1 K).re) (h2 : 0 ≤ (e2 K).re) (h3 : 0 ≤ (Matrix.det K).re) : K.PosSemidef := by
  refine posSemidef_of_det_ne_zero hK fun s hs => ?_
  have e : (((s : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) + K).det) =
      ((s ^ 3 : ℝ) : ℂ) + ((s ^ 2 : ℝ) : ℂ) * e1 K + (s : ℂ) * e2 K + K.det := by
    simp only [det_fin_three, e1, e2]
    simp
    ring
  rw [e]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
  have : 0 < s ^ 3 := by positivity
  nlinarith [mul_nonneg hs.le h2, mul_nonneg (sq_nonneg s) h1]

/-! ### Hermitian-ness, congruence and monotonicity in `λ` -/

theorem Q3_conjTranspose : (Q3 : Matrix (Fin 4) (Fin 3) ℂ)ᴴ = Q3ᵀ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Q3]

theorem Q2_conjTranspose : (Q2 : Matrix (Fin 3) (Fin 2) ℂ)ᴴ = Q2ᵀ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Q2]

theorem isHermitian_smul_one_sub {m : Type*} [Fintype m] [DecidableEq m] {lam : ℂ}
    (hl : star lam = lam) {X : Matrix m m ℂ} (hX : X.IsHermitian) :
    (lam • (1 : Matrix m m ℂ) - X).IsHermitian :=
  (isHermitian_one.smul hl).sub hX

theorem pairingMatrix_isHermitian {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : A.IsHermitian) :
    (pairingMatrix A).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, pairingMatrix, of_apply, star_sum]
  refine Finset.sum_nbij' (fun g => g⁻¹) (fun g => g⁻¹) ?_ ?_ (fun g _ => inv_inv g)
    (fun g _ => inv_inv g) ?_
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    intro x y
    simpa using (hg (g⁻¹ x) (g⁻¹ y)).symm
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    intro x y
    simpa using (hg (g⁻¹ x) (g⁻¹ y)).symm
  · intro g _
    simp only [phi, star_prod]
    rw [← Equiv.prod_comp g (fun k => A k (g⁻¹ k))]
    refine Finset.prod_congr rfl fun k _ => ?_
    simpa using hA.apply (g k) k

theorem K31_isHermitian {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : A.IsHermitian) :
    (K31 A.permanent A).IsHermitian := by
  unfold K31
  rw [← Q3_conjTranspose]
  exact isHermitian_conjTranspose_mul_mul _ (isHermitian_smul_one_sub
    (star_permanent_of_isHermitian hA) (cofactorPermMatrix_isHermitian hA))

theorem K22_isHermitian {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : A.IsHermitian) :
    (K22 A.permanent A).IsHermitian := by
  unfold K22
  rw [← Q2_conjTranspose]
  exact isHermitian_conjTranspose_mul_mul _ (isHermitian_smul_one_sub
    (star_permanent_of_isHermitian hA) (pairingMatrix_isHermitian hA))

theorem compress_mono {m n : ℕ} (Q : Matrix (Fin m) (Fin n) ℂ) (X : Matrix (Fin m) (Fin m) ℂ)
    {lam lam' : ℂ} (hl : lam ≤ lam')
    (h : (Qᴴ * (lam • (1 : Matrix (Fin m) (Fin m) ℂ) - X) * Q).PosSemidef) :
    (Qᴴ * (lam' • (1 : Matrix (Fin m) (Fin m) ℂ) - X) * Q).PosSemidef := by
  have e : Qᴴ * (lam' • (1 : Matrix (Fin m) (Fin m) ℂ) - X) * Q =
      Qᴴ * (lam • (1 : Matrix (Fin m) (Fin m) ℂ) - X) * Q + (lam' - lam) • (Qᴴ * Q) := by
    have : (lam' • (1 : Matrix (Fin m) (Fin m) ℂ) - X) =
        (lam • (1 : Matrix (Fin m) (Fin m) ℂ) - X) + (lam' - lam) • 1 := by
      rw [sub_smul]; abel
    rw [this, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [e]
  exact h.add ((posSemidef_conjTranspose_mul_self Q).smul (sub_nonneg.2 hl))

/-- **(R5)** monotonicity in `λ` (for `λ ≤ λ'` in the complex order; real `λ, λ'` are covered by
`Complex.real_le_real`, see also `K31_mono_real`). -/
theorem K31_mono {A : Matrix (Fin 4) (Fin 4) ℂ} {lam lam' : ℂ} (hl : lam ≤ lam')
    (h : (K31 lam A).PosSemidef) : (K31 lam' A).PosSemidef := by
  unfold K31 at *
  rw [← Q3_conjTranspose] at *
  exact compress_mono _ _ hl h

theorem K211_mono {A : Matrix (Fin 4) (Fin 4) ℂ} {lam lam' : ℂ} (hl : lam ≤ lam')
    (h : (K211 lam A).PosSemidef) : (K211 lam' A).PosSemidef := by
  unfold K211 at *
  rw [← Q3_conjTranspose] at *
  exact compress_mono _ _ hl h

theorem K22_mono {A : Matrix (Fin 4) (Fin 4) ℂ} {lam lam' : ℂ} (hl : lam ≤ lam')
    (h : (K22 lam A).PosSemidef) : (K22 lam' A).PosSemidef := by
  unfold K22 at *
  rw [← Q2_conjTranspose] at *
  exact compress_mono _ _ hl h

theorem K31_mono_real {A : Matrix (Fin 4) (Fin 4) ℂ} {lam lam' : ℝ} (hl : lam ≤ lam')
    (h : (K31 (lam : ℂ) A).PosSemidef) : (K31 (lam' : ℂ) A).PosSemidef :=
  K31_mono (Complex.real_le_real.2 hl) h

theorem K211_mono_real {A : Matrix (Fin 4) (Fin 4) ℂ} {lam lam' : ℝ} (hl : lam ≤ lam')
    (h : (K211 (lam : ℂ) A).PosSemidef) : (K211 (lam' : ℂ) A).PosSemidef :=
  K211_mono (Complex.real_le_real.2 hl) h

theorem K22_mono_real {A : Matrix (Fin 4) (Fin 4) ℂ} {lam lam' : ℝ} (hl : lam ≤ lam')
    (h : (K22 (lam : ℂ) A).PosSemidef) : (K22 (lam' : ℂ) A).PosSemidef :=
  K22_mono (Complex.real_le_real.2 hl) h

/-! ### (R6) `Π(A) ⪰ 0` and `per A ≥ 0` -/

theorem posSemidef_prod_aux {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    (S : Finset (Fin n)) :
    (Matrix.of fun σ τ : Perm (Fin n) => ∏ j ∈ S, A (σ j) (τ j)).PosSemidef := by
  induction S using Finset.induction_on with
  | empty =>
    have := posSemidef_vecMulVec_self_star (1 : Perm (Fin n) → ℂ)
    convert this using 1
    ext σ τ; simp [vecMulVec]
  | insert a S ha ih =>
    have h1 : (A.submatrix (fun σ : Perm (Fin n) => σ a) (fun τ => τ a)).PosSemidef :=
      hA.submatrix _
    have e : (Matrix.of fun σ τ : Perm (Fin n) => ∏ j ∈ insert a S, A (σ j) (τ j)) =
        (A.submatrix (fun σ : Perm (Fin n) => σ a) (fun τ => τ a)) ⊙
          (Matrix.of fun σ τ : Perm (Fin n) => ∏ j ∈ S, A (σ j) (τ j)) := by
      ext σ τ; simp [Finset.prod_insert ha]
    rw [e]
    exact h1.hadamard ih

theorem posSemidef_schurPower {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) :
    (schurPower A).PosSemidef :=
  posSemidef_prod_aux hA Finset.univ

theorem permanent_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) :
    0 ≤ A.permanent := by
  have h := (posSemidef_schurPower hA).dotProduct_mulVec_nonneg (1 : Perm (Fin n) → ℂ)
  rw [schurPower_mulVec_one] at h
  simp [dotProduct] at h
  have hN : (0 : ℝ) < Fintype.card (Perm (Fin n)) := by exact_mod_cast Fintype.card_pos
  obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 h
  rw [Complex.nonneg_iff]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero,
    Complex.mul_im] at h1 h2
  exact ⟨nonneg_of_mul_nonneg_right h1 hN, by nlinarith⟩

theorem re_permanent_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) :
    0 ≤ A.permanent.re :=
  (Complex.nonneg_iff.1 (permanent_nonneg hA)).1

/-- The permanent of a PSD matrix is the coercion of its (nonnegative) real part. -/
theorem permanent_eq_ofReal_re {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) :
    ((A.permanent.re : ℝ) : ℂ) = A.permanent :=
  Complex.ext (by simp) (by simpa using (Complex.nonneg_iff.1 (permanent_nonneg hA)).2)

theorem permanent_nonneg_real {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    0 ≤ A.permanent := by
  have h := permanent_nonneg ((posSemidef_map_ofReal_iff A).2 hA)
  have h2 : (A.map ((↑) : ℝ → ℂ)).permanent = (A.permanent : ℂ) := permanent_map Complex.ofRealHom A
  rw [h2] at h
  exact Complex.zero_le_real.1 h

/-! ### The cofactor matrix `G` of a rank-`≤ 3` Gram matrix -/

/-- `κ_i = (-1)^i det V_{î}`. -/
def kappa (V : Matrix (Fin 3) (Fin 4) ℂ) (i : Fin 4) : ℂ :=
  (-1) ^ (i : ℕ) * (V.submatrix id i.succAbove).det

theorem minor_gram (V : Matrix (Fin 3) (Fin 4) ℂ) (i j : Fin 4) :
    (Vᴴ * V).submatrix i.succAbove j.succAbove =
      (V.submatrix id i.succAbove)ᴴ * V.submatrix id j.succAbove := by
  ext a b
  simp [mul_apply, conjTranspose_apply]

theorem signCofactor_gram (V : Matrix (Fin 3) (Fin 4) ℂ) :
    signCofactorMatrix (Vᴴ * V) =
      diagonal (star (kappa V)) * (Vᴴ * V) * diagonal (kappa V) := by
  ext i j
  rw [dmd_apply]
  simp only [signCofactorMatrix, of_apply, minor_gram, det_mul, det_conjTranspose, kappa,
    Pi.star_apply, star_mul', star_pow, star_neg, star_one, pow_add]
  ring

theorem det_eq_zero_of_rank {A : Matrix (Fin 4) (Fin 4) ℂ} (hrk : A.rank ≤ 3) : A.det = 0 := by
  by_contra h
  have := Matrix.rank_of_isUnit A ((Matrix.isUnit_iff_isUnit_det A).2 (IsUnit.mk0 _ h))
  simp at this
  omega

/-- For `A` PSD of rank `≤ 3`, `G = signCofactorMatrix A` is PSD with `det G = 0`. -/
theorem signCofactor_posSemidef {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : A.PosSemidef)
    (hrk : A.rank ≤ 3) : (signCofactorMatrix A).PosSemidef ∧ (signCofactorMatrix A).det = 0 := by
  obtain ⟨V, rfl⟩ := exists_gram_factor (by norm_num) hA hrk
  rw [signCofactor_gram]
  refine ⟨?_, ?_⟩
  · have := hA.conjTranspose_mul_mul_same (diagonal (kappa V))
    rwa [diagonal_conjTranspose] at this
  · rw [det_mul, det_mul, det_eq_zero_of_rank hrk]; simp

/-! ### The eigenvalue argument for the cofactor sector -/

theorem trace_mul_self_eq {n : Type*} [Fintype n] [DecidableEq n] {G : Matrix n n ℂ}
    (hG : G.IsHermitian) : trace (G * G) = ∑ i, ((hG.eigenvalues i : ℝ) : ℂ) ^ 2 := by
  have h := hG.spectral_theorem
  have e : G * G = Unitary.conjStarAlgAut ℂ _ hG.eigenvectorUnitary
      (diagonal (RCLike.ofReal ∘ hG.eigenvalues) * diagonal (RCLike.ofReal ∘ hG.eigenvalues)) := by
    rw [map_mul, ← h]
  rw [e, Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul,
    diagonal_mul_diagonal, trace_diagonal]
  simp [sq]

theorem e2four_eq (G : Matrix (Fin 4) (Fin 4) ℂ) :
    e2four G = ((trace G) ^ 2 - trace (G * G)) / 2 := by
  simp only [e2four, trace, diag_apply, mul_apply, Fin.sum_univ_four]
  simp
  ring

theorem eig_core {l a b c p : ℝ} (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h0 : l * a * b * c = 0) (h8 : 5 * (l + a + b + c) ≤ 8 * p)
    (hm : 0 ≤ 3 * p ^ 2 - 2 * p * (l + a + b + c) - (l + a + b + c) ^ 2 +
      4 * (l * (a + b + c) + (a * b + a * c + b * c))) : l ≤ p := by
  by_contra hlp
  rw [not_le] at hlp
  have hl0 : l ≠ 0 := by intro h; rw [h] at hlp; linarith
  have habc : a * b * c = 0 := by
    have : l * (a * b * c) = 0 := by rw [← h0]; ring
    exact (mul_eq_zero.1 this).resolve_left hl0
  have hq : a * b + a * c + b * c ≤ (a + b + c) ^ 2 / 4 := by
    rcases mul_eq_zero.1 habc with h | h
    · rcases mul_eq_zero.1 h with h | h
      · subst h; nlinarith [sq_nonneg (b - c)]
      · subst h; nlinarith [sq_nonneg (a - c)]
    · subst h; nlinarith [sq_nonneg (a - b)]
  have key : 0 ≤ (l - p) * (2 * (a + b + c) - 3 * p - l) := by nlinarith [hm, hq]
  have hs8 : 2 * (a + b + c) - 3 * p - l < 0 := by linarith
  nlinarith [mul_pos (sub_pos.2 hlp) (neg_pos.2 hs8)]

theorem eig_bound (μ : Fin 4 → ℝ) (hμ : ∀ i, 0 ≤ μ i) (h0 : μ 0 * μ 1 * μ 2 * μ 3 = 0)
    {p : ℝ} (hp : 0 ≤ p) (h8 : 5 * (∑ i, μ i) ≤ 8 * p)
    (hm : 0 ≤ 3 * p ^ 2 - 2 * p * (∑ i, μ i) - (∑ i, μ i) ^ 2 +
      2 * ((∑ i, μ i) ^ 2 - ∑ i, μ i ^ 2)) (i : Fin 4) : μ i ≤ p := by
  simp only [Fin.sum_univ_four] at h8 hm
  fin_cases i
  · exact eig_core (l := μ 0) (a := μ 1) (b := μ 2) (c := μ 3) hp (hμ 1) (hμ 2) (hμ 3)
      h0 (by linarith) (le_of_le_of_eq hm (by ring))
  · exact eig_core (l := μ 1) (a := μ 0) (b := μ 2) (c := μ 3) hp (hμ 0) (hμ 2) (hμ 3)
      (by rw [← h0]; ring) (by linarith) (le_of_le_of_eq hm (by ring))
  · exact eig_core (l := μ 2) (a := μ 0) (b := μ 1) (c := μ 3) hp (hμ 0) (hμ 1) (hμ 3)
      (by rw [← h0]; ring) (by linarith) (le_of_le_of_eq hm (by ring))
  · exact eig_core (l := μ 3) (a := μ 0) (b := μ 1) (c := μ 2) hp (hμ 0) (hμ 1) (hμ 2)
      (by rw [← h0]; ring) (by linarith) (le_of_le_of_eq hm (by ring))

/-- The cofactor-sector eigenvalue bound: a PSD `G` with `det G = 0`, `8p ≥ 5 tr G` and the moment
inequality satisfies `G ⪯ p I`. -/
theorem G_psd_bound {G : Matrix (Fin 4) (Fin 4) ℂ} (hG : G.PosSemidef) (hdet : G.det = 0)
    {pr : ℝ} (hp : 0 ≤ pr)
    (h8 : 0 ≤ (8 * (pr : ℂ) - 5 * trace G).re)
    (hm : 0 ≤ (3 * (pr : ℂ) ^ 2 - 2 * pr * trace G - (trace G) ^ 2 + 4 * e2four G).re) :
    ((pr : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - G).PosSemidef := by
  have hH := hG.isHermitian
  have hμ : ∀ i, 0 ≤ hH.eigenvalues i := hG.eigenvalues_nonneg
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = ∑ i, hH.eigenvalues i := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ i, hH.eigenvalues i ^ 2 := ⟨_, rfl⟩
  have hT : trace G = (T : ℂ) := by
    rw [hH.trace_eq_sum_eigenvalues, hTdef]; push_cast; rfl
  have hS : trace (G * G) = (S : ℂ) := by
    rw [trace_mul_self_eq hH, hSdef]; push_cast; rfl
  have hE : e2four G = (((T ^ 2 - S) / 2 : ℝ) : ℂ) := by
    rw [e2four_eq, hT, hS]; push_cast; ring
  have h0 : hH.eigenvalues 0 * hH.eigenvalues 1 * hH.eigenvalues 2 * hH.eigenvalues 3 = 0 := by
    have h1 : (((∏ i, hH.eigenvalues i : ℝ)) : ℂ) = 0 := by
      rw [← hdet, hH.det_eq_prod_eigenvalues]; push_cast; rfl
    rw [← Fin.prod_univ_four (f := hH.eigenvalues)]
    exact Complex.ofReal_eq_zero.1 h1
  have h8' : 0 ≤ 8 * pr - 5 * T := by
    rw [hT] at h8
    have e : (8 * (pr : ℂ) - 5 * (T : ℂ)) = ((8 * pr - 5 * T : ℝ) : ℂ) := by push_cast; ring
    rwa [e, Complex.ofReal_re] at h8
  have hm' : 0 ≤ 3 * pr ^ 2 - 2 * pr * T - T ^ 2 + 4 * ((T ^ 2 - S) / 2) := by
    rw [hT, hE] at hm
    have e : (3 * (pr : ℂ) ^ 2 - 2 * pr * T - (T : ℂ) ^ 2 + 4 * (((T ^ 2 - S) / 2 : ℝ) : ℂ)) =
        ((3 * pr ^ 2 - 2 * pr * T - T ^ 2 + 4 * ((T ^ 2 - S) / 2) : ℝ) : ℂ) := by push_cast; ring
    rwa [e, Complex.ofReal_re] at hm
  refine (posSemidef_smul_one_sub_iff hH pr).2 fun i => ?_
  refine eig_bound _ hμ h0 hp ?_ ?_ i
  · rw [← hTdef]; linarith
  · rw [← hTdef, ← hSdef]; linarith

/-! ### The sector theorems -/

theorem homog_c8p5T :
    Homog (fun A => 8 * A.permanent - 5 * Matrix.trace (signCofactorMatrix A)) 1 :=
  (homog_permanent.const_mul 8).sub (homog_trace_G.const_mul 5)

theorem homog_moment :
    Homog (fun A => 3 * A.permanent ^ 2 - 2 * A.permanent * Matrix.trace (signCofactorMatrix A) -
      Matrix.trace (signCofactorMatrix A) ^ 2 + 4 * e2four (signCofactorMatrix A)) 2 :=
  ⟨by fun_prop, fun d A => by
    rw [permanent_scaleA, signCofactor_scaleA, trace_smul', e2four_smul]; ring⟩

variable (cert : ComplexCerts) {A : Matrix (Fin 4) (Fin 4) ℂ}
include cert

/-- **(R1)** trace and determinant of `K₂₂` are nonnegative, hence `K₂₂ ⪰ 0`. -/
theorem K22_trace_nonneg (hA : A.PosSemidef) (hrk : A.rank ≤ 3) :
    0 ≤ (Matrix.trace (K22 A.permanent A)).re :=
  transfer_rank3_of homog_trace_K22 cert.tr22 A hA hrk

theorem K22_det_nonneg (hA : A.PosSemidef) (hrk : A.rank ≤ 3) :
    0 ≤ (Matrix.det (K22 A.permanent A)).re :=
  transfer_rank3_of homog_det_K22 cert.det22 A hA hrk

theorem K22_posSemidef (hA : A.PosSemidef) (hrk : A.rank ≤ 3) :
    (K22 A.permanent A).PosSemidef :=
  posSemidef_fin_two (K22_isHermitian hA.isHermitian) (K22_trace_nonneg cert hA hrk)
    (K22_det_nonneg cert hA hrk)

/-- **(R3)** -/
theorem e1_K31_nonneg (hA : A.PosSemidef) (hrk : A.rank ≤ 3) :
    0 ≤ (e1 (K31 A.permanent A)).re :=
  transfer_rank3_of homog_e1_K31 cert.tr31 A hA hrk

theorem e2_K31_nonneg (hA : A.PosSemidef) (hrk : A.rank ≤ 3) :
    0 ≤ (e2 (K31 A.permanent A)).re :=
  transfer_rank3_of homog_e2_K31 cert.e2_31 A hA hrk

/-- **(R4)** `K₃₁ ⪰ 0` as soon as `det K₃₁ ≥ 0`. -/
theorem K31_posSemidef_of_det (hA : A.PosSemidef) (hrk : A.rank ≤ 3)
    (hdet : 0 ≤ (Matrix.det (K31 A.permanent A)).re) : (K31 A.permanent A).PosSemidef :=
  posSemidef_fin_three (K31_isHermitian hA.isHermitian) (e1_K31_nonneg cert hA hrk)
    (e2_K31_nonneg cert hA hrk) hdet

theorem c8p5T_nonneg (hA : A.PosSemidef) (hrk : A.rank ≤ 3) :
    0 ≤ (8 * A.permanent - 5 * Matrix.trace (signCofactorMatrix A)).re :=
  transfer_rank3_of homog_c8p5T cert.c8p5T A hA hrk

/-- **(R2)** `K₂₁₁ ⪰ 0`. -/
theorem K211_posSemidef (hA : A.PosSemidef) (hrk : A.rank ≤ 3) :
    (K211 A.permanent A).PosSemidef := by
  obtain ⟨hG, hdet⟩ := signCofactor_posSemidef hA hrk
  have h8 := c8p5T_nonneg cert hA hrk
  have hm := transfer_rank3_of homog_moment cert.moment A hA hrk
  have hpn := permanent_nonneg hA
  obtain ⟨pr, hpr⟩ : ∃ pr : ℝ, A.permanent = pr :=
    ⟨A.permanent.re, (Complex.ext (by simp) (by simpa using (Complex.nonneg_iff.1 hpn).2)).symm⟩
  rw [hpr] at hpn h8 hm
  have hX := G_psd_bound hG hdet (Complex.zero_le_real.1 hpn) h8 hm
  unfold K211
  rw [hpr, ← Q3_conjTranspose]
  exact hX.conjTranspose_mul_mul_same _

end Results.SoulesPotOrderFour
