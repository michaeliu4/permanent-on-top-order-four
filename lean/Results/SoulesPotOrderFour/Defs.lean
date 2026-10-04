import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Definitions for "Permanent-on-top bounds in order four" (POT V2)

Frozen source: 17-page PDF, SHA-256
`c5b450c59818ebaf0747494083f30e93a02789b89d2a74a902dd535716826251`.

* `Matrix.permanent` is Mathlib's `∑ σ, ∏ i, M (σ i) i`. It equals the paper's
  `per(A) = ∑_σ ∏_i a_{i,σ(i)}`; the reindexing is proved in `DefsTest.lean`.
* `schurPower A` is the paper's `Π(A)` from eq. (1): rows and columns are indexed by
  permutations of `Fin n`, and the `(σ, τ)` entry is `∏_j a_{σ(j), τ(j)}`.
* `lambdaMax h` is the largest eigenvalue of a Hermitian matrix, counted from Mathlib's
  spectral-theorem eigenvalue list (all real).
* `permMinor A i j` is `per A(i,j)`, the permanent after deleting row `i` and column `j`.
* `cofactorPermMatrix A` is the paper's `F_A = (a_ij per A(i,j))` from Sections 1 and 5.

The Hermitian and realness lemmas below are complete proofs. They let the statements in
`Challenge.lean` use `lambdaMax` and the real part of the permanent without adding hypotheses.
-/

open Matrix Equiv

namespace Results.SoulesPotOrderFour

section Algebraic

variable {R : Type*} [CommSemiring R]

/-- The Schur power matrix `Π(A)` of eq. (1): `Π(A)_{σ,τ} = ∏_{j} a_{σ(j), τ(j)}`. -/
def schurPower {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Perm (Fin n)) (Perm (Fin n)) R :=
  Matrix.of fun σ τ => ∏ j, A (σ j) (τ j)

/-- `per A(i,j)`: the permanent of the matrix obtained by deleting row `i` and column `j`. -/
def permMinor {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i j : Fin (n + 1)) : R :=
  (A.submatrix i.succAbove j.succAbove).permanent

/-- The cofactor-permanent matrix `F_A = (a_ij per A(i,j))` of Bapat and Sunder. -/
def cofactorPermMatrix {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j => A i j * permMinor A i j

end Algebraic

section Spectral

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `λ_max`: the largest eigenvalue of a Hermitian matrix. Mathlib lists the eigenvalues of a
Hermitian matrix with multiplicity, indexed by the matrix index type; this is their maximum. -/
noncomputable def lambdaMax {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    {M : Matrix m m 𝕜} (hM : M.IsHermitian) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty hM.eigenvalues

/-- `Π(A)` is Hermitian when `A` is Hermitian (the paper uses that it is Gram, hence PSD). -/
theorem schurPower_isHermitian {n : ℕ} {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    (schurPower A).IsHermitian := by
  ext σ τ
  simp only [conjTranspose_apply, schurPower, of_apply, star_prod]
  exact Finset.prod_congr rfl fun j _ => hA.apply (σ j) (τ j)

/-- Conjugating a permanent conjugate-transposes the matrix. -/
theorem permanent_conjTranspose {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m 𝕜) : Aᴴ.permanent = star A.permanent := by
  rw [← permanent_transpose, permanent, permanent, star_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [star_prod]
  rfl

/-- The permanent of a Hermitian matrix is fixed by conjugation. -/
theorem star_permanent_of_isHermitian {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m 𝕜} (hA : A.IsHermitian) : star A.permanent = A.permanent := by
  rw [← permanent_conjTranspose, hA.eq]

/-- The permanent of a Hermitian matrix is real: it equals the coercion of its real part.
This justifies stating the paper's real inequalities for `per(A)` through `RCLike.re`. -/
theorem ofReal_re_permanent_of_isHermitian {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m 𝕜} (hA : A.IsHermitian) :
    ((RCLike.re A.permanent : ℝ) : 𝕜) = A.permanent :=
  RCLike.conj_eq_iff_re.mp (by rw [starRingEnd_apply]; exact star_permanent_of_isHermitian hA)

/-- `F_A` is Hermitian when `A` is Hermitian (stated in Section 5.1 of the paper). -/
theorem cofactorPermMatrix_isHermitian {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜}
    (hA : A.IsHermitian) : (cofactorPermMatrix A).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, cofactorPermMatrix, permMinor, of_apply, star_mul]
  rw [hA.apply i j, mul_comm, ← permanent_conjTranspose, conjTranspose_submatrix, hA.eq]

end Spectral

end Results.SoulesPotOrderFour
