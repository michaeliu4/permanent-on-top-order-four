import Results.SoulesPotOrderFour.Solution.Assembly
import Results.SoulesPotOrderFour.Solution.CertReal
import Results.SoulesPotOrderFour.Solution.CertComplex
import Results.SoulesPotOrderFour.Solution.CertZero
import Results.SoulesPotOrderFour.Solution.CertRankTwo
import Results.SoulesPotOrderFour.Solution.CertBound

/-!
# Solution: the seven Challenge statements

The statements are those of `Challenge.lean`; the proofs assemble the modules of `Solution/`.  The
polynomial chart inequalities (exact rational sum-of-squares certificates) are the theorems
`cert_*` of the `Cert*` modules, checked by kernel computation.
-/

open Matrix Equiv
open scoped ComplexOrder

namespace Results.SoulesPotOrderFour

/-- All polynomial chart inequalities used by the proof, from the certificate modules. -/
theorem allCerts : AllCerts :=
  ⟨⟨cert_tr22, cert_det22, cert_tr31, cert_e2_31, cert_8p5T, cert_moment⟩, cert_zero_det31,
    cert_real_det31, cert_rank2_det31, cert_bound1918⟩

/-- **Theorem 1.1.** If `A` is a real symmetric positive semidefinite matrix of order four, or a
complex Hermitian positive semidefinite matrix of order four with `rank A ≤ 2`, then
`λ_max(Π(A)) = per(A)`. -/
theorem main :
    (∀ (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.PosSemidef),
        lambdaMax (schurPower_isHermitian hA.isHermitian) = A.permanent) ∧
    (∀ (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef), A.rank ≤ 2 →
        (lambdaMax (schurPower_isHermitian hA.isHermitian) : ℂ) = A.permanent) :=
  asm_main allCerts

/-- **Theorem 1.2, first sentence** (= Theorem 5.3). Every Hermitian positive semidefinite
matrix `A` of order four satisfies `per(A) ≤ λ_max(Π(A)) ≤ (19/18) per(A)`. -/
theorem theorem_1_2_bounds (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef) :
    A.permanent.re ≤ lambdaMax (schurPower_isHermitian hA.isHermitian) ∧
      lambdaMax (schurPower_isHermitian hA.isHermitian) ≤ (19 / 18 : ℝ) * A.permanent.re :=
  asm_bounds allCerts A hA

/-- **Theorem 1.2, second sentence** (= Theorem 5.2). If moreover `a_ij = 0` for some `i ≠ j`,
then `λ_max(Π(A)) = per(A)`. -/
theorem theorem_1_2_zero_offdiag (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef)
    (hzero : ∃ i j, i ≠ j ∧ A i j = 0) :
    (lambdaMax (schurPower_isHermitian hA.isHermitian) : ℂ) = A.permanent :=
  asm_zero_offdiag allCerts A hA hzero

/-- **Theorem 1.3** (`λ_max` form). For a fixed `n`, every complex Hermitian positive semidefinite
matrix `A` of order `n` with `rank A ≤ 2` satisfies `λ_max(Π(A)) = per(A)` if and only if `n ≤ 4`.
The introduction does not restrict `n`, so `n` ranges over all of `ℕ`. The `n = 0` instance
holds on both sides (`Π` of the empty matrix is `[1]` and its permanent is `1`; see
`DefsTest.lean`). Theorem 3.3's "positive integer" form is `theorem_3_3_cutoff_loewner`. -/
theorem theorem_1_3_cutoff (n : ℕ) :
    (∀ (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef), A.rank ≤ 2 →
        (lambdaMax (schurPower_isHermitian hA.isHermitian) : ℂ) = A.permanent) ↔ n ≤ 4 :=
  asm_1_3 allCerts n

/-- **Theorem 3.2.** If `A ∈ ℂ^{4×4}` is Hermitian positive semidefinite and `rank A ≤ 2`, then
`Π(A) ⪯ per(A) I`. -/
theorem theorem_3_2_loewner (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef)
    (hrank : A.rank ≤ 2) :
    (A.permanent • (1 : Matrix (Perm (Fin 4)) (Perm (Fin 4)) ℂ) - schurPower A).PosSemidef :=
  asm_3_2 allCerts A hA hrank

/-- **Theorem 3.3.** For a positive integer `n`, every complex Hermitian positive semidefinite
`n × n` matrix of rank at most two satisfies `Π(A) ⪯ per(A) I` if and only if `n ≤ 4`. -/
theorem theorem_3_3_cutoff_loewner (n : ℕ) (hn : 0 < n) :
    (∀ A : Matrix (Fin n) (Fin n) ℂ, A.PosSemidef → A.rank ≤ 2 →
        (A.permanent • (1 : Matrix (Perm (Fin n)) (Perm (Fin n)) ℂ) - schurPower A).PosSemidef) ↔
      n ≤ 4 :=
  asm_3_3 allCerts n hn

/-- **Section 5.6.** For every complex Hermitian positive semidefinite `A` of order four,
`λ_max(Π(A)) = λ_max(F_A)`, where `F_A = (a_ij per A(i,j))`. -/
theorem section_5_6_lambdaMax_eq (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef) :
    lambdaMax (schurPower_isHermitian hA.isHermitian) =
      lambdaMax (cofactorPermMatrix_isHermitian hA.isHermitian) :=
  asm_5_6 allCerts A hA

end Results.SoulesPotOrderFour
