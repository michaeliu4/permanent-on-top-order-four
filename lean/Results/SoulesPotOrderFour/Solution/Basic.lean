import Results.SoulesPotOrderFour.Defs

/-!
# Shared definitions for the Level 3 proof

Definitions over an arbitrary commutative ring `R`, so that the same pipeline can be evaluated in
`ℂ`, in polynomial rings and in `ℤ[i]`-valued polynomial rings.  Nothing here is a statement of
the paper; the Challenge statements only use `Defs.lean`.

* `phi A g = ∏ i, A i (g i)` is the paper's `φ_A(g)`.
* `cofactorPermMatrix` (Defs) is `F = (a_ij per A(i,j))`.
* `signCofactorMatrix` is `G = (a_ij (-1)^(i+j) det A(i,j))`.
* `pairingMatrix` is `H = (∑_{g(P_j)=P_i} φ_A(g))` over the three pair partitions.
* `Q3`, `Q2` are the fixed (non-orthonormal) bases of `1^⊥` of the paper.
* `K31`, `K211`, `K22` are the compressed defect matrices.
* `e1`, `e2` for `3 × 3` matrices (trace, sum of principal `2 × 2` minors).
-/

open Matrix Equiv

namespace Results.SoulesPotOrderFour

section Basic

variable {R : Type*} [CommRing R]

/-- `φ_A(g) = ∏_i a_{i,g(i)}`. -/
def phi (A : Matrix (Fin 4) (Fin 4) R) (g : Perm (Fin 4)) : R := ∏ i, A i (g i)

/-- `G = (a_ij (-1)^(i+j) det A(i,j))`, the realization of the `(2,1,1)` block. -/
def signCofactorMatrix (A : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 4) (Fin 4) R :=
  Matrix.of fun i j =>
    A i j * (((-1 : R) ^ (i.val + j.val)) * (A.submatrix i.succAbove j.succAbove).det)

/-- Same-block relation of the pair partition `P_k` (`P_0 = 12|34`, `P_1 = 13|24`, `P_2 = 14|23`,
indices counted from `0`), as a Boolean. -/
def pairRel (k : Fin 3) (x y : Fin 4) : Bool :=
  match k with
  | 0 => decide (x.val / 2 = y.val / 2)
  | 1 => decide (x.val % 2 = y.val % 2)
  | 2 => decide (x.val = y.val ∨ x.val + y.val = 3)

/-- `H = (∑_{g : g(P_j) = P_i} φ_A(g))`, the realization of the `(2,2)` block. -/
def pairingMatrix (A : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun i j =>
    ∑ g ∈ Finset.univ.filter (fun g : Perm (Fin 4) => ∀ x y, pairRel j x y = pairRel i (g x) (g y)),
      phi A g

/-- The columns span `1^⊥ ⊆ R^4`. -/
def Q3 : Matrix (Fin 4) (Fin 3) R :=
  !![1, 0, 0; 0, 1, 0; 0, 0, 1; -1, -1, -1]

/-- The columns span `1^⊥ ⊆ R^3`. -/
def Q2 : Matrix (Fin 3) (Fin 2) R :=
  !![1, 0; 0, 1; -1, -1]

/-- `K_{31}(λ) = Q₃ᵀ (λ I - F) Q₃`; the paper's `K_{31}` is `K31 A.permanent A`. -/
def K31 (lam : R) (A : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 3) (Fin 3) R :=
  (Q3 : Matrix (Fin 4) (Fin 3) R)ᵀ * (lam • (1 : Matrix (Fin 4) (Fin 4) R) - cofactorPermMatrix A) * Q3

/-- `K_{211}(λ) = Q₃ᵀ (λ I - G) Q₃`. -/
def K211 (lam : R) (A : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 3) (Fin 3) R :=
  (Q3 : Matrix (Fin 4) (Fin 3) R)ᵀ * (lam • (1 : Matrix (Fin 4) (Fin 4) R) - signCofactorMatrix A) * Q3

/-- `K_{22}(λ) = Q₂ᵀ (λ I - H) Q₂`. -/
def K22 (lam : R) (A : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 2) (Fin 2) R :=
  (Q2 : Matrix (Fin 3) (Fin 2) R)ᵀ * (lam • (1 : Matrix (Fin 3) (Fin 3) R) - pairingMatrix A) * Q2

/-- First elementary symmetric function (trace) of a `3 × 3` matrix. -/
def e1 (K : Matrix (Fin 3) (Fin 3) R) : R := K 0 0 + K 1 1 + K 2 2

/-- Second elementary symmetric function (sum of the principal `2 × 2` minors) of a `3 × 3` matrix. -/
def e2 (K : Matrix (Fin 3) (Fin 3) R) : R :=
  (K 0 0 * K 1 1 - K 0 1 * K 1 0) + (K 0 0 * K 2 2 - K 0 2 * K 2 0) +
    (K 1 1 * K 2 2 - K 1 2 * K 2 1)

/-- Second elementary symmetric function (sum of the six principal `2 × 2` minors) of a `4 × 4`
matrix. -/
def e2four (G : Matrix (Fin 4) (Fin 4) R) : R :=
  ∑ i : Fin 4, ∑ j : Fin 4, if i < j then G i i * G j j - G i j * G j i else 0

end Basic

end Results.SoulesPotOrderFour
