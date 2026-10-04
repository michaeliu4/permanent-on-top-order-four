import Results.SoulesPotOrderFour.Solution.Real
import Results.SoulesPotOrderFour.Solution.RankTwo
import Results.SoulesPotOrderFour.Solution.Bound
import Results.SoulesPotOrderFour.Solution.Sec56
import Results.SoulesPotOrderFour.Solution.ZeroOrder3
import Results.SoulesPotOrderFour.Solution.FullRank
import Results.SoulesPotOrderFour.Solution.Cutoff

/-!
# Assembly of the Challenge statements from the chart certificates

Every theorem below is parametrized by `AllCerts`, the conjunction of the polynomial chart
inequalities (the exact rational sum-of-squares certificates of the paper's companion data).  The
certificates themselves are proved in the `Cert*` modules and `Main.lean` instantiates `AllCerts`.
The remaining ingredients (sector reduction, charts, diagonal decrement, order three, the order
cutoff) are proved in the other `Solution` modules.
-/

open Matrix Equiv
open scoped ComplexOrder

namespace Results.SoulesPotOrderFour

/-- The 19/18 chart inequality (one eighteenth of the paper's `Θ(t,q)`). -/
def BoundCert : Prop :=
  ∀ (x a b z c d e f q0 q1 q2 q3 q4 q5 : ℝ),
    0 ≤ (star ![(q0 : ℂ) + (q3 : ℂ) * Complex.I, (q1 : ℂ) + (q4 : ℂ) * Complex.I,
        (q2 : ℂ) + (q5 : ℂ) * Complex.I] ⬝ᵥ
      (K31 ((19 / 18 : ℂ) * ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f).permanent)
        ((chartV1 x a b z c d e f)ᴴ * chartV1 x a b z c d e f) *ᵥ
        ![(q0 : ℂ) + (q3 : ℂ) * Complex.I, (q1 : ℂ) + (q4 : ℂ) * Complex.I,
          (q2 : ℂ) + (q5 : ℂ) * Complex.I])).re

/-- All polynomial chart inequalities used by the proof. -/
structure AllCerts : Prop where
  cc : ComplexCerts
  zc : ZeroCert
  rc : RealCert
  rt : RankTwoCert
  bc : BoundCert

variable (C : AllCerts)

include C

/-- The order-three theorem (Bapat–Sunder for `n = 3`), proved here. -/
theorem order3_of : Order3 := order3 C.cc C.zc

theorem asm_main :
    (∀ (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.PosSemidef),
        lambdaMax (schurPower_isHermitian hA.isHermitian) = A.permanent) ∧
    (∀ (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef), A.rank ≤ 2 →
        (lambdaMax (schurPower_isHermitian hA.isHermitian) : ℂ) = A.permanent) :=
  ⟨main_real_of C.cc C.rc (order3_of C), main_ranktwo_of C.cc C.rt⟩

theorem asm_bounds (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef) :
    A.permanent.re ≤ lambdaMax (schurPower_isHermitian hA.isHermitian) ∧
      lambdaMax (schurPower_isHermitian hA.isHermitian) ≤ (19 / 18 : ℝ) * A.permanent.re :=
  theorem_1_2_bounds_of C.cc C.bc (order3_of C) A hA

theorem asm_zero_offdiag (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef)
    (hzero : ∃ i j, i ≠ j ∧ A i j = 0) :
    (lambdaMax (schurPower_isHermitian hA.isHermitian) : ℂ) = A.permanent :=
  theorem_1_2_zero_offdiag_of (fun _ hA _ _ hij hz => zero_all C.cc C.zc hA ⟨_, _, hij, hz⟩) A hA hzero

theorem asm_3_2 (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef) (hrank : A.rank ≤ 2) :
    (A.permanent • (1 : Matrix (Perm (Fin 4)) (Perm (Fin 4)) ℂ) - schurPower A).PosSemidef :=
  rank_two_pot C.cc C.rt A hA hrank

theorem asm_5_6 (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef) :
    lambdaMax (schurPower_isHermitian hA.isHermitian) =
      lambdaMax (cofactorPermMatrix_isHermitian hA.isHermitian) :=
  section_5_6_of (fun _ hA => K22_psd_all C.cc (order3_of C) hA)
    (fun _ hA => K211_psd_all C.cc (order3_of C) hA) (fun _ hA => det_le_permanent (order3_of C) hA) A hA

/-- Loewner form of the positive direction of the cutoff: every `n ≤ 4`. -/
theorem asm_pot_of_le_four (n : ℕ) (hn : n ≤ 4) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (hrank : A.rank ≤ 2) :
    (A.permanent • (1 : Matrix (Perm (Fin n)) (Perm (Fin n)) ℂ) - schurPower A).PosSemidef := by
  interval_cases n
  · have h : (A.permanent • (1 : Matrix (Perm (Fin 0)) (Perm (Fin 0)) ℂ) - schurPower A) = 0 := by
      ext σ τ
      obtain rfl : σ = τ := Subsingleton.elim σ τ
      simp [schurPower, Matrix.permanent_isEmpty]
    rw [h]
    exact Matrix.PosSemidef.zero
  · have h : (A.permanent • (1 : Matrix (Perm (Fin 1)) (Perm (Fin 1)) ℂ) - schurPower A) = 0 := by
      ext σ τ
      obtain rfl : σ = τ := Subsingleton.elim σ τ
      have hσ : σ = 1 := Subsingleton.elim _ _
      subst hσ
      simp [schurPower, Matrix.permanent]
    rw [h]
    exact Matrix.PosSemidef.zero
  · exact pot_two A hA.isHermitian
  · exact order3_of C A hA
  · exact asm_3_2 C A hA hrank

theorem asm_3_3 (n : ℕ) (_hn : 0 < n) :
    (∀ A : Matrix (Fin n) (Fin n) ℂ, A.PosSemidef → A.rank ≤ 2 →
        (A.permanent • (1 : Matrix (Perm (Fin n)) (Perm (Fin n)) ℂ) - schurPower A).PosSemidef) ↔
      n ≤ 4 := by
  constructor
  · intro h
    by_contra hn4
    obtain ⟨A, hA, hr, hnot⟩ := not_pot_of_five_le n (by omega)
    exact hnot (h A hA hr)
  · intro hn4 A hA hr
    exact asm_pot_of_le_four C n hn4 A hA hr

theorem asm_1_3 (n : ℕ) :
    (∀ (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef), A.rank ≤ 2 →
        (lambdaMax (schurPower_isHermitian hA.isHermitian) : ℂ) = A.permanent) ↔ n ≤ 4 := by
  constructor
  · intro h
    by_contra hn4
    obtain ⟨A, hA, hr, hnot⟩ := not_pot_of_five_le n (by omega)
    exact hnot ((lambdaMax_eq_permanent_iff_complex hA.isHermitian).1 (h A hA hr))
  · intro hn4 A hA hr
    exact (lambdaMax_eq_permanent_iff_complex hA.isHermitian).2
      (asm_pot_of_le_four C n hn4 A hA hr)

end Results.SoulesPotOrderFour
