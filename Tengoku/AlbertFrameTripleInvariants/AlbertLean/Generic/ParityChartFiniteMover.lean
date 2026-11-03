import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ParityChartMovingCenter
import Tengoku.Seed.Algebra.Polynomial.Roots

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms pivotPolynomial_ne_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms natDegree_pivotPolynomial_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_fin15_move_centers` (it only prints; the queue checks the axioms of every declaration). -/

/-! A fixed fifteen-point selector puts two anisotropic centers in the
`r ≠ 0` parity chart. -/
noncomputable section
namespace AlbertLean.Triality.ParityChartFiniteMover

open ExteriorSix CoordinateTensor
open SourceVectorPairDephase ParityChartMovingCenter
open SourceEvenReflections

universe u
variable {K : Type u} [Field K] [CharZero K]

open Polynomial

def pivotPolynomial (A : VCoord K) : K[X] :=
  C A.r * X ^ 7 - C A.z - C (A.omega .i34) * X +
    C (A.omega .i24) * X ^ 2 - C (A.omega .i23) * X ^ 3 -
    C (A.omega .i14) * X ^ 4 + C (A.omega .i13) * X ^ 5 -
    C (A.omega .i12) * X ^ 6

@[simp] theorem eval_pivotPolynomial (A : VCoord K) (t : K) :
    (pivotPolynomial A).eval t = pivotValue A t := by
  simp [pivotPolynomial, pivotValue]

theorem pivotPolynomial_ne_zero (A : VCoord K) (hA : nV A ≠ 0) :
    pivotPolynomial A ≠ 0 := by
  intro h
  have hr := congrArg (fun p : K[X] => p.coeff 7) h
  have hz := congrArg (fun p : K[X] => p.coeff 0) h
  have h12 := congrArg (fun p : K[X] => p.coeff 6) h
  have h13 := congrArg (fun p : K[X] => p.coeff 5) h
  have h14 := congrArg (fun p : K[X] => p.coeff 4) h
  have h23 := congrArg (fun p : K[X] => p.coeff 3) h
  have h24 := congrArg (fun p : K[X] => p.coeff 2) h
  have h34 := congrArg (fun p : K[X] => p.coeff 1) h
  simp [pivotPolynomial] at hr hz h12 h13 h14 h23 h24 h34
  have hzero : A = 0 := by
    apply VCoord.ext
    · exact hr
    · exact hz
    · funext i
      fin_cases i
      · exact h12
      · exact h13
      · exact h14
      · exact h23
      · exact h24
      · exact h34
  apply hA
  rw [hzero]
  simp [nV, pf_coordinate]

theorem natDegree_pivotPolynomial_le (A : VCoord K) :
    (pivotPolynomial A).natDegree ≤ 7 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  have h2 : n ≠ 2 := by omega
  have h3 : n ≠ 3 := by omega
  have h4 : n ≠ 4 := by omega
  have h5 : n ≠ 5 := by omega
  have h6 : n ≠ 6 := by omega
  have h7 : n ≠ 7 := by omega
  simp [pivotPolynomial, coeff_C, coeff_X, coeff_X_pow,
    h0, h1, Ne.symm h1, h2, h3, h4, h5, h6, h7]

theorem natDegree_pivotPolynomial_mul_le (A B : VCoord K) :
    (pivotPolynomial A * pivotPolynomial B).natDegree ≤ 14 := by
  calc
    (pivotPolynomial A * pivotPolynomial B).natDegree ≤
        (pivotPolynomial A).natDegree + (pivotPolynomial B).natDegree :=
      natDegree_mul_le
    _ ≤ 14 := Nat.add_le_add (natDegree_pivotPolynomial_le A)
      (natDegree_pivotPolynomial_le B)

/-- Among the fifteen fixed numeral values, one simultaneously puts both
anisotropic centers in the `r ≠ 0` parity chart.-/
theorem exists_fin15_move_centers (A B : VCoord K)
    (hA : nV A ≠ 0) (hB : nV B ≠ 0) :
    ∃ t : Fin 15,
      (evenV parityVector (movingCenter (t.val : K)) A).r ≠ 0 ∧
      (evenV parityVector (movingCenter (t.val : K)) B).r ≠ 0 := by
  classical
  let p := pivotPolynomial A * pivotPolynomial B
  have hp : p ≠ 0 := mul_ne_zero (pivotPolynomial_ne_zero A hA)
    (pivotPolynomial_ne_zero B hB)
  by_contra hall
  push Not at hall
  have hroots : ∀ t : Fin 15, p.eval (t.val : K) = 0 := by
    intro t
    by_cases hAt : (evenV parityVector (movingCenter (t.val : K)) A).r = 0
    · rw [moved_r, ← eval_pivotPolynomial] at hAt
      simp [p, hAt]
    · have hBt := hall t hAt
      rw [moved_r, ← eval_pivotPolynomial] at hBt
      simp [p, hBt]
  let S : Finset K := Finset.univ.image (fun t : Fin 15 => (t.val : K))
  have hScard : S.card = 15 := by
    have hi : Set.InjOn (fun t : Fin 15 => (t.val : K)) (Finset.univ : Finset (Fin 15)) := by
      intro i _ j _ hij
      apply Fin.ext
      exact Nat.cast_injective hij
    simpa [S] using Finset.card_image_iff.mpr hi
  have hsubset : S ⊆ p.roots.toFinset := by
    intro z hz
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hz
    simpa only [Multiset.mem_toFinset] using
      (Polynomial.mem_roots hp).mpr (hroots t)
  have hcard : 15 ≤ p.roots.toFinset.card := by
    rw [← hScard]
    exact Finset.card_le_card hsubset
  have hdeg : p.natDegree ≤ 14 := natDegree_pivotPolynomial_mul_le A B
  have hbound : p.roots.toFinset.card ≤ p.natDegree :=
    (Multiset.toFinset_card_le p.roots).trans (Polynomial.card_roots' p)
  omega

end AlbertLean.Triality.ParityChartFiniteMover
