import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.BlockAlgebra
import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.Goal
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.LinearAlgebra.Matrix.Hermitian
import Tengoku.Seed.Algebra.Order.BigOperators.Group.List
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hermitian splitting and the adaptive two-commutator reduction

Every trace-zero complex matrix splits into two trace-zero Hermitian matrices, each with
operator norm bounded by the original norm. A bounded commutator theorem for Hermitian
matrices therefore implies the adaptive two-commutator input needed by the Riccati construction.

The Hermitian commutator statement below is an explicit proposition and theorem hypothesis,
not an axiom. Its full spectral-ordering proof is given in `NoEpsilon.CyclicCommutator`.
Unlike the earlier quantum-expander route, the two first factors may depend on the input.
-/

open scoped Matrix.Norms.L2Operator

namespace NoEpsilon

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Hermitian real part of a complex matrix.-/
noncomputable def hermitianRealPart (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  realPart A

/-- The Hermitian imaginary part of a complex matrix.-/
noncomputable def hermitianImaginaryPart (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  imaginaryPart A

/-- The bounded Hermitian single-commutator proposition, proved in `NoEpsilon.CyclicCommutator`.
The norm of the unitary is stated as at most one to include the empty index type.-/
def HermitianUnitaryCommutatorBound : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ),
    G.IsHermitian → Matrix.trace G = 0 →
      ∃ U V : Matrix (Fin n) (Fin n) ℂ,
        U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ G = ringCommutator U V ∧
          ‖U‖ ≤ 1 ∧ ‖V‖ ≤ ‖G‖

/-- The weaker quantifier order sufficient for the Riccati construction: first factors may
depend on the target. This proposition does not assert any common fixed pair for all targets.-/
def AdaptiveTwoCommutatorBound : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), Matrix.trace A = 0 →
    ∃ U K V T : Matrix (Fin n) (Fin n) ℂ,
      U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ K ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
        A = ringCommutator U V + ringCommutator K T ∧
          ‖U‖ ≤ 1 ∧ ‖K‖ ≤ 1 ∧ ‖V‖ ≤ ‖A‖ ∧ ‖T‖ ≤ ‖A‖

/-- Multiplying the second factor by a complex scalar multiplies the commutator by it.
@isnad1 id=eq.0h4v.s6.0de32f90af43 from=translated src=- shape=482f8eec vocab=d3de4b61
-/
theorem ringCommutator_smul_right (z : ℂ) (U V : Matrix ι ι ℂ) :
    ringCommutator U (z • V) = z • ringCommutator U V := by
  simp only [ringCommutator, mul_smul_comm, smul_mul_assoc, smul_sub]

/-- The sign-greedy step for a real zero-sum ordering: one can choose a remaining term
without leaving the same interval that bounds the individual terms and current sum.
@isnad1 id=ex.4h3v.s6.85380e162a0b from=translated src=- shape=e5c017f8 vocab=eb54b4c6
-/
theorem exists_bounded_next_term (l : List ℝ) (s M : ℝ) (hl : l ≠ [])
    (hs : |s| ≤ M) (hbound : ∀ x ∈ l, |x| ≤ M) (htotal : s + l.sum = 0) :
    ∃ x ∈ l, |s + x| ≤ M := by
  rcases abs_le.mp hs with ⟨hslo, hshi⟩
  by_cases hsign : 0 ≤ s
  · have hsum : (l.map (fun x ↦ x)).sum ≤ (l.map (fun _ ↦ (0 : ℝ))).sum := by
      simpa using (show l.sum ≤ 0 by linarith)
    obtain ⟨x, hx, hxsign⟩ := List.exists_le_of_sum_le hl (fun x ↦ x) (fun _ ↦ (0 : ℝ)) hsum
    refine ⟨x, hx, abs_le.mpr ?_⟩
    have hxbound := abs_le.mp (hbound x hx)
    constructor <;> linarith
  · have hsum : (l.map (fun _ ↦ (0 : ℝ))).sum ≤ (l.map (fun x ↦ x)).sum := by
      simpa using (show 0 ≤ l.sum by linarith)
    obtain ⟨x, hx, hxsign⟩ := List.exists_le_of_sum_le hl (fun _ ↦ (0 : ℝ)) (fun x ↦ x) hsum
    refine ⟨x, hx, abs_le.mpr ?_⟩
    have hxbound := abs_le.mp (hbound x hx)
    constructor <;> linarith

/-- A real finite list whose sum cancels a bounded starting value can be reordered so
that every partial sum, including the starting value, stays within the same bound.
@isnad1 id=ex.3h3v.s6.836566abfa2d from=translated src=- shape=805ed8d2 vocab=14355a0b
-/
theorem exists_perm_bounded_partial_sums (l : List ℝ) (s M : ℝ)
    (hs : |s| ≤ M) (hbound : ∀ x ∈ l, |x| ≤ M) (htotal : s + l.sum = 0) :
    ∃ k : List ℝ, l.Perm k ∧ ∀ j : ℕ, |s + (k.take j).sum| ≤ M := by
  classical
  by_cases hl : l = []
  · subst l
    exact ⟨[], List.Perm.refl [], by simpa using fun _ : ℕ ↦ hs⟩
  · obtain ⟨x, hx, hsx⟩ := exists_bounded_next_term l s M hl hs hbound htotal
    have hperm : l.Perm (x :: l.erase x) := List.perm_cons_erase hx
    have hrest : ∀ y ∈ l.erase x, |y| ≤ M :=
      fun y hy ↦ hbound y (List.mem_of_mem_erase hy)
    have htotal' : (s + x) + (l.erase x).sum = 0 := by
      have hsum := hperm.sum_eq
      simp only [List.sum_cons] at hsum
      linarith
    obtain ⟨k, hk, hkbound⟩ :=
      exists_perm_bounded_partial_sums (l.erase x) (s + x) M hsx hrest htotal'
    refine ⟨x :: k, hperm.trans (hk.cons x), ?_⟩
    intro j
    cases j with
    | zero => simpa using hs
    | succ j => simpa [List.take_succ_cons, List.sum_cons, add_assoc] using hkbound j
termination_by l.length
decreasing_by
  classical
  have hlength := (List.perm_cons_erase hx).length_eq
  simp only [List.length_cons] at hlength
  omega

/-- In particular, real zero-sum eigenvalue lists admit a permutation with all partial
sums bounded by the maximum absolute eigenvalue.
@isnad1 id=ex.3h2v.s6.a3055459955f from=translated src=- shape=5aeae47b vocab=993fd93b
-/
theorem exists_zero_sum_real_ordering (l : List ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ l, |x| ≤ M) (htotal : l.sum = 0) :
    ∃ k : List ℝ, l.Perm k ∧ ∀ j : ℕ, |(k.take j).sum| ≤ M := by
  simpa using exists_perm_bounded_partial_sums l 0 M (by simpa using hM) hbound
    (by simpa using htotal)

/-- The sign-greedy ordering also preserves labels; repeated equal values do not lose
which spectral coordinate they came from.
@isnad1 id=ex.3h5v.s6.bf67469f00b0 from=translated src=- shape=a452e1c3 vocab=4b5c3dfe
-/
theorem exists_perm_bounded_weighted_partial_sums {α : Type*} (l : List α)
    (a : α → ℝ) (s M : ℝ) (hs : |s| ≤ M)
    (hbound : ∀ x ∈ l, |a x| ≤ M) (htotal : s + (l.map a).sum = 0) :
    ∃ k : List α, l.Perm k ∧ ∀ j : ℕ, |s + ((k.take j).map a).sum| ≤ M := by
  classical
  by_cases hl : l = []
  · subst l
    exact ⟨[], List.Perm.refl [], by simpa using fun _ : ℕ ↦ hs⟩
  · have hmap : l.map a ≠ [] := by simpa using hl
    have hb : ∀ y ∈ l.map a, |y| ≤ M := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      exact hbound x hx
    obtain ⟨y, hy, hsy⟩ := exists_bounded_next_term (l.map a) s M hmap hs hb htotal
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have hperm : l.Perm (x :: l.erase x) := List.perm_cons_erase hx
    have hrest : ∀ z ∈ l.erase x, |a z| ≤ M :=
      fun z hz ↦ hbound z (List.mem_of_mem_erase hz)
    have htotal' : (s + a x) + ((l.erase x).map a).sum = 0 := by
      have hsum := (hperm.map a).sum_eq
      simp only [List.map_cons, List.sum_cons] at hsum
      linarith
    obtain ⟨k, hk, hkbound⟩ :=
      exists_perm_bounded_weighted_partial_sums (l.erase x) a (s + a x) M hsy hrest htotal'
    refine ⟨x :: k, hperm.trans (hk.cons x), ?_⟩
    intro j
    cases j with
    | zero => simpa using hs
    | succ j => simpa [List.take_succ_cons, List.map_cons, List.sum_cons, add_assoc] using hkbound j
termination_by l.length
decreasing_by
  classical
  have hlength := (List.perm_cons_erase hx).length_eq
  simp only [List.length_cons] at hlength
  omega

end NoEpsilon
