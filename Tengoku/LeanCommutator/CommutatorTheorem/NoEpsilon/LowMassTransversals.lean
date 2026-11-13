import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.MSSSelection
import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.LowMassRecurrence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/WuProver/lean-commutator@2f197491d436, `CommutatorTheorem/NoEpsilon/LowMassTransversals.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# Exact quotas in the balanced binary selection tree

The analytic paired-selection assertion is an explicit premise here. All index permutations,
quotas, coverage, and propagation of the operator norm bound are proved in this file.
-/

open scoped BigOperators Matrix.Norms.L2Operator

namespace NoEpsilon.LowMassPaving

open MSSSelection

noncomputable def splitBound (δ L : ℝ) : ℝ :=
  (Real.sqrt L + 2 * Real.sqrt δ) ^ 2 / 2

/--
@isnad1 id=le.0h2v.s4.4491d0d17b2e from=translated src=- shape=a120b2a8 vocab=435812e7
-/
theorem splitBound_nonneg (δ L : ℝ) : 0 ≤ splitBound δ L := by
  unfold splitBound
  positivity

/-- The sole analytic input to the finite quota construction.-/
def PairedHalfSelection (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ {κ : Type} [Fintype κ] (a b : κ → ι → ℂ) (δ L : ℝ),
    0 ≤ δ → 0 ≤ L → (∀ i, energy (a i) ≤ δ) → (∀ i, energy (b i) ≤ δ) →
    ‖∑ i, (outer (a i) + outer (b i))‖ ≤ L →
    ∃ q : κ → Bool × Bool,
      ‖∑ i, outer (firstVector a b q i)‖ ≤ splitBound δ L ∧
      ‖∑ i, outer (secondVector a b q i)‖ ≤ splitBound δ L

/-- A depth-indexed binary type without arithmetic casts at a split.-/
def BinaryIndex : ℕ → Type
  | 0 => Unit
  | h + 1 => Bool × BinaryIndex h

instance binaryIndexFintype : (h : ℕ) → Fintype (BinaryIndex h)
  | 0 => inferInstanceAs (Fintype Unit)
  | h + 1 =>
    letI := binaryIndexFintype h
    inferInstanceAs (Fintype (Bool × BinaryIndex h))

instance binaryIndexDecidableEq : (h : ℕ) → DecidableEq (BinaryIndex h)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | h + 1 =>
    letI := binaryIndexDecidableEq h
    inferInstanceAs (DecidableEq (Bool × BinaryIndex h))

def branchPermutation {α : Type*} (e : Bool → Equiv.Perm α) :
    Equiv.Perm (Bool × α) where
  toFun p := (p.1, e p.1 p.2)
  invFun p := (p.1, (e p.1).symm p.2)
  left_inv p := by simp
  right_inv p := by simp

def flipPermutation {α : Type*} (s : α → Bool) : Equiv.Perm (Bool × α) where
  toFun p := (p.1.xor (s p.2), p.2)
  invFun p := (p.1.xor (s p.2), p.2)
  left_inv p := by
    rcases p with ⟨b, x⟩
    change ((b.xor (s x)).xor (s x), x) = (b, x)
    cases b <;> cases s x <;> rfl
  right_inv p := by
    rcases p with ⟨b, x⟩
    change ((b.xor (s x)).xor (s x), x) = (b, x)
    cases b <;> cases s x <;> rfl

noncomputable def treeBound (δ : ℝ) (h : ℕ) (L : ℝ) : ℝ :=
  (splitBound δ)^[h] L

/--
@isnad1 id=le.1h3v.s4.86e3ea901779 from=translated src=- shape=b86a77a8 vocab=35b1a65b
-/
theorem treeBound_nonneg (δ : ℝ) (h : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    0 ≤ treeBound δ h L := by
  induction h with
  | zero => exact hL
  | succ h ih =>
    simpa only [treeBound, Function.iterate_succ_apply'] using
      splitBound_nonneg δ (treeBound δ h L)

-- Preserve the existing parameter list for downstream callers.
/--
@isnad1 id=eq.0h4v.s7.469bba79eefb from=translated src=- shape=3eca7193 vocab=4d2e6011
-/
theorem binary_sum_split {ι : Type*} [Fintype ι] {k h : ℕ}
    (f : Fin k → BinaryIndex (h + 1) → ι → ℂ) :
    (∑ j, ∑ x, outer (f j x)) =
      ∑ p : Fin k × BinaryIndex h,
        (outer (f p.1 (false, p.2)) + outer (f p.1 (true, p.2))) := by
  change (∑ j, ∑ x : Bool × BinaryIndex h, outer (f j x)) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro x _
  exact add_comm _ _

/--
@isnad1 id=eq.0h5v.s7.0dcd45d3973d from=translated src=- shape=9fb5dc80 vocab=a0bf1331
-/
theorem sum_permuted_vectors {ι κ : Type*} [Fintype ι] [Fintype κ]
    {k : ℕ} (f : Fin k → κ → ι → ℂ) (σ : Fin k → Equiv.Perm κ) :
    (∑ x, ∑ j, outer (f j (σ j x))) = ∑ j, ∑ x, outer (f j x) := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ ↦ Equiv.sum_comp (σ j) (fun x ↦ outer (f j x)))

end NoEpsilon.LowMassPaving
