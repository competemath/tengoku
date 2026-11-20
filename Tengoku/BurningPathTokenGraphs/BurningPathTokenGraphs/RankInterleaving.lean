import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.ContinuousCover
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact interleaving of normalized ranked covers

Local rank `j` from copy `a` is assigned global rank `M*j+a`. This rank
arithmetic supports cube replication and chamber permutation.
-/

namespace BurningPath

/-- The rank `M*j+a` as an embedding into a list of length `M*q`.-/
def interleavedRankEmbedding (M q : ℕ) (hM : 1 ≤ M) :
    Fin M × Fin q ↪ Fin (M * q) where
  toFun p := ⟨M * p.2.val + p.1.val, by
    calc
      M * p.2.val + p.1.val < M * p.2.val + M :=
        Nat.add_lt_add_left p.1.isLt _
      _ = M * (p.2.val + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ ≤ M * q := Nat.mul_le_mul_left M (Nat.add_one_le_iff.mpr p.2.isLt)⟩
  inj' := by
    rintro ⟨a, j⟩ ⟨b, l⟩ h
    have hab : a.val = b.val := by
      have hmod := congrArg (fun x ↦ x % M) (congrArg Fin.val h)
      simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt a.isLt,
        Nat.mod_eq_of_lt b.isLt] using hmod
    have hjl : j.val = l.val := by
      have hval := congrArg Fin.val h
      change M * j.val + a.val = M * l.val + b.val at hval
      rw [hab] at hval
      have hmul : M * j.val = M * l.val := Nat.add_right_cancel hval
      exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
    exact Prod.ext (Fin.ext hab) (Fin.ext hjl)

@[simp]
theorem interleavedRankEmbedding_val (M q : ℕ) (hM : 1 ≤ M)
    (a : Fin M) (j : Fin q) :
    (interleavedRankEmbedding M q hM (a, j)).val = M * j.val + a.val :=
  rfl

/-- Interleaving never decreases a local normalized radius.-/
theorem interleavedRank_normalized_le {M q : ℕ} (hM : 1 ≤ M)
    (hq : 1 ≤ q) (a : Fin M) (j : Fin q) :
    (j.val : ℝ) / q ≤
      ((interleavedRankEmbedding M q hM (a, j)).val : ℝ) / (M * q) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  rw [div_le_div_iff₀ hqpos (mul_pos hMpos hqpos)]
  have hnat :
      j.val * (M * q) ≤ (M * j.val + a.val) * q := by
    calc
      j.val * (M * q) = (M * j.val) * q := by ring
      _ ≤ (M * j.val + a.val) * q :=
        Nat.mul_le_mul_right q (Nat.le_add_right _ _)
  change
    (j.val : ℝ) * (M * q) ≤
      ((M * j.val + a.val : ℕ) : ℝ) * q
  exact_mod_cast hnat

/--
Interleave `M` local normalized covers of a common region.  The geometric
application supplies which copy and local rank cover each point.-/
theorem hasL1NormalizedRankedCover_interleave {k M q : ℕ}
    {S : Set (Fin k → ℝ)} (hM : 1 ≤ M) (hq : 1 ≤ q)
    (centers : Fin M → Fin q → (Fin k → ℝ))
    (hlegal : ∀ a j, centers a j ∈ S)
    (hcover :
      ∀ x ∈ S, ∃ a : Fin M, ∃ j : Fin q,
        realL1Dist x (centers a j) ≤ (j.val : ℝ) / q) :
    HasL1NormalizedRankedCover S (M * q) := by
  classical
  let e := interleavedRankEmbedding M q hM
  let localCenters : Fin M × Fin q → (Fin k → ℝ) :=
    fun p ↦ centers p.1 p.2
  let defaultCenter := centers ⟨0, by omega⟩ ⟨0, by omega⟩
  let globalCenters : Fin (M * q) → (Fin k → ℝ) :=
    Function.extend e localCenters (fun _ ↦ defaultCenter)
  have hglobal (a : Fin M) (j : Fin q) :
      globalCenters (e (a, j)) = centers a j := by
    exact e.injective.extend_apply localCenters (fun _ ↦ defaultCenter) (a, j)
  refine ⟨globalCenters, ?_, ?_⟩
  · intro r
    by_cases hr : r ∈ Set.range e
    · obtain ⟨⟨a, j⟩, rfl⟩ := hr
      rw [hglobal]
      exact hlegal a j
    · change Function.extend e localCenters (fun _ ↦ defaultCenter) r ∈ S
      rw [Function.extend_apply' localCenters (fun _ ↦ defaultCenter) r]
      · exact hlegal ⟨0, by omega⟩ ⟨0, by omega⟩
      · simpa only [Set.mem_range] using hr
  · intro x hx
    obtain ⟨a, j, hj⟩ := hcover x hx
    refine ⟨e (a, j), ?_⟩
    rw [hglobal]
    exact hj.trans (by simpa [e] using interleavedRank_normalized_le hM hq a j)

end BurningPath
