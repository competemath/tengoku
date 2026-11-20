import Tengoku.Rank3kum.Rank3KUM.HalfWeave.ParallelClasses
import Tengoku.Rank3kum.Rank3KUM.Interleave

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_uniformlyDense_rankTwo_flat` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_tight_rank_two` (it only prints; the queue checks the axioms of every declaration). -/

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/--
A uniformly dense rank-two flat of size `2k`, with a complement of size `k`,
canonically supplies the sorted half-weave enumeration and hence a cyclic
rank-three basis order.
@isnad1 id=ex.8h4v.s7.499ef17a2d8a from=translated src=- shape=2c8f9406 vocab=6061f39c
-/
theorem exists_cyclicBasisOrder3_of_uniformlyDense_rankTwo_flat
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hRestrictRank : (M.restrict X).eRank = 2)
    (hXflat : M.IsFlat X)
    (hXcard : X.encard = ((2 * k : ℕ) : ℕ∞))
    (hComplementCard : (M.E \ X).encard = (k : ℕ∞)) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  have hXfinite : X.Finite :=
    hE.subset hXflat.subset_ground
  let : Fintype X := hXfinite.fintype
  let : Fintype (M.restrict X).E :=
    Fintype.ofEquiv X (restrictGroundEquiv M X).symm
  let : DecidableEq (M.restrict X).E :=
    Classical.decEq _
  have hXncard : X.ncard = 2 * k := by
    have hcast : (X.ncard : ℕ∞) =
        ((2 * k : ℕ) : ℕ∞) := by
      rw [hXfinite.cast_ncard_eq]
      exact hXcard
    exact_mod_cast hcast
  have hRestrictCard :
      Fintype.card (M.restrict X).E = 2 * k := by
    calc
      Fintype.card (M.restrict X).E =
          Fintype.card X :=
        Fintype.card_congr (restrictGroundEquiv M X)
      _ = Nat.card X := Fintype.card_eq_nat_card
      _ = X.ncard := by
        simp only [Nat.card_coe_set_eq]
      _ = 2 * k := hXncard
  have hRestrictDense : UniformlyDense (M.restrict X) k :=
    UniformlyDense.restrict M k hDense hXflat.subset_ground
  have hRestrictLoopless : (M.restrict X).Loopless :=
    loopless_of_uniformlyDense
      (M.restrict X) k hk hRestrictDense
  let D :=
    HalfWeave.rankTwoSortedEnumerationOfUniformlyDense
      (M.restrict X) k hRestrictCard hRestrictDense
      hRestrictLoopless hRestrictRank
  exact
    exists_cyclicBasisOrder3_of_sortedEnumeration_tight_flat
      M hk hE hRank hRestrictRank hXflat
      hComplementCard D

/--
The rank-two side of the tight-set classification now discharges all
enumeration, restriction-rank, flatness, and complement-cardinality data.
@isnad1 id=ex.7h4v.s7.c69b9ec06b7e from=translated src=- shape=f09e4e98 vocab=d299b271
-/
theorem exists_cyclicBasisOrder3_of_tight_rank_two
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hX : Tight M k X)
    (hXrank : M.eRk X = 2) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  have hXflat : M.IsFlat X :=
    tight_isFlat M k hE hDense hX
  have hXcard :
      X.encard = ((2 * k : ℕ) : ℕ∞) :=
    tight_encard_eq_two_mul_k_of_eRk_eq_two
      M k hX hXrank
  have hsum :
      X.encard + (M.E \ X).encard = M.E.encard := by
    rw [← Set.encard_union_eq Set.disjoint_sdiff_right,
      Set.union_sdiff_cancel hX.1]
  have hComplementCard :
      (M.E \ X).encard = (k : ℕ∞) := by
    apply ENat.add_right_injective_of_ne_top
      (ENat.natCast_ne_top (2 * k))
    calc
      ((2 * k : ℕ) : ℕ∞) + (M.E \ X).encard =
          X.encard + (M.E \ X).encard := by
        rw [hXcard]
      _ = M.E.encard := hsum
      _ = ((3 * k : ℕ) : ℕ∞) := hEcard
      _ = ((2 * k : ℕ) : ℕ∞) + (k : ℕ∞) := by
        rw [← ENat.natCast_add]
        congr 1
        omega
  have hRestrictRank :
      (M.restrict X).eRank = 2 := by
    rw [Matroid.eRank_def,
      Matroid.restrict_ground_eq,
      M.restrict_eRk_eq Set.Subset.rfl, hXrank]
  exact
    exists_cyclicBasisOrder3_of_uniformlyDense_rankTwo_flat
      M k hk hE hRank hDense hRestrictRank
      hXflat hXcard hComplementCard

end

end Rank3KUM
