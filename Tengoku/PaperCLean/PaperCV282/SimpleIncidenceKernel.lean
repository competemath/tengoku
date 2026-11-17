import Tengoku.PaperCLean.PaperCV282.SimpleIncidenceModel
import Tengoku.Seed.Algebra.Field.ZMod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The kernel of an actual incidence matrix

The row equations are precisely constancy along graph edges and vanishing
at pins. The historical graph resolution therefore computes the true matrix
nullity without a graph-rank hypothesis.
-/
namespace PaperC.V282.SimpleIncidenceKernel

open Matrix Finset SimpleGraph PinnedGraphResolution SimpleIncidenceModel

noncomputable section

/--
@isnad1 id=fact.0h0v.s2.2cde8ffc8dda from=translated src=- shape=8d7dbbf6 vocab=c1c9ca6d
-/
local instance instPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {R V : Type*} [Fintype R] [Fintype V] [DecidableEq V]

omit [Fintype R] [DecidableEq V] in
/-- Kernel membership is the literal row-support equation at every row.
@isnad1 id=iff.0h4v.s9.3e63346d4b1a from=translated src=- shape=7204843c vocab=3e701cd8
-/
theorem mem_kernel_iff_support_sums (H : Matrix R V F₂) (f : V → F₂) :
    f ∈ LinearMap.ker H.mulVecLin ↔ ∀ r, ∑ v ∈ rowSupport H r, f v = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h r
    rw [← mulVecLin_apply_eq_support_sum, h]
    rfl
  · intro h
    funext r
    exact (mulVecLin_apply_eq_support_sum H f r).trans (h r)

/-- No simplification or deletion is imposed on the zero rows and repeated pins.
@isnad1 id=eq.1h3v.s8.6707c0ebaf69 from=translated src=- shape=c418a367 vocab=b3d3281f
-/
theorem kernel_eq_pinnedGraphSpace (H : Matrix R V F₂)
    (hrow : ∀ r, (rowSupport H r).card ≤ 2) :
    LinearMap.ker H.mulVecLin = PinnedGraphSpace (incidenceGraph H) (pinnedColumns H) := by
  classical
  ext f
  rw [mem_kernel_iff_support_sums, mem_pinnedGraphSpace]
  constructor
  · intro hf
    constructor
    · rintro u v ⟨hne,r,hr⟩
      have hs := hf r
      rw [hr, Finset.sum_pair hne] at hs
      exact (eq_neg_of_add_eq_zero_left hs).trans (ZMod.neg_eq_self_mod_two (f v))
    · intro v hv
      obtain ⟨r, hr⟩ := (mem_pinnedColumns H v).mp hv
      simpa only [hr, Finset.sum_singleton] using hf r
  · rintro ⟨hedge,hpin⟩ r
    rcases row_shapes H r (hrow r) with hz | ⟨v,hv⟩ | ⟨u,v,hne,huv⟩
    · simp [hz]
    · rw [hv, Finset.sum_singleton]
      exact hpin v ((mem_pinnedColumns H v).mpr ⟨r,hv⟩)
    · rw [huv, Finset.sum_pair hne]
      have he : f u = f v := hedge ⟨hne,r,huv⟩
      calc
        f u + f v = -(f v) + f v := by rw [he, ZMod.neg_eq_self_mod_two]
        _ = 0 := neg_add_cancel (f v)

/-- Exact nullity: one coordinate for every unpinned connected component.
@isnad1 id=eq.1h3v.s10.ba55f0ebf388 from=translated src=- shape=75f0c398 vocab=9ee02ec4
-/
theorem finrank_kernel_eq_unpinned (H : Matrix R V F₂)
    (hrow : ∀ r, (rowSupport H r).card ≤ 2) :
    Module.finrank F₂ (LinearMap.ker H.mulVecLin) =
      Fintype.card (UnpinnedComponent (incidenceGraph H) (pinnedColumns H)) := by
  rw [kernel_eq_pinnedGraphSpace H hrow]
  exact finrank_pinnedGraphSpace _ _

/-- Rank plus the actual unpinned-component count equals the number of columns.
@isnad1 id=eq.1h3v.s6.d909c40e8ca7 from=translated src=- shape=2691f5b3 vocab=87576ee4
-/
theorem rank_add_unpinned_eq_card (H : Matrix R V F₂)
    (hrow : ∀ r, (rowSupport H r).card ≤ 2) :
    H.rank + Fintype.card (UnpinnedComponent (incidenceGraph H) (pinnedColumns H)) =
      Fintype.card V := by
  rw [← finrank_kernel_eq_unpinned H hrow, Matrix.rank]
  have h := LinearMap.finrank_range_add_finrank_ker (K := F₂) H.mulVecLin
  simpa only [Module.finrank_pi] using h

end
end PaperC.V282.SimpleIncidenceKernel
