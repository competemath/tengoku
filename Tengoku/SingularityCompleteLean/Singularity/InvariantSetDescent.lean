import Tengoku.Seed.MeasureTheory.Group.Action
import Tengoku.Seed.MeasureTheory.Group.FundamentalDomain

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Descending almost-invariant sets to an orbit quotient

For a countable group, intersecting all translates of an almost-invariant
measurable set gives an exactly invariant measurable representative in the
same measure class. Its image is measurable in the quotient sigma algebra,
so no measurable choice of coset representatives is required.
-/

noncomputable section
open Set Filter MeasureTheory

namespace Singularity

/-- The largest invariant subset obtained by intersecting all inverse translates.-/
def invariantSetCore (G X : Type*) [SMul G X] (s : Set X) : Set X :=
  ⋂ g : G, (fun x : X => g • x) ⁻¹' s

/-- Group translation preserves the core exactly.
@isnad1 id=eq.0h4v.s6.9c08d6333b2b from=translated src=- shape=4ab52c2d vocab=d5bfb911
-/
theorem preimage_invariantSetCore {G X : Type*} [Group G] [MulAction G X]
    (s : Set X) (g : G) :
    (fun x : X => g • x) ⁻¹' invariantSetCore G X s = invariantSetCore G X s := by
  ext x
  simp only [invariantSetCore, mem_preimage, mem_iInter]
  constructor
  · intro h a
    simpa only [mul_smul, inv_smul_smul] using h (a * g⁻¹)
  · intro h a
    simpa only [mul_smul] using h (a * g)

/--
@isnad1 id=measurab.1h3v.s5.d0af3e2abdf5 from=translated src=- shape=84e638f9 vocab=2801d259
-/
theorem invariantSetCore_measurable {G X : Type*} [Countable G] [SMul G X]
    [MeasurableSpace X] [MeasurableConstSMul G X] {s : Set X} (hs : MeasurableSet s) :
    MeasurableSet (invariantSetCore G X s) :=
  MeasurableSet.iInter (fun g => hs.preimage (measurable_const_smul g))

/-- Saturating the core adds no new points.
@isnad1 id=eq.0h3v.s6.39c1f68eebf7 from=translated src=- shape=17e79195 vocab=e07cf916
-/
theorem quotient_preimage_image_invariantSetCore {G X : Type*} [Group G] [MulAction G X]
    (s : Set X) :
    Quotient.mk (MulAction.orbitRel G X) ⁻¹'
      (Quotient.mk (MulAction.orbitRel G X) '' invariantSetCore G X s) = invariantSetCore G X s := by
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (Quotient.exact hyx))
    rw [← hg] at hy
    change x ∈ (fun z : X => g • z) ⁻¹' invariantSetCore G X s at hy
    rwa [preimage_invariantSetCore] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

end Singularity
