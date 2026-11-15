import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_HeckePair

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open scoped Pointwise ENNReal
open MulAction MeasureTheory

namespace HeckeIntegralSeam

section CosetSystem

variable {G : Type*} [Group G]

structure IsHeckeCosetSystem (U : Subgroup G) (g : G) {ι : Type*} (reps : ι → G) : Prop where

  mem_doubleCoset : ∀ i, reps i ∈ HeckePair.doubleCoset U g

  covers : ∀ x ∈ HeckePair.doubleCoset U g,
    ∃ i, (QuotientGroup.mk x : G ⧸ U) = QuotientGroup.mk (reps i)

  mk_injective : Function.Injective fun i => (QuotientGroup.mk (reps i) : G ⧸ U)

variable {U : Subgroup G} {g : G}

/--
@isnad1 id=iff.0h4v.s6.078f2b305b3f from=translated src=- shape=54d5d078 vocab=b1f01277
-/
theorem mem_smul_coe_iff {y x : G} :
    x ∈ y • (U : Set G) ↔ (QuotientGroup.mk y : G ⧸ U) = QuotientGroup.mk x := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, SetLike.mem_coe, QuotientGroup.eq]

/--
@isnad1 id=le.0h3v.s5.262b05bf698d from=translated src=- shape=2c03edd7 vocab=d32a103a
-/
theorem mulSet_subset_doubleCoset : (U : Set G) * {g} ⊆ HeckePair.doubleCoset U g := by
  intro x hx
  obtain ⟨u, hu, w, hw, rfl⟩ := Set.mem_mul.mp hx
  obtain rfl : w = g := hw
  exact HeckePair.mem_doubleCoset_iff.mpr ⟨u, hu, 1, one_mem U, by group⟩

/--
@isnad1 id=mem.1h4v.s5.14aff6ec83ec from=translated src=- shape=459c2fcc vocab=f68f5036
-/
theorem out_mk_mem_doubleCoset {x : G} (hx : x ∈ HeckePair.doubleCoset U g) :
    Quotient.out (QuotientGroup.mk x : G ⧸ U) ∈ HeckePair.doubleCoset U g := by
  have hmem : Quotient.out (QuotientGroup.mk x : G ⧸ U) ∈ x • (U : Set G) :=
    mem_smul_coe_iff.mpr (QuotientGroup.out_eq' _).symm
  obtain ⟨u, hu, hux⟩ := Set.mem_smul_set.mp hmem
  rw [← hux, smul_eq_mul]
  exact HeckePair.doubleCoset_mul_mem hx hu

namespace IsHeckeCosetSystem

variable {ι : Type*} {reps : ι → G}

/--
@isnad1 id=le.1h6v.s6.83c1f694b908 from=translated src=- shape=08087e51 vocab=a788bfbd
-/
theorem smul_subset (hsys : IsHeckeCosetSystem U g reps) (i : ι) :
    reps i • (U : Set G) ⊆ HeckePair.doubleCoset U g := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp hx
  rw [smul_eq_mul]
  exact HeckePair.doubleCoset_mul_mem (hsys.mem_doubleCoset i) hu

/--
@isnad1 id=eq.1h5v.s6.4413b3d8376b from=translated src=- shape=0625e92b vocab=376463e4
-/
theorem doubleCoset_eq_iUnion (hsys : IsHeckeCosetSystem U g reps) :
    HeckePair.doubleCoset U g = ⋃ i, reps i • (U : Set G) := by
  refine Set.Subset.antisymm (fun x hx => ?_) (Set.iUnion_subset fun i => hsys.smul_subset i)
  obtain ⟨i, hi⟩ := hsys.covers x hx
  exact Set.mem_iUnion.mpr ⟨i, mem_smul_coe_iff.mpr hi.symm⟩

/--
@isnad1 id=disjoint.2h7v.s7.9350e03ae718 from=translated src=- shape=a694f336 vocab=2f786b2e
-/
theorem disjoint (hsys : IsHeckeCosetSystem U g reps) {i j : ι} (hij : i ≠ j) :
    Disjoint (reps i • (U : Set G)) (reps j • (U : Set G)) := by
  refine Set.disjoint_left.mpr fun x hxi hxj => hij ?_
  exact hsys.mk_injective ((mem_smul_coe_iff.mp hxi).trans (mem_smul_coe_iff.mp hxj).symm)

/--
@isnad1 id=injectiv.1h5v.s4.5c186678ad91 from=translated src=- shape=b14e67d9 vocab=7e7603cf
-/
theorem reps_injective (hsys : IsHeckeCosetSystem U g reps) : Function.Injective reps :=
  fun i j hij => hsys.mk_injective (by simp only [hij])

end IsHeckeCosetSystem

/--
@isnad1 id=isheckec.1h3v.s8.6299202a6b49 from=translated src=- shape=b32e6f26 vocab=cfbb7c69
-/
theorem canonical_isHeckeCosetSystem
    (hfin : (QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ U)).Finite) :
    IsHeckeCosetSystem U g (fun q : ↥hfin.toFinset => Quotient.out (q : G ⧸ U)) := by
  constructor
  · rintro ⟨q, hq⟩
    rw [Set.Finite.mem_toFinset] at hq
    obtain ⟨z, hz, rfl⟩ := hq
    exact out_mk_mem_doubleCoset (mulSet_subset_doubleCoset hz)
  · intro x hx
    have hmk : (QuotientGroup.mk x : G ⧸ U) ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset, ← HeckePair.image_mk_doubleCoset g]
      exact Set.mem_image_of_mem _ hx
    exact ⟨⟨QuotientGroup.mk x, hmk⟩, (QuotientGroup.out_eq' _).symm⟩
  · intro q q' h
    refine Subtype.ext ?_
    have h' : QuotientGroup.mk (Quotient.out (q : G ⧸ U))
        = QuotientGroup.mk (Quotient.out (q' : G ⧸ U)) := h
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h'

end CosetSystem

section Volume

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
variable {U : Subgroup G} {g : G}

/--
@isnad1 id=eq.0h3v.s6.6dc26a4b39a7 from=translated src=- shape=280f75b5 vocab=4d3a28d0
-/
theorem smul_coe_eq_preimage (y : G) :
    y • (U : Set G) = (fun x => y⁻¹ * x) ⁻¹' (U : Set G) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  rfl

/--
@isnad1 id=measurab.1h3v.s6.32456e275941 from=translated src=- shape=26a0ad0a vocab=17396b04
-/
theorem measurableSet_smul_coe (hU : MeasurableSet (U : Set G)) (y : G) :
    MeasurableSet (y • (U : Set G)) := by
  rw [smul_coe_eq_preimage]
  exact (measurable_const_mul y⁻¹) hU

/--
@isnad1 id=eq.0h4v.s6.c9a9ef56acc2 from=translated src=- shape=7bbfc953 vocab=ae976556
-/
theorem measure_smul_coe (μ : Measure G) [μ.IsMulLeftInvariant] (y : G) :
    μ (y • (U : Set G)) = μ (U : Set G) := by
  rw [smul_coe_eq_preimage]
  exact measure_preimage_mul μ y⁻¹ _

/--
@isnad1 id=eq.2h6v.s7.4cdcf948afe2 from=translated src=- shape=08a52088 vocab=b5dff7cf
-/
theorem IsHeckeCosetSystem.measure_doubleCoset {ι : Type*} [Fintype ι] {reps : ι → G}
    (hsys : IsHeckeCosetSystem U g reps) (μ : Measure G) [μ.IsMulLeftInvariant]
    (hU : MeasurableSet (U : Set G)) :
    μ (HeckePair.doubleCoset U g) = (Fintype.card ι : ℝ≥0∞) * μ (U : Set G) := by
  classical
  rw [hsys.doubleCoset_eq_iUnion]
  have hbU : (⋃ i, reps i • (U : Set G))
      = ⋃ i ∈ (Finset.univ : Finset ι), reps i • (U : Set G) := by
    simp
  rw [hbU, measure_biUnion_finset (fun i _ j _ hij => hsys.disjoint hij)
    (fun i _ => measurableSet_smul_coe hU (reps i))]
  rw [Finset.sum_congr rfl fun i _ => measure_smul_coe μ (reps i), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

/--
@isnad1 id=measurab.2h5v.s6.7a9fb93443a0 from=translated src=- shape=91e01e1a vocab=8c750899
-/
theorem IsHeckeCosetSystem.measurableSet_doubleCoset {ι : Type*} [Fintype ι] {reps : ι → G}
    (hsys : IsHeckeCosetSystem U g reps) (hU : MeasurableSet (U : Set G)) :
    MeasurableSet (HeckePair.doubleCoset U g) := by
  rw [hsys.doubleCoset_eq_iUnion]
  exact MeasurableSet.iUnion fun i => measurableSet_smul_coe hU (reps i)

end Volume

end HeckeIntegralSeam
