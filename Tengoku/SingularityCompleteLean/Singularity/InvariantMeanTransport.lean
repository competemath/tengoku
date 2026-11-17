import Tengoku.SingularityCompleteLean.Singularity.InvariantMean
import Tengoku.Seed.GroupTheory.Coset.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Invariant means pass to subgroups

An equivariant coordinate map along chosen coset representatives pulls a mean
on the ambient group back to a mean on a subgroup. This establishes the precise
heredity statement needed to use a free subgroup for nonamenability.
-/

noncomputable section
open Set
open scoped Classical

namespace Singularity

/-- A nonnegative finitely additive set function is monotone.
@isnad1 id=le.3h4v.s6.2ba3ee88ebfd from=translated src=- shape=f7f4d099 vocab=66043f1f
-/
theorem invariantMean_mono {X : Type*} (m : Set X → ℝ) (hpos : ∀ A, 0 ≤ m A)
    (hadd : ∀ A B, Disjoint A B → m (A ∪ B) = m A + m B)
    {A B : Set X} (hAB : A ⊆ B) : m A ≤ m B := by
  have h := hadd A (B \ A) Set.disjoint_sdiff_right
  have he : A ∪ (B \ A) = B := by
    ext x
    simp only [mem_union, mem_sdiff]
    constructor
    · rintro (ha | ⟨hb, _⟩)
      · exact hAB ha
      · exact hb
    · intro hb
      by_cases ha : x ∈ A
      · exact Or.inl ha
      · exact Or.inr ⟨hb, ha⟩
  rw [he] at h
  linarith [hpos (B \ A)]

/-- An equivariant map transports a left invariant mean by preimages.
@isnad1 id=hasinvar.2h4v.s7.06438efb6ba7 from=translated src=- shape=91b43f32 vocab=82ac8750
-/
theorem hasInvariantMean_of_equivariant_map {G H : Type*} [Group G] [Group H]
    (j : H →* G) (p : G → H) (hp : ∀ h x, p (j h * x) = h * p x)
    (hm : HasInvariantMean G) : HasInvariantMean H := by
  obtain ⟨m, hpos, hemp, huniv, hadd, hinv⟩ := hm
  refine ⟨fun A => m (p ⁻¹' A), fun A => hpos _, ?_, ?_, ?_, ?_⟩
  · simpa only [preimage_empty] using hemp
  · simpa only [preimage_univ] using huniv
  · intro A B hAB
    dsimp only
    rw [preimage_union]
    exact hadd _ _ (hAB.preimage p)
  · intro h A
    have he : p ⁻¹' ((fun y => h * y) '' A) = (fun x => j h * x) '' (p ⁻¹' A) := by
      ext x
      constructor
      · rintro ⟨y, hy, hxy⟩
        refine ⟨j h⁻¹ * x, ?_, by simp⟩
        change p (j h⁻¹ * x) ∈ A
        rw [hp, ← hxy]
        simpa using hy
      · rintro ⟨y, hy, rfl⟩
        exact ⟨p y, hy, (hp h y).symm⟩
    dsimp only
    rw [he, hinv]

/-- The right-translation version of equivariant transport.
@isnad1 id=hasright.2h4v.s7.0433b78ec519 from=translated src=- shape=7d677053 vocab=04e90ba2
-/
theorem hasRightInvariantMean_of_equivariant_map {G H : Type*} [Group G] [Group H]
    (j : H →* G) (p : G → H) (hp : ∀ h x, p (x * j h) = p x * h)
    (hm : HasRightInvariantMean G) : HasRightInvariantMean H := by
  obtain ⟨m, hpos, hemp, huniv, hadd, hinv⟩ := hm
  refine ⟨fun A => m (p ⁻¹' A), fun A => hpos _, ?_, ?_, ?_, ?_⟩
  · simpa only [preimage_empty] using hemp
  · simpa only [preimage_univ] using huniv
  · intro A B hAB
    dsimp only
    rw [preimage_union]
    exact hadd _ _ (hAB.preimage p)
  · intro h A
    have he : p ⁻¹' ((fun y => y * h) '' A) = (fun x => x * j h) '' (p ⁻¹' A) := by
      ext x
      constructor
      · rintro ⟨y, hy, hxy⟩
        refine ⟨x * j h⁻¹, ?_, by simp [mul_assoc]⟩
        change p (x * j h⁻¹) ∈ A
        rw [hp, ← hxy]
        simpa only [mul_inv_cancel_right] using hy
      · rintro ⟨y, hy, rfl⟩
        exact ⟨p y, hy, (hp h y).symm⟩
    dsimp only
    rw [he, hinv]

/-- The subgroup coordinate in a chosen left-coset representative.-/
def subgroupRightCoordinate {G : Type*} [Group G] (H : Subgroup G) (x : G) : H :=
  ⟨(Quotient.out (QuotientGroup.mk x : G ⧸ H))⁻¹ * x,
    QuotientGroup.leftRel_apply.mp (Quotient.exact' (Quotient.out_eq' _))⟩

/-- Right multiplication by subgroup elements leaves the coset representative fixed.
@isnad1 id=eq.0h4v.s7.e9bf1d7a8e01 from=translated src=- shape=6b5f2b60 vocab=1e46c8fd
-/
theorem subgroupRightCoordinate_mul {G : Type*} [Group G] (H : Subgroup G)
    (h : H) (x : G) : subgroupRightCoordinate H (x * h) = subgroupRightCoordinate H x * h := by
  apply Subtype.ext
  change (Quotient.out (QuotientGroup.mk (x * h) : G ⧸ H))⁻¹ * (x * h) =
    ((Quotient.out (QuotientGroup.mk x : G ⧸ H))⁻¹ * x) * h
  rw [QuotientGroup.mk_mul_of_mem x h.property, mul_assoc]

/-- A right invariant mean on a group induces one on each subgroup.
@isnad1 id=hasright.1h2v.s5.365813488a25 from=translated src=- shape=4b15469b vocab=f01d0ea8
-/
theorem hasRightInvariantMean_subgroup {G : Type*} [Group G] (H : Subgroup G)
    (hm : HasRightInvariantMean G) : HasRightInvariantMean H :=
  hasRightInvariantMean_of_equivariant_map H.subtype (subgroupRightCoordinate H)
    (subgroupRightCoordinate_mul H) hm

/-- Amenability is inherited by subgroups, in the classical set-function formulation.
@isnad1 id=hasinvar.1h2v.s5.4f553e7d3125 from=translated src=- shape=4b15469b vocab=2382cf56
-/
theorem hasInvariantMean_subgroup {G : Type*} [Group G] (H : Subgroup G)
    (hm : HasInvariantMean G) : HasInvariantMean H :=
  (hasInvariantMean_iff_right H).mpr
    (hasRightInvariantMean_subgroup H ((hasInvariantMean_iff_right G).mp hm))

/-- An injective group homomorphism transfers an ambient invariant mean to its domain.
@isnad1 id=hasinvar.2h3v.s6.a0e0fccbbf10 from=translated src=- shape=2be079fb vocab=34d6a2f8
-/
theorem hasInvariantMean_of_injective {G H : Type*} [Group G] [Group H]
    (j : H →* G) (hj : Function.Injective j) (hm : HasInvariantMean G) : HasInvariantMean H := by
  let e : H ≃* j.range := MonoidHom.ofInjective hj
  apply hasInvariantMean_of_equivariant_map e.toMonoidHom e.symm
    (fun h x => by simp)
  exact hasInvariantMean_subgroup j.range hm

end Singularity
