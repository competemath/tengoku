import Tengoku.LeanCommutator.KadisonSinger.States

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Purity of the unique state extension

An extension unique among all states is pure whenever its restriction is pure.
This is the elementary extreme-point argument, separate from the paving theorem.
-/

noncomputable section
open scoped ComplexOrder
namespace KadisonSinger.State

variable {A D : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [StarOrderedRing A] in
/-- The one-endpoint definition of purity is equivalent to the usual requirement
that both endpoints of every nontrivial convex decomposition equal the state.
@isnad1 id=iff.0h2v.s9.6e858c295e94 from=translated src=- shape=4f7ad44c vocab=560ab774
-/
theorem isPure_iff_extreme (φ : KadisonSinger.State A) :
    φ.IsPure ↔ ∀ (ψ χ : KadisonSinger.State A) (t : ℝ), 0 < t → t < 1 →
      (∀ a, φ.val a = t • ψ.val a + (1-t) • χ.val a) → ψ = φ ∧ χ = φ := by
  constructor
  · intro hφ ψ χ t ht ht' hdecomp
    refine ⟨hφ ψ χ t ht ht' hdecomp, ?_⟩
    apply hφ χ ψ (1-t) (sub_pos.mpr ht') (by linarith)
    intro a
    simpa only [sub_sub_cancel, add_comm] using hdecomp a
  · intro hφ ψ χ t ht ht' hdecomp
    exact (hφ ψ χ t ht ht' hdecomp).1

/-- Restrict a state along a unital star-algebra homomorphism.-/
def restrict (ψ : KadisonSinger.State A) (ι : D →⋆ₐ[ℂ] A) : KadisonSinger.State D :=
  ⟨{ toLinearMap := ψ.val.toLinearMap.comp ι.toAlgHom.toLinearMap
     monotone' := fun _ _ h ↦ OrderHomClass.mono ψ.val (OrderHomClass.mono ι h) }, by
    change ψ.val (ι 1) = 1
    rw [map_one, ψ.apply_one]⟩

/--
@isnad1 id=eq.0h5v.s9.eb51babf7482 from=translated src=- shape=65ef1492 vocab=c5e469d2
-/
lemma restrict_apply (ψ : KadisonSinger.State A) (ι : D →⋆ₐ[ℂ] A) (d : D) :
    (ψ.restrict ι).val d = ψ.val (ι d) := rfl

/-- The unique extension of a pure state is itself pure. Uniqueness here is among
all states, not merely among pure states.
@isnad1 id=ispure.3h5v.s10.061dff74ba92 from=translated src=- shape=c8e0a41f vocab=2d8a1aae
-/
theorem isPure_of_unique_extension (ι : D →⋆ₐ[ℂ] A)
    (φ : KadisonSinger.State D) (hφ : φ.IsPure) (ψ : KadisonSinger.State A)
    (hψ : ∀ d, ψ.val (ι d) = φ.val d)
    (hunique : ∀ χ : KadisonSinger.State A, (∀ d, χ.val (ι d) = φ.val d) → χ = ψ) :
    ψ.IsPure := by
  intro χ ξ t ht ht' hdecomp
  have hrestrict : χ.restrict ι = φ := by
    apply hφ (χ.restrict ι) (ξ.restrict ι) t ht ht'
    intro d
    simpa only [restrict_apply, hψ] using hdecomp (ι d)
  apply hunique χ
  intro d
  have h := congrArg (fun ρ : KadisonSinger.State D ↦ ρ.val d) hrestrict
  exact h

/-- Unique state extension supplies a unique pure extension as well.
@isnad1 id=existsun.2h4v.s10.7f399c8b59e3 from=translated src=- shape=20a921c6 vocab=d0675afe
-/
theorem existsUnique_pure_extension (ι : D →⋆ₐ[ℂ] A)
    (φ : KadisonSinger.State D) (hφ : φ.IsPure)
    (h : ∃! ψ : KadisonSinger.State A, ∀ d, ψ.val (ι d) = φ.val d) :
    ∃! ψ : KadisonSinger.State A, ψ.IsPure ∧ ∀ d, ψ.val (ι d) = φ.val d := by
  obtain ⟨ψ, hψ, huniq⟩ := h
  refine ⟨ψ, ⟨isPure_of_unique_extension ι φ hφ ψ hψ huniq, hψ⟩, ?_⟩
  intro χ hχ
  exact huniq χ hχ.2

end KadisonSinger.State

namespace KadisonSinger.State
variable {A D : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CommCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

end KadisonSinger.State
