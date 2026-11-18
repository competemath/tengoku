import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_ValuationSubring_exists_ringHom_extend_of_isAlgClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsAlgClosed_exists_valuationSubring_ringHom_retraction.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsAlgClosed_exists_valuationSubring_ringHom_retraction

set_option autoImplicit false

theorem solution
    (K K' : Type*) [Field K] [IsAlgClosed K] [Field K'] [Algebra K K'] :
    ∃ (A : ValuationSubring K') (hK : ∀ c : K, algebraMap K K' c ∈ A) (σ : A →+* K),
      RingHom.ker σ = IsLocalRing.maximalIdeal A ∧
      ∀ c : K, σ ⟨algebraMap K K' c, hK c⟩ = c := by
  let f : K →+* K' := algebraMap K K'
  let e : K ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun a b h => f.injective (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  obtain ⟨O, hRO, ψ, hψ, hker⟩ :=
    ValuationSubring.exists_ringHom_extend_of_isAlgClosed (Ω := K) f.range e.symm.toRingHom
  refine ⟨O, fun c => hRO ⟨c, rfl⟩, ψ, hker, fun c => ?_⟩
  have h1 : ψ (Subring.inclusion hRO ⟨f c, ⟨c, rfl⟩⟩) = e.symm ⟨f c, ⟨c, rfl⟩⟩ := by
    rw [← RingHom.comp_apply, hψ]; rfl
  have h2 : e.symm ⟨f c, ⟨c, rfl⟩⟩ = c := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    rfl
  rw [h2] at h1
  exact h1
