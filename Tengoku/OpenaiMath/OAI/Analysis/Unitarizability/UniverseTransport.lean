import Tengoku.OpenaiMath.OAI.Analysis.Unitarizability.Main
import Tengoku

namespace OAI

/-! Countability lets a group be represented in any universe.
Transport by group equivalences preserves the positive normalized invariant mean
and the bounded nonunitarizable witness. -/
noncomputable section
namespace Dixmier
universe u v w
open scoped BoundedContinuousFunction
variable {G : Type u} {Q : Type v} [Group G] [Group Q]
variable [TopologicalSpace G] [DiscreteTopology G]
variable [TopologicalSpace Q] [DiscreteTopology Q]

def meanPullback (e : G ≃* Q) : (G →ᵇ ℂ) →ₗ[ℂ] (Q →ᵇ ℂ) where
  toFun f := f.compContinuous ⟨e.symm, continuous_of_discreteTopology⟩
  map_add' f h := by ext q; rfl
  map_smul' z f := by ext q; rfl

omit [DiscreteTopology G] in
@[simp] theorem meanPullback_apply (e : G ≃* Q) (f : G →ᵇ ℂ) (q : Q) :
    meanPullback e f q = f (e.symm q) := rfl

/-- Amenability transport uses the same positive normalized invariant mean. -/
theorem amenable_of_mulEquiv (e : G ≃* Q) (hQ : Amenable Q) : Amenable G := by
  rcases hQ with ⟨m, h1, hp, hi⟩
  refine ⟨m.comp (meanPullback e), ?_, ?_, ?_⟩
  · have hc : meanPullback e (BoundedContinuousFunction.const G 1) =
        BoundedContinuousFunction.const Q 1 := by ext q; rfl
    simpa only [LinearMap.comp_apply, hc] using h1
  · intro f hf
    exact hp _ (fun q => hf (e.symm q))
  · intro g f
    have hc : meanPullback e (leftTranslate g f) = leftTranslate (e g) (meanPullback e f) := by
      ext q
      simp [meanPullback_apply, leftTranslate, map_mul, map_inv]
    simpa only [LinearMap.comp_apply, hc] using hi (e g) (meanPullback e f)

omit [TopologicalSpace G] [DiscreteTopology G] [TopologicalSpace Q] [DiscreteTopology Q] in
/-- Reindexing the group does not change the Hilbert space, bound or similarities. -/
theorem witness_of_mulEquiv (e : G ≃* Q) (hQ : NonamenableWitness.{v,w} Q) :
    NonamenableWitness.{u,w} G := by
  rcases hQ with ⟨H, hnorm, hinner, hcomplete, hsep, π, hb, hn⟩
  refine ⟨H, hnorm, hinner, hcomplete, hsep, π.comp e.toMonoidHom, fun g => hb (e g), ?_⟩
  rintro ⟨S, hS⟩
  apply hn
  refine ⟨S, ?_⟩
  intro q x
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.apply_symm_apply] using hS (e.symm q) x

end Dixmier

end

end OAI
