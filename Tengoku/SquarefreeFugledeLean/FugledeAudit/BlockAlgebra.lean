import Tengoku.Seed.Algebra.Module.LinearMap.Basic
import Tengoku.Seed.Algebra.Module.Submodule.Basic
import Tengoku.Seed.Analysis.Normed.Group.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Selected algebraic steps in the square-free manuscript

These are component lemmas, not a formalization of Lemma 3.2 as a whole.
In particular the sparse-power identities and injectivity of the shift block
are hypotheses here. Their derivation from spectrality is NOT checked here.
-/

namespace FugledeAudit

/-- The cancellation used after the shift-one blocks of U² and U³ vanish.
The two level spaces may be different; no identification is assumed.
@isnad1 id=eq.3h6v.s10.4bb0af603b33 from=translated src=- shape=f1efdf1e vocab=5008f5ba
-/
theorem shift_block_square_zero
    {𝕜 V W : Type*} [Field 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
    (D : V →ₗ[𝕜] V) (E : W →ₗ[𝕜] W) (S : W →ₗ[𝕜] V)
    (hS : Function.Injective S)
    (h₂ : D.comp S + S.comp E = 0)
    (h₃ : (D.comp D).comp S + (D.comp S).comp E + S.comp (E.comp E) = 0) :
    E.comp E = 0 := by
  have hcancel : (D.comp D).comp S + (D.comp S).comp E = 0 := by
    rw [LinearMap.comp_assoc, LinearMap.comp_assoc, ← LinearMap.comp_add,
      h₂, LinearMap.comp_zero]
  rw [hcancel, zero_add] at h₃
  ext v
  apply hS
  simpa using congrArg (fun f : W →ₗ[𝕜] V => f v) h₃

/-- The norm argument for a factor of a product of contractions equal to the identity.
Here T is the product of the remaining factors; its contraction property is explicit.
@isnad1 id=eq.3h5v.s6.5adfb3249b12 from=translated src=- shape=4350c4a0 vocab=77d674a8
-/
theorem norm_eq_of_contraction_left_inverse
    {V W : Type*} [SeminormedAddCommGroup V] [SeminormedAddCommGroup W]
    (S : V → W) (T : W → V)
    (hS : ∀ v, ‖S v‖ ≤ ‖v‖) (hT : ∀ w, ‖T w‖ ≤ ‖w‖)
    (hTS : Function.LeftInverse T S) (v : V) : ‖S v‖ = ‖v‖ := by
  apply le_antisymm (hS v)
  simpa only [hTS v] using hT (S v)

/-- Invariance is the essential hypothesis when a compressed eigenvector is
promoted to an actual eigenvector of the ambient operator.
@isnad1 id=eq.4h7v.s9.33e5d0b96c49 from=translated src=- shape=80b7e9d8 vocab=f0fe7a70
-/
theorem ambient_eigenvector_of_invariant_compression
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (K : Submodule 𝕜 V) (R T : V →ₗ[𝕜] V)
    (hR : ∀ w ∈ K, R w = w)
    (hT : ∀ w ∈ K, T w ∈ K)
    {v : V} (hv : v ∈ K) {μ : 𝕜}
    (he : R (T v) = μ • v) : T v = μ • v := by
  rwa [hR (T v) (hT v hv)] at he

end FugledeAudit
