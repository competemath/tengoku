import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.FrameGaugeNormalization
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.AmbientLocalizedRotation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Relative product control for normalization cobordisms

Componentwise normalization is useful only if every later move leaves the
components already put in standard position literally unchanged.  This file
records that invariant at the level of the actual space-time defining map and
sign label, proves that it survives cobordism gluing, and carries it through the
three stages of `signedNormalizationCobordism`.

In particular, a localized ambient rotation supported in the ball of squared
radius two can be used in a normalization step while the final glued signed
cobordism remains a product over every component outside that ball.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Topology ContDiff RealInnerProductSpace

namespace Submission

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))
local notation "F" => EuclideanSpace ℝ (Fin n)

/-! ## Product regions survive gluing -/

namespace FramedLevelCobordism

/-- The space-time defining map is literally the product of `g` over `K`.-/
def ProductOn (C : FramedLevelCobordism n) (K : Set E) (g : E → F) : Prop :=
  ∀ x ∈ K, ∀ t : ℝ, C.G (spaceTime x t) = g x

/-- Gluing two product cobordisms over the same set produces another literal
product there.-/
theorem ProductOn.trans {C₁ C₂ : FramedLevelCobordism n} {K : Set E}
    {g : E → F} (h₁ : C₁.ProductOn K g) (h₂ : C₂.ProductOn K g)
    (hmid : C₁.X₁ = C₂.X₀) : (C₁.trans C₂ hmid).ProductOn K g := by
  intro x hx t
  change transFun C₁ C₂ (spaceTime x t) = g x
  rw [transFun, vertC_spaceTime]
  by_cases ht : t < 1 / 2
  · rw [ite_eq_left ht, reparamMap, initCLM_spaceTime, vertC_spaceTime]
    exact h₁ x hx (3 * t + -(1 / 2))
  · rw [ite_eq_right ht, reparamMap, initCLM_spaceTime, vertC_spaceTime]
    exact h₂ x hx (3 * t + -(3 / 2))

end FramedLevelCobordism

namespace SignedFramedLevelCobordism

/-- Both the defining map and sign extension are literal products over `K`.-/
def ProductOn {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀}
    {S₁ : FiberSign X₁} (C : SignedFramedLevelCobordism S₀ S₁)
    (K : Set E) (g : E → F) (σ : E → ℝ) : Prop :=
  C.cobordism.ProductOn K g ∧
    ∀ x ∈ K, ∀ t : ℝ, C (spaceTime x t) = σ x

/-- Signed gluing preserves a common literal product region.-/
theorem ProductOn.trans {X₀ X₁ X₂ : FramedLevelSet n}
    {S₀ : FiberSign X₀} {S₁ : FiberSign X₁} {S₂ : FiberSign X₂}
    {C₁ : SignedFramedLevelCobordism S₀ S₁}
    {C₂ : SignedFramedLevelCobordism S₁ S₂}
    {K : Set E} {g : E → F} {σ : E → ℝ}
    (h₁ : C₁.ProductOn K g σ) (h₂ : C₂.ProductOn K g σ) :
    (SignedFramedLevelCobordism.trans C₁ C₂).ProductOn K g σ := by
  constructor
  · exact h₁.1.trans h₂.1 (C₁.target_eq.trans C₂.source_eq.symm)
  · intro x hx t
    change SignedFramedLevelCobordism.transFun C₁ C₂ (spaceTime x t) = σ x
    rw [SignedFramedLevelCobordism.transFun, vertC_spaceTime]
    by_cases ht : t < 1 / 2
    · rw [ite_eq_left ht, reparamMap, initCLM_spaceTime, vertC_spaceTime]
      exact h₁.2 x hx (3 * t + -(1 / 2))
    · rw [ite_eq_right ht, reparamMap, initCLM_spaceTime, vertC_spaceTime]
      exact h₂.2 x hx (3 * t + -(3 / 2))

end SignedFramedLevelCobordism

/-! ## Relative ambient and defining-map stages -/

namespace SmoothAmbientIsotopy

/-- A relative ambient sweep is a literal signed product on its fixed set.-/
theorem FixedOn.signedCobordism_productOn {A : SmoothAmbientIsotopy n}
    {K : Set E} (hA : A.FixedOn K) {X : FramedLevelSet n}
    (S : FiberSign X) :
    (A.signedCobordism S).ProductOn K X.g S := by
  constructor
  · intro x hx t
    exact hA.cobordism_product X hx t
  · intro x hx t
    exact hA.signedCobordism_product S hx t

end SmoothAmbientIsotopy

namespace DefiningMapHomotopy

/-- A defining-map homotopy is stationary over `K` when all its maps agree
there with one fixed defining map.-/
def FixedOn {X₀ X₁ : FramedLevelSet n} (D : DefiningMapHomotopy X₀ X₁)
    (K : Set E) (g : E → F) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, D.H s x = g x

/-- The signed cobordism of a stationary defining-map homotopy is a literal
product over its stationary set.-/
theorem FixedOn.signedCobordism_productOn {X₀ X₁ : FramedLevelSet n}
    {D : DefiningMapHomotopy X₀ X₁} {K : Set E} {g : E → F}
    (hD : D.FixedOn K g) (S : FiberSign X₀) :
    (D.signedCobordism S).ProductOn K g S := by
  constructor
  · intro x hx t
    change D.cobMap (spaceTime x t) = g x
    rw [D.cobMap_spaceTime]
    exact hD (normRamp t) ⟨normRamp_nonneg t, normRamp_le_one t⟩ x hx
  · intro x hx t
    change S (initCLM (n + 1) (spaceTime x t)) = S x
    rw [initCLM_spaceTime]

end DefiningMapHomotopy

/-! ## The full three-stage normalization -/

namespace SmoothAmbientIsotopy

/-- If the ambient move and the frame homotopy preserve `K`, and the target
label agrees there, then the complete ambient/frame/sign normalization
cobordism is a literal product over `K`, even after both gluings.-/
theorem signedNormalizationCobordism_productOn
    (A : SmoothAmbientIsotopy n) {X Y : FramedLevelSet n}
    (D : DefiningMapHomotopy (A.pullback X) Y)
    (S : FiberSign X) (T : FiberSign Y)
    (hpos : ∀ x ∈ Y.fiber,
      (0 < (A.pullbackSign S).restrict D.fiber_subset x ↔ 0 < T x))
    {K : Set E} (hA : A.FixedOn K)
    (hD : D.FixedOn K X.g) (hT : ∀ x ∈ K, T x = S x) :
    (signedNormalizationCobordism A D S T hpos).ProductOn K X.g S := by
  let C₁ := A.signedCobordism S
  let C₂ := D.signedCobordism (A.pullbackSign S)
  let C₃ := signInterpolationCobordism
    ((A.pullbackSign S).restrict D.fiber_subset) T hpos
  have hC₁ : C₁.ProductOn K X.g S :=
    hA.signedCobordism_productOn S
  have hC₂ : C₂.ProductOn K X.g S := by
    constructor
    · intro x hx t
      change D.cobMap (spaceTime x t) = X.g x
      rw [D.cobMap_spaceTime]
      exact hD (normRamp t) ⟨normRamp_nonneg t, normRamp_le_one t⟩ x hx
    · intro x hx t
      change A.pullbackSign S (initCLM (n + 1) (spaceTime x t)) = S x
      rw [initCLM_spaceTime]
      exact hA.pullbackSign_eq S hx
  have hYg : ∀ x ∈ K, Y.g x = X.g x := by
    intro x hx
    rw [← congrFun D.H_one x]
    exact hD 1 ⟨zero_le_one, le_rfl⟩ x hx
  have hC₃ : C₃.ProductOn K X.g S := by
    constructor
    · intro x hx t
      change Y.g (initCLM (n + 1) (spaceTime x t)) = X.g x
      rw [initCLM_spaceTime, hYg x hx]
    · intro x hx t
      change
        (1 - normRamp (vertC (spaceTime x t))) *
              A.pullbackSign S (initCLM (n + 1) (spaceTime x t)) +
            normRamp (vertC (spaceTime x t)) *
              T (initCLM (n + 1) (spaceTime x t)) = S x
      rw [vertC_spaceTime, initCLM_spaceTime,
        hA.pullbackSign_eq S hx, hT x hx]
      ring
  exact hC₁.trans (hC₂.trans hC₃)

end SmoothAmbientIsotopy

/-! ## Localized rotation specialization -/

namespace SmoothAmbientIsotopy

variable {m : ℕ}

end SmoothAmbientIsotopy

end Submission
