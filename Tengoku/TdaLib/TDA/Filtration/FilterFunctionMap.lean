import Tengoku.TdaLib.TDA.Filtration.OrderingEquivalent
import Tengoku.Seed.Algebra.Order.GroupWithZero.OrderIso
import Tengoku.Seed.Data.Real.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Reparametrizing face-value filters along order embeddings

A filter function with values in `α` is reparametrized along an order embedding
`φ : α ↪o β` by composing its values with `φ`. Monotonicity is preserved, sublevels
correspond at every source threshold, and at every target threshold when `φ` is an order
isomorphism, and the original and reparametrized filters are ordering-equivalent. Positive
scaling of real filters is the special case `φ = OrderIso.mulLeft₀ c hc`.

These are library extensions proved from the merged definitions; no external theorem is
translated. Monotone non-injective and order-reversing maps are outside this API.
-/

universe u v w z

namespace TDA.Filtration.FilterFunction

open TDA.Simplicial

variable {V : Type u} {K : PreAbstractSimplicialComplex V}
variable {α : Type v} {β : Type w} {γ : Type z}
variable [LinearOrder α] [LinearOrder β] [LinearOrder γ]

/-- Two filters with the same value on every face are equal.
@isnad1 id=eq.1h5v.s5.ba660b029714 from=translated src=- shape=a6e53691 vocab=527508ab
-/
@[ext] theorem ext {f g : FilterFunction K α} (h : ∀ s, f.value s = g.value s) : f = g := by
  cases f
  cases g
  congr
  funext s
  exact h s

/-- Reparametrize the values of a filter along an order embedding.-/
def map (f : FilterFunction K α) (φ : α ↪o β) : FilterFunction K β where
  value s := φ (f.value s)
  mono h := φ.monotone (f.mono h)

/--
@isnad1 id=eq.0h7v.s7.244c51dd161f from=translated src=- shape=29f6d44f vocab=8c0eb2b4
-/
@[simp] theorem map_value (f : FilterFunction K α) (φ : α ↪o β) (s : TotalFace K) :
    (f.map φ).value s = φ (f.value s) := rfl

/-- The reparametrized sublevel at the image of a source threshold is the source sublevel.
@isnad1 id=eq.0h7v.s7.3f32a46463d8 from=translated src=- shape=0ee2cee6 vocab=a7c9eabf
-/
theorem map_sublevel_apply (f : FilterFunction K α) (φ : α ↪o β) (r : α) :
    (f.map φ).sublevel (φ r) = f.sublevel r := by
  apply le_antisymm
  · rintro s ⟨hs, h⟩
    exact ⟨hs, φ.le_iff_le.1 h⟩
  · rintro s ⟨hs, h⟩
    exact ⟨hs, φ.le_iff_le.2 h⟩

/-- Along an order isomorphism every target threshold is the image of a source threshold.
@isnad1 id=eq.0h7v.s7.d2f8c835bd00 from=translated src=- shape=2ad15496 vocab=bb71857f
-/
theorem map_sublevel_orderIso (f : FilterFunction K α) (e : α ≃o β) (q : β) :
    (f.map e.toOrderEmbedding).sublevel q = f.sublevel (e.symm q) := by
  have h := map_sublevel_apply f e.toOrderEmbedding (e.symm q)
  simpa only [OrderIso.coe_toOrderEmbedding, OrderIso.apply_symm_apply] using h

/-- A filter and its reparametrization make exactly the same weak comparisons.
@isnad1 id=ordering.0h6v.s6.b671794e8198 from=translated src=- shape=b1715c91 vocab=0b5f6ce5
-/
theorem orderingEquivalent_map (f : FilterFunction K α) (φ : α ↪o β) :
    OrderingEquivalent f (f.map φ) :=
  fun _ _ => φ.le_iff_le.symm

/-- Reparametrizing along the identity embedding does nothing.
@isnad1 id=eq.0h4v.s5.65e96d171c45 from=translated src=- shape=4cc11fdd vocab=25165581
-/
theorem map_refl (f : FilterFunction K α) : f.map (RelEmbedding.refl (· ≤ ·)) = f := by
  ext s
  rfl

/-- Successive reparametrizations compose.
@isnad1 id=eq.0h8v.s7.6715173b021f from=translated src=- shape=b33b04ac vocab=ba598d87
-/
theorem map_map (f : FilterFunction K α) (φ : α ↪o β) (ψ : β ↪o γ) :
    (f.map φ).map ψ = f.map (φ.trans ψ) := by
  ext s
  rfl

/-- Multiply every face value of a real filter by a positive constant.-/
noncomputable def scale (f : FilterFunction K ℝ) (c : ℝ) (hc : 0 < c) : FilterFunction K ℝ :=
  f.map (OrderIso.mulLeft₀ c hc).toOrderEmbedding

/--
@isnad1 id=eq.1h5v.s5.6448f1efdcfa from=translated src=- shape=17d7d5c4 vocab=be62d836
-/
@[simp] theorem scale_value (f : FilterFunction K ℝ) (c : ℝ) (hc : 0 < c)
    (s : TotalFace K) : (f.scale c hc).value s = c * f.value s := rfl

/-- The scaled sublevel at `r` is the original sublevel at `c⁻¹ * r`.
@isnad1 id=eq.1h5v.s5.d4c39e72aab8 from=translated src=- shape=63b0a50a vocab=4d64b168
-/
theorem scale_sublevel (f : FilterFunction K ℝ) (c : ℝ) (hc : 0 < c) (r : ℝ) :
    (f.scale c hc).sublevel r = f.sublevel (c⁻¹ * r) := by
  rw [scale, map_sublevel_orderIso, OrderIso.mulLeft₀_symm, OrderIso.mulLeft₀_apply]

/--
@isnad1 id=eq.0h3v.s4.f85837caece9 from=translated src=- shape=a267ce03 vocab=4ed5c0b7
-/
theorem scale_one (f : FilterFunction K ℝ) : f.scale 1 one_pos = f := by
  ext s
  simp

/--
@isnad1 id=eq.2h5v.s6.52c9d9a80c1c from=translated src=- shape=77463276 vocab=4215e945
-/
theorem scale_scale (f : FilterFunction K ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (f.scale a ha).scale b hb = f.scale (b * a) (mul_pos hb ha) := by
  ext s
  simp [mul_assoc]

end TDA.Filtration.FilterFunction
