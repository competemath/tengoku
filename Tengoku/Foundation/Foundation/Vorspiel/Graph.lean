module

public import Tengoku.Seed.Logic.Function.Defs

namespace Function
end Function

namespace FoundationFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose]
public section

namespace Function
open _root_.Function

variable {k} {σ α β γ δ ε : Sort*}

def Graphᵥ (f : (Fin k → α) → α) : (Fin (k + 1) → α) → Prop := fun v ↦ v 0 = f (v ·.succ)

def Graph (f : α → σ) : σ → α → Prop := fun y x ↦ y = f x

def Graph₂ (f : α → β → σ) : σ → α → β → Prop := fun y x₁ x₂ ↦ y = f x₁ x₂

def Graph₃ (f : α → β → γ → σ) : σ → α → β → γ → Prop := fun y x₁ x₂ x₃ ↦ y = f x₁ x₂ x₃

def Graph₄ (f : α → β → γ → δ → σ) : σ → α → β → γ → δ → Prop := fun y x₁ x₂ x₃ x₄ ↦ y = f x₁ x₂ x₃ x₄

def Graph₅ (f : α → β → γ → δ → ε → σ) : σ → α → β → γ → δ → ε → Prop := fun y x₁ x₂ x₃ x₄ x₅ ↦ y = f x₁ x₂ x₃ x₄ x₅

lemma Graph.eq {f : α → σ} {y x} (h : Graph f y x) : f x = y := h.symm

lemma Graph.iff_left (f : α → σ) {y x} : f x = y ↔ Graph f y x := by simp [Graph, eq_comm]

lemma Graph.iff_right (f : α → σ) {y x} : y = f x ↔ Graph f y x := by simp [Graph]

end Function

end
