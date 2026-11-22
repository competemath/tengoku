/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku

/-! # Graph -/

@[expose] public section
namespace Tengoku.LeanPool end Tengoku.LeanPool open Tengoku.LeanPool 
namespace Function

variable {σ α β : Sort*}

/-- Imported declaration from the Incompleteness formalization. -/
def Graphᵥ (f : (Fin k → α) → α) : (Fin (k + 1) → α) → Prop := fun v ↦ v 0 = f (v ·.succ)

/-- Imported declaration from the Incompleteness formalization. -/
def Graph (f : α → σ) : σ → α → Prop := fun y x ↦ y = f x

/-- Imported declaration from the Incompleteness formalization. -/
def Graph₂ (f : α → β → σ) : σ → α → β → Prop := fun y x₁ x₂ ↦ y = f x₁ x₂

/-- Imported declaration from the Incompleteness formalization. -/
def Graph₃ (f : α → β → γ → σ) : σ → α → β → γ → Prop := fun y x₁ x₂ x₃ ↦ y = f x₁ x₂ x₃

/-- Imported declaration from the Incompleteness formalization. -/
def Graph₄ (f : α → β → γ → δ → σ) :
    σ → α → β → γ → δ → Prop :=
  fun y x₁ x₂ x₃ x₄ ↦ y = f x₁ x₂ x₃ x₄

/-- Imported declaration from the Incompleteness formalization. -/
def Graph₅ (f : α → β → γ → δ → ε → σ) :
    σ → α → β → γ → δ → ε → Prop :=
  fun y x₁ x₂ x₃ x₄ x₅ ↦ y = f x₁ x₂ x₃ x₄ x₅

/--
@isnad1 id=eq.1h5v.s4.f44fa0f098bc from=translated src=- shape=f5949549 vocab=40d4e13d
-/
lemma _root_.Function.Graph.eq {f : α → σ} {y x} (h : Graph f y x) : f x = y := h.symm

/--
@isnad1 id=iff.0h5v.s4.3eada1e98c9d from=translated src=- shape=96b60d79 vocab=40d4e13d
-/
lemma _root_.Function.Graph.iff_left (f : α → σ) {y x} :
    f x = y ↔ Graph f y x := by simp [Graph, eq_comm]

/--
@isnad1 id=iff.0h5v.s4.dbecbb76635e from=translated src=- shape=9c7cce4b vocab=40d4e13d
-/
lemma _root_.Function.Graph.iff_right (f : α → σ) {y x} : y = f x ↔ Graph f y x := by simp [Graph]

/--
@isnad1 id=eq.1h7v.s5.7be727c854ce from=translated src=- shape=a73ec93b vocab=4838b4ca
-/
lemma _root_.Function.Graph₂.eq {f : α → β → σ} {y x₁ x₂} (h : Graph₂ f y x₁ x₂) :
    f x₁ x₂ = y :=
  h.symm

/--
@isnad1 id=iff.0h7v.s5.0e234272ba68 from=translated src=- shape=7b646f67 vocab=4838b4ca
-/
lemma _root_.Function.Graph₂.iff_left (f : α → β → σ) {y x₁ x₂} :
    f x₁ x₂ = y ↔ Graph₂ f y x₁ x₂ := by simp [Graph₂, eq_comm]

/--
@isnad1 id=iff.0h7v.s5.b558b1cc6c5c from=translated src=- shape=e462a590 vocab=4838b4ca
-/
lemma _root_.Function.Graph₂.iff_right (f : α → β → σ) {y x₁ x₂} :
    y = f x₁ x₂ ↔ Graph₂ f y x₁ x₂ := by simp [Graph₂]

/--
@isnad1 id=eq.1h9v.s5.9b18e0e44335 from=translated src=- shape=830ef725 vocab=82f2e254
-/
lemma _root_.Function.Graph₃.eq {f : α → β → γ → σ} {y x₁ x₂ x₃} (h : Graph₃ f y x₁ x₂ x₃) :
    f x₁ x₂ x₃ = y :=
  h.symm

/--
@isnad1 id=iff.0h9v.s5.76aec05e70e9 from=translated src=- shape=9dbf0e1a vocab=82f2e254
-/
lemma _root_.Function.Graph₃.iff_left (f : α → β → γ → σ) {y x₁ x₂ x₃} :
    f x₁ x₂ x₃ = y ↔ Graph₃ f y x₁ x₂ x₃ := by simp [Graph₃, eq_comm]

/--
@isnad1 id=iff.0h9v.s5.02c8e796965e from=translated src=- shape=3bd950f5 vocab=82f2e254
-/
lemma _root_.Function.Graph₃.iff_right (f : α → β → γ → σ) {y x₁ x₂ x₃} :
    y = f x₁ x₂ x₃ ↔ Graph₃ f y x₁ x₂ x₃ := by simp [Graph₃]

end Function
-- Tengoku: root names of this library moved to Tengoku.LeanPool so they do not collide with other libraries (generated)
