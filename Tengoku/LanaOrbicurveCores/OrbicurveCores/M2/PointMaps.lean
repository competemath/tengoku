/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Tengoku.LanaOrbicurveCores.OrbicurveCores.M2.ErgodicUse
import Tengoku.LanaOrbicurveCores.OrbicurveCores.M2.CrossRatio

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# M2: equivariant point maps to `ℙ¹(k)`

Setting: `Γ ≤ SL(2, ℝ)` acts on `Y = OnePoint k` through `a : SL(2, ℝ) → GL(2, k)`
(`ActsOn`: `a` is multiplicative on `Γ` as an action on `Y`). `NonElem Γ a`: no finite-index
subgroup of `Γ` has a common fixed point.

* `ae_ne_of_equivariant`: an equivariant measurable map `ψ : B → Y` is essentially
  non-constant: `ψ x₁ ≠ ψ x₂` for almost every pair.
-/

open MeasureTheory Filter Set
open scoped MatrixGroups

namespace OrbicurveCores.M2

variable {k : Type*} [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k]

/-- `ψ` is almost everywhere `Γ`-equivariant for the action `a`. -/
def Equivariant (Γ : Subgroup SL(2, ℝ)) (a : SL(2, ℝ) → GL (Fin 2) k)
    (ψ : OnePoint ℝ → OnePoint k) : Prop :=
  ∀ γ ∈ Γ, ∀ᵐ x ∂bdry, ψ (γ • x) = a γ • ψ x

/-- `a` is multiplicative on `Γ`, as an action on `ℙ¹(k)`. -/
def ActsOn (Γ : Subgroup SL(2, ℝ)) (a : SL(2, ℝ) → GL (Fin 2) k) : Prop :=
  ∀ g ∈ Γ, ∀ h ∈ Γ, ∀ y : OnePoint k, a (g * h) • y = a g • a h • y

/-- No finite-index subgroup of `Γ` fixes a point of `ℙ¹(k)`. -/
def NonElem (Γ : Subgroup SL(2, ℝ)) (a : SL(2, ℝ) → GL (Fin 2) k) : Prop :=
  ∀ Γ' : Subgroup SL(2, ℝ), Γ' ≤ Γ → Γ'.relIndex Γ ≠ 0 →
    ∀ y : OnePoint k, ∃ γ ∈ Γ', a γ • y ≠ y

omit [ProperSpace k] in
lemma ActsOn.one {Γ : Subgroup SL(2, ℝ)} {a : SL(2, ℝ) → GL (Fin 2) k} (h : ActsOn Γ a)
    (y : OnePoint k) : a 1 • y = y := by
  have := h 1 (one_mem _) 1 (one_mem _) y
  rw [mul_one] at this
  exact ((smul_left_cancel_iff (a 1)).1 this).symm

omit [ProperSpace k] in
lemma ActsOn.inv {Γ : Subgroup SL(2, ℝ)} {a : SL(2, ℝ) → GL (Fin 2) k} (h : ActsOn Γ a)
    {γ : SL(2, ℝ)} (hγ : γ ∈ Γ) (y : OnePoint k) : a γ⁻¹ • a γ • y = y := by
  rw [← h _ (inv_mem hγ) _ hγ, inv_mul_cancel, h.one]

lemma ae_fst {p : OnePoint ℝ → Prop} (h : ∀ᵐ x ∂bdry, p x) :
    ∀ᵐ q ∂(bdry.prod bdry), p q.1 :=
  Measure.quasiMeasurePreserving_fst.ae h

lemma ae_snd {p : OnePoint ℝ → Prop} (h : ∀ᵐ x ∂bdry, p x) :
    ∀ᵐ q ∂(bdry.prod bdry), p q.2 :=
  Measure.quasiMeasurePreserving_snd.ae h

lemma exists_of_ae {p : OnePoint ℝ → Prop} (h : ∀ᵐ x ∂bdry, p x) : ∃ x, p x := by
  by_contra hne
  push Not at hne
  have : bdry univ = 0 := by
    rw [← ae_iff.1 (h.mono fun x hx ↦ hx)]
    exact congrArg bdry (by ext x; simp [hne x])
  exact bdry_ne_zero (Measure.measure_univ_eq_zero.1 this)

end OrbicurveCores.M2
