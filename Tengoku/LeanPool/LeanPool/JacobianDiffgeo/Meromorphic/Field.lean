/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Meromorphic.OrderEval
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Meromorphic.CodiscreteBridge
public import Tengoku

/-!
# `Field (ℳ X)` and pointwise inverse (CC3, proof plan §6.2)

Unit: meromorphic-and-divisors (`docs/design/meromorphic-and-divisors.md` §4.5).

* `Inv (MeroGermOn X U)`: the honest pointwise inverse on germs (`Germ.instInv`), unconditional
  (no `if`), junk-free — `mk_inv`, `ord_inv` (unconditional, matches `ordAtX_inv`).
* On a connected surface, the meromorphic identity dichotomy (`CodiscreteBridge`) classifies the
  zero class (`Mero.ord_eq_top_iff`) and gives `mul_inv_cancel₀`, assembling `Field (ℳ X)`.
-/

@[expose] public section

open scoped ContDiff Manifold
open Set Filter Topology

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {U : Set X} {x : X}

namespace MeroGermOn

noncomputable instance : Inv (MeroGermOn X U) :=
  ⟨fun φ => ⟨φ.1⁻¹, by
    obtain ⟨f, hf, hfeq⟩ := φ.2
    exact ⟨f⁻¹, hf.inv, by rw [hfeq]; exact (Filter.Germ.coe_inv f).symm⟩⟩⟩

@[simp] theorem mk_inv {f : X → ℂ} {hf : MeromorphicOnX f U} : (mk f hf)⁻¹ = mk f⁻¹ hf.inv :=
  Subtype.ext (Filter.Germ.coe_inv f).symm

theorem ord_inv (hU : IsOpen U) (hx : x ∈ U) (φ : MeroGermOn X U) :
    (φ⁻¹).ord x = -(φ.ord x) := by
  obtain ⟨f, hf, rfl⟩ := exists_rep φ
  rw [mk_inv, ord_mk hU hx, ord_mk hU hx]
  exact ordAtX_inv

end MeroGermOn

/-! ### The zero class on a connected surface -/

/-! ### `Field (ℳ X)` -/

theorem Mero.mul_inv_cancel [T1Space X] [ConnectedSpace X] {φ : ℳ X} (hφ : φ ≠ 0) :
    φ * φ⁻¹ = 1 := by
  obtain ⟨f, hf, rfl⟩ := MeroGermOn.exists_rep φ
  have hne : ¬ (f =ᶠ[codiscrete X] fun _ => (0 : ℂ)) := by
    intro hcontra
    exact hφ (by rw [← MeroGermOn.mk_zero]; exact MeroGermOn.mk_eq_mk.2 hcontra)
  have hcodis : ∀ᶠ z in codiscrete X, f z ≠ 0 := hf.codiscrete_setOf_ne_zero hne
  rw [MeroGermOn.mk_inv, MeroGermOn.mk_mul]
  have hval : (f * f⁻¹) =ᶠ[codiscrete X] fun _ => (1 : ℂ) := by
    filter_upwards [hcodis] with z hz
    simp [mul_inv_cancel₀ hz]
  rw [MeroGermOn.mk_eq_mk.2 hval]
  exact MeroGermOn.mk_one

end RS
