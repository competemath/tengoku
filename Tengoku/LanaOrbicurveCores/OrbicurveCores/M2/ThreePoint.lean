/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Tengoku.LanaOrbicurveCores.OrbicurveCores.ForMathlib.ProjectiveLine

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# M2: triples and relative positions

`G s t = h(s) h(t)⁻¹ (0, 1, ∞)` for distinct triples `s`, `t`. Then:

* `G t' (rel t t') = t`;
* `G (g t) t = g (0, 1, ∞)`;
* `G` is continuous on pairs of distinct triples and takes distinct values.
-/

open Topology Set Filter OnePoint OnePoint.Proj

namespace OrbicurveCores.M2

variable {k : Type*} [Field k] [DecidableEq k]

/-- The standard triple `(0, 1, ∞)`. -/
def e₃ : Triple k := (((0 : k) : OnePoint k), ((1 : k) : OnePoint k), ∞)

omit [DecidableEq k] in
lemma distinct3_e₃ : Distinct3 (e₃ (k := k)) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [e₃]

/-- Apply a Möbius matrix to a triple. -/
def mob3 (M : Matrix (Fin 2) (Fin 2) k) (t : Triple k) : Triple k :=
  (mob M t.1, mob M t.2.1, mob M t.2.2)

/-- `G s t = h(s) h(t)⁻¹ (0, 1, ∞)`. -/
def G3 (s t : Triple k) : Triple k := mob3 (tri s) (mob3 (tri t).adjugate e₃)

lemma mob3_tri {t : Triple k} (ht : Distinct3 t) : mob3 (tri t) e₃ = t := by
  simp only [mob3, e₃, mob_tri_zero ht, mob_tri_one ht, mob_tri_infty ht]

section topology

variable {k : Type*} [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k]

omit [DecidableEq k] in
lemma isOpen_distinct3 : IsOpen {t : Triple k | Distinct3 t} := by
  have e : {t : Triple k | Distinct3 t} =
      {y | y.1 ≠ y.2.1} ∩ {y | y.1 ≠ y.2.2} ∩ {y | y.2.1 ≠ y.2.2} := by
    ext; simp [Distinct3, and_assoc]
  rw [e]
  refine ((isOpen_ne_fun (f := fun t : Triple k ↦ t.1) (g := fun t ↦ t.2.1) (by fun_prop)
    (by fun_prop)).inter (isOpen_ne_fun (f := fun t : Triple k ↦ t.1) (g := fun t ↦ t.2.2)
    (by fun_prop) (by fun_prop))).inter (isOpen_ne_fun (f := fun t : Triple k ↦ t.2.1)
    (g := fun t ↦ t.2.2) (by fun_prop) (by fun_prop))

end topology

end OrbicurveCores.M2
