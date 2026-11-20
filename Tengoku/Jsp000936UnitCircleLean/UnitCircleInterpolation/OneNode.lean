/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.Basic
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.RegularNodes

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The complete one-node case -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

/--
@isnad1 id=eq.0h3v.s5.4a6622d243d3 from=translated src=- shape=9becf5b7 vocab=d4bffe4b
-/
lemma cardinal_one (z : Fin 1 → ℂ) (j : Fin 1) (w : ℂ) : cardinal z j w = 1 := by
  have hj : j = 0 := Subsingleton.elim _ _
  simp [cardinal, hj]

/--
@isnad1 id=eq.0h2v.s4.d23c761c0cda from=translated src=- shape=dccbe108 vocab=c3516b0d
-/
lemma lebesgueFunction_one (z : Fin 1 → ℂ) (w : ℂ) : lebesgueFunction z w = 1 := by
  simp [lebesgueFunction, cardinal_one]

/--
@isnad1 id=eq.0h1v.s4.95f7b75c2995 from=translated src=- shape=1e0028ff vocab=a8996e94
-/
lemma amplification_one (nodes : NodeFamily 1) : amplification nodes = 1 := by
  obtain ⟨w, hw⟩ := amplification_attained nodes
  rw [hw, lebesgueFunction_one]

/--
@isnad1 id=isminimi.0h1v.s3.12e9d352e4dd from=translated src=- shape=9315f4f4 vocab=1688365a
-/
lemma isMinimizer_one (nodes : NodeFamily 1) : IsMinimizer nodes := by
  intro other
  simp [amplification_one]

/--
@isnad1 id=isregula.0h1v.s3.9b7fb248c47f from=translated src=- shape=9315f4f4 vocab=3a452625
-/
lemma isRegularRotation_one (nodes : NodeFamily 1) : IsRegularRotation nodes := by
  refine ⟨nodes.point 0, Equiv.refl _, ?_⟩
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  simp [hi, regularPoint]

/--
@isnad1 id=iff.0h1v.s4.3acaf74f8c55 from=translated src=- shape=c2a3ec81 vocab=f6d7bd49
-/
lemma minimizer_iff_regular_one (nodes : NodeFamily 1) :
    IsMinimizer nodes ↔ IsRegularRotation nodes :=
  ⟨fun _ => isRegularRotation_one nodes, fun _ => isMinimizer_one nodes⟩

/--
@isnad1 id=and.0h0v.s5.78df1949e626 from=translated src=- shape=b7305fab vocab=f6d7bd49
-/
lemma target_one :
    (∃ nodes : NodeFamily 1, IsMinimizer nodes) ∧
      ∀ nodes : NodeFamily 1, IsMinimizer nodes ↔ IsRegularRotation nodes :=
  ⟨⟨regularNodes 1 (by decide), isMinimizer_one _⟩, minimizer_iff_regular_one⟩

end

end UnitCircleInterpolation
