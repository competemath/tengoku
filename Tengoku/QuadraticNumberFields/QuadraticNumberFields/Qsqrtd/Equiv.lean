/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Tengoku.QuadraticNumberFields.QuadraticNumberFields.QuadraticField.Parameters

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Equivalences Between `Qsqrtd` Models

This file proves the rational-parameter equivalence criterion for the standard
models `Qsqrtd d`.

The squarefree integer parameter uniqueness theorem lives in
`QuadraticNumberFields.QuadraticField.Parameters`. Here the parameter may change
by a rational square: two standard models are `ℚ`-algebra equivalent exactly
when their parameters differ by a rational square factor.

## Main definitions

* `Qsqrtd.IsSquareRatio`: `d' = a² d` for some `a : ℚˣ`.
* `Qsqrtd.IsSquareRatioByDivision`: `d' / d = a²` for some `a : ℚˣ`.
* `Qsqrtd.algEquiv_iff_isSquareRatio`: classification of equivalences between
  non-square standard models by rational square ratios.
-/

local notation "ℚ√" d => Qsqrtd d

namespace Qsqrtd

-- Resolve the diamond between `DivisionRing.toRatAlgebra` and `QuadraticAlgebra.instAlgebra`.
-- NOTE: This is a file-local workaround for standard model algebra equivalences.
attribute [-instance] DivisionRing.toRatAlgebra

/-- The parameters `d` and `d'` differ by a rational square factor.-/
def IsSquareRatio (d d' : ℚ) : Prop :=
  ∃ a : ℚˣ, d' = (a : ℚ) ^ 2 * d

/-- Division-form version of `Qsqrtd.IsSquareRatio`: `d' / d` is a rational
unit square. This is the shape usually used in informal statements.-/
def IsSquareRatioByDivision (d d' : ℚ) : Prop :=
  ∃ a : ℚˣ, d' / d = (a : ℚ) ^ 2

/-- Rescaling gives an algebra equivalence whenever the parameters differ by a
rational square factor.
@isnad1 id=nonempty.1h2v.s6.7f8352700726 from=translated src=- shape=4271f56a vocab=d763ddd7
-/
theorem nonempty_algEquiv_of_isSquareRatio {d d' : ℚ} :
    IsSquareRatio d d' → Nonempty (Qsqrtd d ≃ₐ[ℚ] Qsqrtd d') := by
  rintro ⟨a, rfl⟩
  exact ⟨Qsqrtd.rescale d a⟩

/-- Multiplicative and division forms of square-ratio equivalence agree away
from `d = 0`.
@isnad1 id=iff.1h2v.s4.4ef4b7b496c3 from=translated src=- shape=f0484c38 vocab=6df50310
-/
theorem isSquareRatio_iff_isSquareRatioByDivision {d d' : ℚ} (hd : d ≠ 0) :
    IsSquareRatio d d' ↔ IsSquareRatioByDivision d d' := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    field_simp [hd]
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    calc
      d' = d' / d * d := by field_simp [hd]
      _ = (a : ℚ) ^ 2 * d := by rw [ha]

/-- Non-square standard models are equivalent exactly when their parameters
differ by a rational square factor.
@isnad1 id=iff.0h2v.s6.0295a268e5ad from=translated src=- shape=ebc6b386 vocab=a039bfb3
-/
theorem algEquiv_iff_isSquareRatio
    (d d' : ℚ) [Fact (¬ IsSquare d)] [Fact (¬ IsSquare d')] :
    Nonempty (Qsqrtd d ≃ₐ[ℚ] Qsqrtd d') ↔ IsSquareRatio d d' := by
  constructor
  · rintro ⟨φ⟩
    obtain ⟨-, hb, hr⟩ := algEquiv_param_rel (Fact.out : ¬ IsSquare d) φ
    set b := (φ ⟨0, 1⟩).im
    -- `hr : d = d' * b²` with `b ≠ 0`, so `d' = (b⁻¹)² * d`.
    refine ⟨Units.mk0 b⁻¹ (inv_ne_zero hb), ?_⟩
    change d' = (b⁻¹) ^ 2 * d
    rw [hr]
    field_simp [hb]
  · exact nonempty_algEquiv_of_isSquareRatio

/-- Division form of the classification, matching the usual informal statement
`d' / d ∈ ℚ×²`.
@isnad1 id=iff.0h2v.s6.6dc923cd2b64 from=translated src=- shape=ebc6b386 vocab=94a5d7c8
-/
theorem algEquiv_iff_isSquareRatioByDivision
    (d d' : ℚ) [Fact (¬ IsSquare d)] [Fact (¬ IsSquare d')] :
    Nonempty (Qsqrtd d ≃ₐ[ℚ] Qsqrtd d') ↔ IsSquareRatioByDivision d d' := by
  have hd : d ≠ 0 := by
    intro hd
    exact (Fact.out : ¬ IsSquare d) (by rw [hd]; exact ⟨0, by ring⟩)
  exact (algEquiv_iff_isSquareRatio d d').trans (isSquareRatio_iff_isSquareRatioByDivision hd)

end Qsqrtd
