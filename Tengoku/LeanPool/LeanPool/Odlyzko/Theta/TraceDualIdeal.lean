/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

/-- A trace dual ideal unit used in the Odlyzko-bound argument. -/
noncomputable def traceDualIdealUnit
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0
    (FractionalIdeal.dual ℤ ℚ
      (I : FractionalIdeal (𝓞 K)⁰ K))
    (FractionalIdeal.dual_ne_zero ℤ ℚ (Units.ne_zero I))

/--
@isnad1 id=eq.0h2v.s9.97893e5e8fbf from=translated src=- shape=870786bd vocab=42b99353
-/
@[simp]
theorem coe_traceDualIdealUnit
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (traceDualIdealUnit K I : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ
        (I : FractionalIdeal (𝓞 K)⁰ K) :=
  rfl

/--
@isnad1 id=eq.0h2v.s8.be58fbf34c8b from=translated src=- shape=af19e80a vocab=f3a86524
-/
@[simp]
theorem traceDualIdealUnit_traceDualIdealUnit
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    traceDualIdealUnit K (traceDualIdealUnit K I) = I := by
  ext
  simp

/--
@isnad1 id=eq.0h2v.s9.49817cb1ba5e from=translated src=- shape=8c2f997a vocab=8d980ddf
-/
theorem coe_traceDualIdealUnit_eq_dual_one_mul_inv
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (traceDualIdealUnit K I : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ
          (1 : FractionalIdeal (𝓞 K)⁰ K) *
        (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [coe_traceDualIdealUnit,
    FractionalIdeal.dual_eq_mul_inv]

/--
@isnad1 id=eq.0h2v.s10.44febcb0dfcb from=translated src=- shape=fdffdec4 vocab=32d37879
-/
theorem absNorm_traceDualIdealUnit
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    FractionalIdeal.absNorm
        (traceDualIdealUnit K I :
          FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.absNorm
          (FractionalIdeal.dual ℤ ℚ
            (1 : FractionalIdeal (𝓞 K)⁰ K)) *
        (FractionalIdeal.absNorm
          (I : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
  rw [coe_traceDualIdealUnit_eq_dual_one_mul_inv,
    map_mul, map_inv₀]

/--
@isnad1 id=eq.0h1v.s9.2add5da7ddfd from=translated src=- shape=1fddd5ae vocab=029c752c
-/
theorem absNorm_traceDual_one :
    FractionalIdeal.absNorm
        (FractionalIdeal.dual ℤ ℚ
          (1 : FractionalIdeal (𝓞 K)⁰ K)) =
      ((|(discr K : ℤ)| : ℚ))⁻¹ := by
  have hdifferent :=
    congrArg FractionalIdeal.absNorm
      (coeIdeal_differentIdeal ℤ ℚ K (𝓞 K))
  rw [map_inv₀, FractionalIdeal.coeIdeal_absNorm,
    NumberField.absNorm_differentIdeal K] at hdifferent
  simp_all

end NumberField.Odlyzko
