import Tengoku.PshdLean.PshLines.DeficitIntegrability
import Tengoku.Seed.MeasureTheory.Function.LocallyIntegrable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Compact localization of an extended-real deficit

The real deficit is nonnegative even at a negative-infinite pole, provided the
chosen upper bound is nonnegative. Its equality with the extended nonnegative
deficit is asserted only almost everywhere, after finiteness of the potential
has been established. Compact localization of a locally integrable real
representative gives a genuine globally integrable density.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal

namespace PshLines

variable {X : Type*} {u : X → EReal} {K : Set X} {C : ℝ}

/-- A nonnegative upper bound gives a nonnegative real deficit, including at
poles where the totalized real representative is zero. A separate exclusion
of positive infinity is unnecessary, since the finite upper bound excludes it.
@isnad1 id=le.2h5v.s6.606b9adc5b1e from=translated src=- shape=32997eca vocab=0d4e6f18
-/
theorem indicator_realDeficit_nonneg (hC : 0 ≤ C)
    (huC : ∀ x ∈ K, u x ≤ (C : EReal)) (x : X) :
    0 ≤ K.indicator (fun y => C - (u y).toReal) x := by
  classical
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx]
    by_cases hbot : u x = ⊥
    · simpa only [hbot, EReal.toReal_bot, sub_zero] using hC
    · exact sub_nonneg.mpr (by
        simpa only [EReal.toReal_coe] using
          EReal.toReal_le_toReal (huC x hx) hbot (EReal.coe_ne_top C))
  · simp only [Set.indicator_of_notMem hx, le_refl]

variable [MeasurableSpace X] {μ : Measure X}

/-- On a measurable set of finite measure, an integrable real representative
has a genuinely integrable zero-extended deficit.
@isnad1 id=integrab.3h5v.s6.41b41e045082 from=translated src=- shape=74aeeaf1 vocab=98fb777f
-/
theorem integrable_indicator_realDeficit (hK : MeasurableSet K) (hμK : μ K ≠ ⊤)
    (hu : IntegrableOn (fun x => (u x).toReal) K μ) (C : ℝ) :
    Integrable (K.indicator (fun x => C - (u x).toReal)) μ :=
  ((integrableOn_const (C := C) hμK).sub hu).integrable_indicator hK

/-- Almost-everywhere finiteness is retained explicitly when identifying the
extended deficit with the nonnegative real deficit. The statement remains
valid without an upper bound because `ofReal` truncates negative values.
@isnad1 id=eventual.2h5v.s6.fb2f2be12d37 from=translated src=- shape=44b5b041 vocab=24bf3c66
-/
theorem indicator_deficit_ae_eq_ofReal (hK : MeasurableSet K)
    (hfin : ∀ᵐ x ∂μ.restrict K, u x ≠ ⊤ ∧ u x ≠ ⊥) (C : ℝ) :
    K.indicator (fun x => ((C : EReal) - u x).toENNReal) =ᵐ[μ]
      fun x => ENNReal.ofReal (K.indicator (fun y => C - (u y).toReal) x) := by
  classical
  filter_upwards [(ae_restrict_iff' hK).mp hfin] with x hx
  by_cases hxK : x ∈ K
  · simp only [Set.indicator_of_mem hxK]
    rw [← EReal.coe_toReal (hx hxK).1 (hx hxK).2, ← EReal.coe_sub,
      EReal.real_coe_toENNReal, EReal.toReal_coe]
  · simp only [Set.indicator_of_notMem hxK, ENNReal.ofReal_zero]

section Compact

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
variable {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
variable {u : E → EReal} {K U : Set E}

/-- The compact-set specialization derives integrability from local
integrability on the ambient domain, rather than assuming it on the compact
set. The ambient domain need not be open.
@isnad1 id=integrab.3h6v.s7.ed91210fdb20 from=translated src=- shape=7bedb80a vocab=954ab710
-/
theorem integrable_indicator_realDeficit_of_isCompact (hK : IsCompact K) (hKU : K ⊆ U)
    (hu : LocallyIntegrableOn (fun x => (u x).toReal) U μ) (C : ℝ) :
    Integrable (K.indicator (fun x => C - (u x).toReal)) μ :=
  integrable_indicator_realDeficit hK.measurableSet hK.measure_ne_top
    ((hu.mono_set hKU).integrableOn_isCompact hK) C

/-- The compactly localized deficit is a valid locally integrable density
for scalar convolution pairings on the entire ambient space.
@isnad1 id=locallyi.3h6v.s7.7dc186b45fc1 from=translated src=- shape=dc99b42e vocab=7d331024
-/
theorem locallyIntegrable_indicator_realDeficit_of_isCompact
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hu : LocallyIntegrableOn (fun x => (u x).toReal) U μ) (C : ℝ) :
    LocallyIntegrable (K.indicator (fun x => C - (u x).toReal)) μ :=
  (integrable_indicator_realDeficit_of_isCompact hK hKU hu C).locallyIntegrable

omit [IsFiniteMeasureOnCompacts μ] in
/-- Almost-everywhere finiteness on the ambient domain suffices for equality
of the two localized deficits on the whole space.
@isnad1 id=eventual.3h6v.s7.5a67ed77900c from=translated src=- shape=d515d675 vocab=7adc8fd7
-/
theorem indicator_deficit_ae_eq_ofReal_of_isCompact
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hfin : ∀ᵐ x ∂μ.restrict U, u x ≠ ⊤ ∧ u x ≠ ⊥) (C : ℝ) :
    K.indicator (fun x => ((C : EReal) - u x).toENNReal) =ᵐ[μ]
      fun x => ENNReal.ofReal (K.indicator (fun y => C - (u y).toReal) x) :=
  indicator_deficit_ae_eq_ofReal hK.measurableSet
    (ae_restrict_of_ae_restrict_of_subset hKU hfin) C

end Compact

end PshLines
