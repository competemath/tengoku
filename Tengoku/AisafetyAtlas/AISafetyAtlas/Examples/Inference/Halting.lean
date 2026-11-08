module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Inference

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Worked models: halting, recursive devices, and the two readings of Definition 9

Definition 8's identification is exercised on a device that halts everywhere and
one that does not, so `recursive_iff_refines` is shown separating real cases
rather than holding vacuously.

The Definition 9 material is a source finding rather than a theorem to
instantiate, and it lives with the definition: `two_rpow_neg_measureLength` says
what the printed formula computes, `two_rpow_neg_measureLengthBase2` says what the
base-consistent reading computes, and `sum_pushOnImage_le_one` shows the second
reading restricts nothing.
-/

namespace AISafetyAtlas.Examples.Inference.Halting

open AISafetyAtlas.Inference

/-- A device whose setup determines its conclusion: it halts at every setup.-/
public abbrev haltingDevice : InferenceDevice.{0, 0} Bool :=
  { Setup := Bool, setup := id, concl := id, concl_surjective := fun b => ⟨b, rfl⟩ }

/-- A device whose single setup value leaves both conclusions open: it halts
nowhere it is realized.-/
public abbrev stuckDevice : InferenceDevice.{0, 0} Bool :=
  { Setup := Unit, setup := fun _ => (), concl := id, concl_surjective := fun b => ⟨b, rfl⟩ }

theorem haltingDevice_recursive : Recursive haltingDevice := by
  rw [recursive_iff_refines]
  intro u u' h
  exact h

theorem stuckDevice_not_recursive : ¬ Recursive stuckDevice := by
  rw [recursive_iff_refines]
  intro h
  exact Bool.noConfusion (h true false rfl)

/-- The setup value of the stuck device is realized, so Definition 8's second
half is not satisfied vacuously.-/
theorem stuckDevice_realized : stuckDevice.Realized () := ⟨true, rfl⟩

/-- Halting is not an empty condition on the stuck device's own setup type: the
one realized value fails it.-/
theorem stuckDevice_not_haltsAt : ¬ HaltsAt stuckDevice () := by
  rintro ⟨y, hy⟩
  have h1 : (true : Bool) = y := hy true rfl
  have h2 : (false : Bool) = y := hy false rfl
  exact Bool.noConfusion (h1.trans h2.symm)

/-! ## The two readings of Definition 9, separated by a model

`sum_pushOnImage_le_one` proves the base-consistent reading is **automatic**:
it holds for every device, every halting set, and every measure of total mass at
most one. Clash 21 argues that the printed reading — `ℳ` in natural logarithm,
the exponent in base 2 — is a different condition. Until now nothing exhibited
the difference: no device in the tree was shown to satisfy `PrefixFree`, and
none was shown to fail it, so clash 21 rested entirely on the algebra of
`μ^{ln 2}` against `μ`.

`haltingDevice` under the uniform measure on `Bool` separates them. Each fibre
carries mass `1/2` and both setups halt, so:

* base-consistent: `1/2 + 1/2 = 1 ≤ 1`, satisfied;
* **as printed**: each summand is `(1/2)^{ln 2} > 1/2`, since `ln 2 < 1` and
  `(1/2)^·` is decreasing, so the sum exceeds `1` and the condition **fails**.

One device, one measure, opposite verdicts. Clash 21 is now a demonstration.
-/

/-- The uniform probability measure on `Bool`: each point carries mass `1/2`.-/
noncomputable def uniformBool : MeasureTheory.Measure Bool :=
  (2 : ENNReal)⁻¹ • MeasureTheory.Measure.count

noncomputable instance : DecidablePred (HaltsAt haltingDevice) := fun _ => Classical.dec _

/-- The identity setup pins the conclusion, so every setup value halts.-/
theorem haltingDevice_haltsAt (b : Bool) : HaltsAt haltingDevice b :=
  ⟨b, fun _ hu => hu⟩

/-- Both setup values are realized and both halt, so the index of Definition 9's
sum is all of `Bool`.-/
theorem haltingSetups_haltingDevice : haltingSetups haltingDevice = Finset.univ := by
  ext b
  simp only [Finset.mem_univ, iff_true]
  exact (mem_haltingSetups_iff haltingDevice b).mpr ⟨⟨b, rfl⟩, haltingDevice_haltsAt b⟩

end AISafetyAtlas.Examples.Inference.Halting
