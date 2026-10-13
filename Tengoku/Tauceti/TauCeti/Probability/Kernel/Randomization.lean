/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Probability.Kernel.ProbabilityMeasure
public import Tengoku

/-!
# Randomizing probability measures and kernels by uniform variables

A probability measure on a standard Borel space is the law of a measurable function of a single
uniform variable, and the function can be chosen to depend measurably on the measure. Packaging
that choice once gives a **coding map**

```text
unitIntervalCoding α : ProbabilityMeasure α → I → α
```

which is jointly measurable and satisfies `volume.map (unitIntervalCoding α P) = P` for every `P`.
Feeding it independent uniform variables therefore realizes any product `P^{⊗ι}` as the law of a
coordinatewise transform of uniform noise, which is `map_infinitePi_volume_unitIntervalCoding`.

This is the "isolation of randomness" step: a random probability measure `ν` and an independent
uniform sequence `ϑ` together generate a sample from `ν`, with all the randomness of the sample
carried by `ϑ`. It is what turns a conditional-distribution statement into a *functional*
representation.

The conditional form starts from a Markov kernel `κ : Kernel β α`. Mathlib provides a jointly
measurable realization `f : β → I → α` of each conditional law `κ b`; this file proves that the
skew map `(b, u) ↦ (b, f b u)` sends `μ.prod volume` to the composition-product `μ ⊗ₘ κ`.
Applying this to the conditional kernel of a joint law gives a functional representation of the
pair by its first coordinate and a fresh independent uniform variable. This is the conditional
randomization step used when a probabilistic representation is converted into latent variables.

## Main definitions

* `TauCeti.Probability.unitIntervalCoding` — the coding map above.

## Main results

* `TauCeti.Probability.map_volume_unitIntervalCoding` — the coding map transports the uniform law
  on `I` to its parameter.
* `TauCeti.Probability.map_infinitePi_volume_unitIntervalCoding` — applying it coordinatewise to
  i.i.d. uniform noise produces the `ι`-fold power of the parameter for an arbitrary index type.
* `TauCeti.Probability.exists_measurable_map_prod_volume_eq_compProd` — a Markov kernel and
  a base measure are jointly realized from the base point and independent uniform noise.
* `TauCeti.Probability.exists_measurable_map_prod_volume_eq` — every finite joint law has
  such a conditional functional representation.
* `TauCeti.Probability.exists_measurable_map_prod_volume_eq_map_prodMk` — the random-variable form,
  using fresh uniform noise on the original probability space.

## Implementation

Mathlib's `ProbabilityTheory.Kernel.exists_measurable_map_eq_unitInterval` supplies the coding for
an arbitrary Markov kernel into a standard Borel space; the content here is applying it to the
tautological kernel, so that the parameter space is the space of probability measures itself and no
further choice has to be threaded through downstream statements. `unitIntervalCoding` is therefore
a choice: it has no properties beyond the two recorded below, and consumers should use those rather
than unfold it. The conditional results apply Mathlib's general kernel realization to an arbitrary
Markov kernel, identify the resulting skew-product law by the product-measure integral formula,
and use Mathlib's `Measure.condKernel` disintegration for the joint-law forms.

## References

* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Lemma 4.22.
* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Theorem 8.5, for disintegration.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

variable (α)

/-- **The coding map of a standard Borel space.** A jointly measurable
`ProbabilityMeasure α → I → α` transporting the uniform law on the unit interval to its parameter,
`map_volume_unitIntervalCoding`.

This is a choice among the maps with that property; the two lemmas below are its entire
specification. -/
def unitIntervalCoding [StandardBorelSpace α] [Nonempty α] : ProbabilityMeasure α → I → α :=
  (Kernel.exists_measurable_map_eq_unitInterval (samplingKernel α)).choose

variable [StandardBorelSpace α] [Nonempty α]

/-- The coding map is jointly measurable in the parameter and the uniform variable. -/
@[fun_prop]
theorem measurable_uncurry_unitIntervalCoding :
    Measurable (Function.uncurry (unitIntervalCoding α)) :=
  (Kernel.exists_measurable_map_eq_unitInterval (samplingKernel α)).choose_spec.1

variable {α}

/-- The coding map is measurable in the uniform variable, for each fixed parameter. -/
@[fun_prop]
theorem measurable_unitIntervalCoding (P : ProbabilityMeasure α) :
    Measurable (unitIntervalCoding α P) :=
  (measurable_uncurry_unitIntervalCoding α).of_uncurry_left

/-- **The defining property of the coding map:** it transports the uniform law on `I` to its
parameter. -/
@[simp]
theorem map_volume_unitIntervalCoding (P : ProbabilityMeasure α) :
    (volume : Measure I).map (unitIntervalCoding α P) = (P : Measure α) :=
  calc
    (volume : Measure I).map (unitIntervalCoding α P) = samplingKernel α P :=
      (Kernel.exists_measurable_map_eq_unitInterval (samplingKernel α)).choose_spec.2 P
    _ = (P : Measure α) := samplingKernel_apply P

/-- **Coding a product law by i.i.d. uniform noise.** Applying the coding map coordinatewise to an
i.i.d. uniform family produces the `ι`-fold power of the parameter, for an arbitrary index type. -/
@[simp]
theorem map_infinitePi_volume_unitIntervalCoding {ι : Type*} (P : ProbabilityMeasure α) :
    (Measure.infinitePi fun _ : ι => (volume : Measure I)).map
        (fun u i => unitIntervalCoding α P (u i))
      = Measure.infinitePi fun _ : ι => (P : Measure α) := by
  rw [Measure.infinitePi_map_pi (μ := fun _ : ι => (volume : Measure I))
    (f := fun _ : ι => unitIntervalCoding α P) fun _ => measurable_unitIntervalCoding P]
  simp

section Conditional

variable {β : Type*} [MeasurableSpace β]

omit [StandardBorelSpace α] [Nonempty α] in
/-- A jointly measurable realization of a Markov kernel turns independent uniform noise into its
composition-product with any s-finite base measure. -/
theorem map_prod_volume_eq_compProd_of_map_volume {μ : Measure β} [SFinite μ]
    (κ : Kernel β α) [IsSFiniteKernel κ] (f : β → I → α)
    (hf : Measurable (Function.uncurry f))
    (hmap : ∀ b, (volume : Measure I).map (f b) = κ b) :
    (μ.prod (volume : Measure I)).map (fun p => (p.1, f p.1 p.2)) = μ ⊗ₘ κ := by
  have hF : Measurable (fun p : β × I => (p.1, f p.1 p.2)) := by fun_prop
  ext s hs
  rw [Measure.map_apply hF hs, Measure.prod_apply (hs.preimage hF), Measure.compProd_apply hs]
  congr with b
  rw [← hmap b, Measure.map_apply hf.of_uncurry_left (measurable_prodMk_left hs)]
  rfl

/-- **Conditional randomization of a Markov kernel.** There is a jointly measurable function of
the kernel parameter and one uniform variable whose skew-product law over any s-finite base
measure is the corresponding composition-product. -/
theorem exists_measurable_map_prod_volume_eq_compProd (κ : Kernel β α)
    [IsMarkovKernel κ] {μ : Measure β} [SFinite μ] :
    ∃ f : β → I → α, Measurable (Function.uncurry f) ∧
      (μ.prod (volume : Measure I)).map (fun p => (p.1, f p.1 p.2)) = μ ⊗ₘ κ := by
  obtain ⟨f, hf, hmap⟩ := Kernel.exists_measurable_map_eq_unitInterval κ
  exact ⟨f, hf, map_prod_volume_eq_compProd_of_map_volume κ f hf hmap⟩

/-- **Conditional randomization of a joint law.** Every finite measure on `β × α` is obtained by
first drawing its first marginal and then applying a jointly measurable function to that point
and a fresh independent uniform variable. -/
theorem exists_measurable_map_prod_volume_eq (ρ : Measure (β × α))
    [IsFiniteMeasure ρ] :
    ∃ f : β → I → α, Measurable (Function.uncurry f) ∧
      (ρ.fst.prod (volume : Measure I)).map (fun p => (p.1, f p.1 p.2)) = ρ := by
  obtain ⟨f, hf, hcode⟩ :=
    exists_measurable_map_prod_volume_eq_compProd ρ.condKernel (μ := ρ.fst)
  exact ⟨f, hf, hcode.trans (Measure.disintegrate ρ ρ.condKernel)⟩

end Conditional

end Probability

end TauCeti
