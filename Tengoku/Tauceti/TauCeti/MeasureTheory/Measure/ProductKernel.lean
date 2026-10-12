/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
-- Public: `Measure.infinitePi` appears in the infinite-product statement.
-- Non-public: `map_infinitePi_infinitePi_of_inj` is used inside the prefix-marginal and
-- block-selection proofs.
-- Non-public: `map_bind` is used only inside the mixture prefix-rectangle proof.
import Tengoku.Tauceti.TauCeti.MeasureTheory.Measure.GiryMonad

/-!
# Product probability-measure kernels

This file provides the basic theory of products of probability measures, phrased directly over
Mathlib's `ProbabilityMeasure.pi` and `Measure.infinitePi`: measurability of the product kernel —
finite and countable — and `Measure.bind`-evaluation of the mixture the finite product induces.

Measurability:
* `measurable_probabilityMeasure_pi` — the product combinator
  `ProbabilityMeasure.pi : (Π i, ProbabilityMeasure (α i)) → ProbabilityMeasure (Π i, α i)`
  is measurable.
* `measurable_probabilityMeasure_pi_toMeasure` — the measure-valued random product
  `ω ↦ (ProbabilityMeasure.pi fun i ↦ ν i ω).toMeasure` is measurable, for measurable coordinate
  kernels `ν i`.
* `aemeasurable_probabilityMeasure_pi_toMeasure` — the same map is `AEMeasurable` from
  a.e.-measurable coordinate kernels (`∀ i, AEMeasurable (ν i) μ`); the `_of_measurable` corollary
  is the measurable-input form.
* the constant-coordinate (`fun _ : Fin m ↦ ν ω`) specializations
  `measurable_probabilityMeasure_pi_const_toMeasure` and
  `aemeasurable_probabilityMeasure_pi_const_toMeasure`.
* `measurable_dirac_prod_probabilityMeasure_pi_const_toMeasure` — the **joint** kernel
  `ω ↦ δ_{ν ω} ⊗ (ν ω)^{⊗ Fin m}`, pairing the block kernel with a Dirac mass at the mixing
  measure. This is the joint-space input a conditional (joint-law) reading of the mixture
  identity needs, as opposed to the block kernel alone.
* `measurable_dirac_prod_infinitePi_const` — the parameter-tagged product kernel
  `t ↦ δ_t ⊗ (P t)^{⊗ι}` over an **arbitrary** index type, for a measurable family `P` of
  probability measures. Here the Dirac factor sits on the parameter rather than on the measure it
  selects, which is what a mixture retaining its parameter as a coordinate needs.
* `measurable_infinitePi` — the product `p ↦ ⊗ᵢ p i` over an **arbitrary** index type, of a
  dependent family of probability measures, is measurable in the measure argument;
  `measurable_infinitePi_const` is the `ℕ`-constant-power specialization `p ↦ p^{⊗ℕ}`. Mathlib
  supplies `Measure.infinitePi` and its projective-limit API but not this measurability, which is
  what a mixture of such products needs for `Measure.bind_apply` and the expected evaluation of
  the mixture as an integral.
* `map_prefixProj_infinitePi` — the finite-prefix marginal of a countable product, its first `n`
  coordinates being the corresponding finite product, with `map_prefixProj_infinitePi_const` the
  constant-family form. Mathlib's `Measure.infinitePi_map_restrict` gives the marginal indexed by a
  coerced `Finset`; this is the `Fin n`-prefix form that prefix-marginal arguments on `ℕ → α` use.
* `map_infinitePi_pair_block` — an **arbitrary injective block** of coordinates read off a constant
  countable power, and tagged with the law it came from: `Q^{⊗ℕ}` pushed along
  `x ↦ (Q, x ∘ k)` is `δ_Q ⊗ Q^{⊗ Fin m}`. This generalizes the prefix marginal above from `Fin.val`
  to any injective `k`, and pairs it with the Dirac factor, which is the form a disintegration
  against a directing measure consumes.

Bind-evaluation of the mixture `μ.bind fun ω ↦ (ProbabilityMeasure.pi fun i ↦ ν i ω).toMeasure`:
* `bind_probabilityMeasure_pi_apply` — evaluation on a measurable set as the integral of the product
  kernel, from a.e.-measurable coordinate kernels.
* `bind_probabilityMeasure_pi_pi` — evaluation on a measurable rectangle as the integral of the
  product of coordinate measures, with `Fin m` constant-coordinate forms
  `bind_probabilityMeasure_pi_const_apply` and `bind_probabilityMeasure_pi_const_pi`.
* `map_prefixProj_bind_infinitePi_pi` — the same evaluation for the *countable*-product mixture
  `π.bind (P ↦ P^{⊗ℕ})`: its finite-prefix rectangle probabilities are the mixed moments
  `∫⁻ P, ∏ i, P (B i) ∂π` of the evaluation maps. This pairs the prefix-marginal lemma above with
  bind-evaluation, and is what identifiability arguments for the mixing measure consume.

This file does not introduce a new product-kernel structure; the lemmas live directly over Mathlib's
`ProbabilityMeasure.pi`. It is motivated by the product-kernel layer of
`cameronfreer/exchangeability` (`MeasureKernels.lean` and the `bind_pi_apply` of
`DeFinetti/CommonEnding.lean`, pin `e0532e59ceff23edab44dda9ab0655debbc9cc22`), implemented using
Mathlib's `ProbabilityMeasure.pi`, `Measure.bind_apply`, and Giry measurability API; the combinator
generalizes Mathlib's binary `ProbabilityMeasure.measurable_fun_prod` to finite index types.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace MeasureTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)] {μ : Measure Ω}

/-- The finite product combinator `ProbabilityMeasure.pi` is a measurable map
`(Π i, ProbabilityMeasure (α i)) → ProbabilityMeasure (Π i, α i)`. -/
@[fun_prop]
theorem measurable_probabilityMeasure_pi :
    Measurable (ProbabilityMeasure.pi : (∀ i, ProbabilityMeasure (α i)) → ProbabilityMeasure
      (∀ i, α i)) := by
  have hcore : Measurable fun p : ∀ i, ProbabilityMeasure (α i) ↦
      (ProbabilityMeasure.pi p).toMeasure := by
    refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      (S := Set.pi univ '' Set.pi univ fun i ↦ {s : Set (α i) | MeasurableSet s})
      generateFrom_pi.symm isPiSystem_pi ?_
    rintro _ ⟨B, hB, rfl⟩
    have hBmeas : ∀ i, MeasurableSet (B i) := fun i ↦ hB i (mem_univ i)
    simp_rw [ProbabilityMeasure.toMeasure_pi, Measure.pi_pi]
    exact Finset.measurable_prod Finset.univ fun i _ ↦
      (Measure.measurable_coe (hBmeas i)).comp (measurable_subtype_coe.comp (measurable_pi_apply i))
  exact hcore.subtype_mk

/-- **Finite-prefix marginal of a countable product.** Restricting `⊗ⱼ p j` to its first `n`
coordinates gives the finite product `⊗_{i : Fin n} p i`.

Mathlib's `Measure.infinitePi_map_restrict` gives the marginal along a `Finset.restrict`, indexed by
the coerced finite set; this is the `Fin n`-prefix form, which is what prefix-marginal arguments on
`ℕ → α` use. Stated with the bare prefix map rather than any particular prefix abbreviation, so it
stays independent of downstream conventions. -/
theorem map_prefixProj_infinitePi {α : Type*} [MeasurableSpace α] (p : ℕ → ProbabilityMeasure α)
    (n : ℕ) :
    (Measure.infinitePi fun j : ℕ ↦ (p j : Measure α)).map (fun x : ℕ → α ↦ fun i : Fin n ↦ x i)
      = Measure.pi fun i : Fin n ↦ (p i : Measure α) := by
  rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]

/-- Constant-coordinate specialization of `map_prefixProj_infinitePi`: the first `n` coordinates of
`p^{⊗ℕ}` are distributed as `p^{⊗ Fin n}`. -/
theorem map_prefixProj_infinitePi_const {α : Type*} [MeasurableSpace α] (p : ProbabilityMeasure α)
    (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ ↦ (p : Measure α))).map (fun x : ℕ → α ↦ fun i : Fin n ↦ x i)
      = Measure.pi (fun _ : Fin n ↦ (p : Measure α)) :=
  map_prefixProj_infinitePi (fun _ ↦ p) n

end MeasureTheory

end TauCeti
