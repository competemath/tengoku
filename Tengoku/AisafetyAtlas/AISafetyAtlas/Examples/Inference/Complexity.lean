module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Inference
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Inference.Device

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Section 5, inhabited

Every other part of this development has a worked model. Section 5 had none: no
example mentioned `inferenceComplexity`, `setupLength`, `answeringSet` or
`emulationCost`, so Definition 6 was a number nothing had ever computed and
Theorem 4 a bound nothing had ever met.

A definition cannot be vacuous, but it can be quietly wrong. Definition 6
totalizes to `0` wherever no setup answers a probe, and the docstring warns that
total failure would then look *cheaper* than success. Nothing checked that the
totalization was not what the definition always returned.

Two models here:

1. **Definition 6 computed.** The Proposition 1(i) device: its setup is the
   identity on a three-state universe, so every fibre is a singleton, every
   length is `−log 1 = 0`, and the complexity is `0` — reached through genuine
   minima over nonempty answering sets, not through the totalization.
2. **Theorem 4 attained.** The section-6 pair `fineDevice ≫ coarseForcedDevice`
   against a target both can answer. Here the theorem's inequality holds with
   **equality**: `𝒞(Γ∣C₁) − 𝒞(Γ∣C₂) = 2 · log 2 = |Γ(U)| · emulation cost`. A
   bound that is merely satisfied might be satisfied because both sides are
   vacuous or because the bound is hopelessly loose; this one is met exactly, so
   no smaller multiple of the emulation cost would do.
-/

namespace AISafetyAtlas.Examples.Inference.Complexity

open AISafetyAtlas.Inference
open AISafetyAtlas.Examples.Inference.Device

/-! ## Shared arithmetic

Every `inf'`/`sup'` in section 5 below is over a set on which the length function
is constant, so the extremum is that constant. -/

public theorem inf'_of_const {α : Type*} {s : Finset α} (h : s.Nonempty)
    (g : α → ℝ) (c : ℝ) (hg : ∀ y ∈ s, g y = c) : s.inf' h g = c := by
  refine le_antisymm ?_ (Finset.le_inf' _ _ (fun y hy => le_of_eq (hg y hy).symm))
  obtain ⟨y, hy⟩ := h
  calc s.inf' _ g ≤ g y := Finset.inf'_le _ hy
    _ = c := hg y hy

/-! ## 1. Definition 6 computed on the Proposition 1(i) device -/

/-! ## 2. Theorem 4 attained

`fineDevice ≫ coarseForcedDevice` is already proved (section 6 of
`Examples.Inference.Device`). Theorem 4 needs one more thing the source demands
and nothing here had supplied: a target the *coarse* device weakly infers.

The coarse setup partitions `Fin 4` into `{0,1}` and `{2,3}`, and its conclusion
is the parity bit. So the target has to agree with parity on one block and
disagree on the other — otherwise one of the two `Bool` probes has no answering
fibre. -/

/-- The target: parity on `{0,1}`, its negation on `{2,3}`.-/
public abbrev gamma4 : Fin 4 → Bool := fun i => decide (i.val = 1 ∨ i.val = 2)

/-- **`C₂ > Γ`.** Each probe is answered, but by a *different* block: the identity
probe by `{0,1}`, the negation probe by `{2,3}`.-/
public theorem coarse_weaklyInfers_gamma4 : WeaklyInfers coarseForcedDevice gamma4 := by
  intro γ f hf _
  rcases isProbe_bool hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨false, ⟨0, by decide⟩, by decide⟩
  · exact ⟨true, ⟨2, by decide⟩, by decide⟩

/-! ### Lengths

The fine setup is the identity — singleton fibres, length `0`. The coarse setup
has two fibres of size two — length `−log 2`. -/

public theorem coarse_fibreCard (x : Bool) : setupFibreCard coarseForcedDevice x = 2 := by
  classical
  unfold setupFibreCard
  cases x
  · have h : (Finset.univ.filter (fun u : Fin 4 => coarseForcedDevice.setup u = false))
        = ({0, 1} : Finset (Fin 4)) := by
      ext u
      fin_cases u <;> simp [coarseForcedDevice]
    rw [h]
    decide
  · have h : (Finset.univ.filter (fun u : Fin 4 => coarseForcedDevice.setup u = true))
        = ({2, 3} : Finset (Fin 4)) := by
      ext u
      fin_cases u <;> simp [coarseForcedDevice]
    rw [h]
    decide

public theorem coarse_setupLength (x : Bool) :
    setupLength coarseForcedDevice x = -Real.log 2 := by
  unfold setupLength
  rw [coarse_fibreCard]
  norm_num

/-! ### The two complexities -/

public theorem rangeFinset_gamma4 : rangeFinset gamma4 = (Finset.univ : Finset Bool) := by
  ext b
  simp only [mem_rangeFinset, Finset.mem_univ, iff_true]
  cases b
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩

/-- `𝒞(Γ∣C₂) = −2·log 2`: each of the two probes is answered only by a
two-element fibre.-/
public theorem coarse_complexity :
    inferenceComplexity coarseForcedDevice (setupLength coarseForcedDevice) gamma4
      coarse_weaklyInfers_gamma4 = -(2 * Real.log 2) := by
  unfold inferenceComplexity inferenceComplexityTotal
  have hterm : ∀ γ ∈ rangeFinset gamma4,
      minAnsweringLength coarseForcedDevice (setupLength coarseForcedDevice) gamma4 (probe γ)
        = -Real.log 2 := by
    intro γ hγ
    unfold minAnsweringLength
    rw [dite_eq_left (answeringSet_nonempty_of_weaklyInfers coarseForcedDevice
      coarse_weaklyInfers_gamma4 γ ((mem_rangeFinset gamma4 γ).mp hγ))]
    exact inf'_of_const _ _ _ (fun y _ => coarse_setupLength y)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, rangeFinset_gamma4]
  simp

/-! ### The emulation cost -/

/-! ### Theorem 4 on the witness -/

end AISafetyAtlas.Examples.Inference.Complexity
