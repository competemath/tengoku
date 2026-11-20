import Tengoku.Hellingerrepolean4.Hellinger.BooleanNoise
import Tengoku.Hellingerrepolean4.Hellinger.BentEstimates
import Tengoku.Seed.Logic.Equiv.Fin.Basic
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms canonical_posterior_root_mean` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms canonical_hellinger` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms canonical_hellinger_strict` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms eightPhase_hellinger` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms eightPhase_hellinger_strict` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms classify_bent2` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms bent2_hellinger` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms bent2_hellinger_strict` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# A concrete two-bit Hellinger theorem

This module connects the actual finite product BSC to the posterior formula
proved analytically in `BentEstimates`. No moment or posterior-formula
hypothesis is imposed on the final canonical theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.TwoBitCase

open Hellinger.BentEstimates

/-- The phase `(-1)^(x₀x₁)` with additive bits represented by `Bool`.-/
def canonical (x : Fin 2 → Bool) : ℝ := boolSign (x 0 && x 1)

/-- Exact expansion of a sum over the four points of the two-bit cube.
@isnad1 id=eq.0h1v.s7.1ade5ac3af0a from=translated src=- shape=e907ed4e vocab=398fde8f
-/
theorem sum_two_bits (f : (Fin 2 → Bool) → ℝ) :
    (∑ x, f x) = f ![false, false] + f ![false, true] +
      f ![true, false] + f ![true, true] := by
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp f]
  simp [Fintype.sum_prod_type, finTwoArrowEquiv]
  ring

/--
@isnad1 id=eq.0h0v.s6.bfe2cef9f48e from=translated src=- shape=ae0ac5f3 vocab=a86b8fe1
-/
theorem canonical_mean : mean canonical = (1 : ℝ) / 2 := by
  norm_num [mean, sum_two_bits, canonical, boolSign]

/--
@isnad1 id=eq.1h1v.s7.fafb5a9d1256 from=translated src=- shape=1dcb3314 vocab=182ca463
-/
theorem canonical_posterior_ff (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    (cubeBSC 2 ρ hρ).apply canonical ![false, false] = (1 + 2 * ρ - ρ ^ 2) / 2 := by
  simp [UniformChannel.apply, sum_two_bits, cubeBSC, UniformChannel.product,
    Fin.prod_univ_two, bsc, canonical, boolSign]
  ring

/--
@isnad1 id=eq.1h1v.s7.7d5b914ff819 from=translated src=- shape=3042a4f9 vocab=e2a791f5
-/
theorem canonical_posterior_ft (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    (cubeBSC 2 ρ hρ).apply canonical ![false, true] = (1 + ρ ^ 2) / 2 := by
  simp [UniformChannel.apply, sum_two_bits, cubeBSC, UniformChannel.product,
    Fin.prod_univ_two, bsc, canonical, boolSign]
  ring

/--
@isnad1 id=eq.1h1v.s7.d0bf17a75034 from=translated src=- shape=3042a4f9 vocab=e2a791f5
-/
theorem canonical_posterior_tf (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    (cubeBSC 2 ρ hρ).apply canonical ![true, false] = (1 + ρ ^ 2) / 2 := by
  simp [UniformChannel.apply, sum_two_bits, cubeBSC, UniformChannel.product,
    Fin.prod_univ_two, bsc, canonical, boolSign]
  ring

/--
@isnad1 id=eq.1h1v.s7.f74006f49bc0 from=translated src=- shape=64baa813 vocab=bab72419
-/
theorem canonical_posterior_tt (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    (cubeBSC 2 ρ hρ).apply canonical ![true, true] = (1 - 2 * ρ - ρ ^ 2) / 2 := by
  simp [UniformChannel.apply, sum_two_bits, cubeBSC, UniformChannel.product,
    Fin.prod_univ_two, bsc, canonical, boolSign]
  ring

/-- The true BSC posterior average is exactly the four-value analytic expression.
@isnad1 id=eq.1h1v.s7.7373ee6d7198 from=translated src=- shape=5c691e96 vocab=df518d6d
-/
theorem canonical_posterior_root_mean (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    mean (fun y => root ((cubeBSC 2 ρ hρ).apply canonical y)) = twoNoiseR ρ := by
  simp only [mean, sum_two_bits, canonical_posterior_ff, canonical_posterior_ft,
    canonical_posterior_tf, canonical_posterior_tt]
  norm_num [root, twoNoiseR]
  ring

/-- The bias term for the canonical function.
@isnad1 id=eq.0h0v.s6.1c90a9dd38fe from=translated src=- shape=425ab682 vocab=c5288047
-/
theorem canonical_root_mean : root (mean canonical) = Real.sqrt 3 / 2 := by
  rw [canonical_mean]
  unfold root
  have harg : (1 : ℝ) - (1 / 2) ^ 2 = 3 / 4 := by norm_num
  rw [harg, Real.sqrt_div' _ (show 0 ≤ (4 : ℝ) by norm_num)]
  have hs4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hs4]

/-- The true biased Hellinger objective under the two-fold BSC.
@isnad1 id=eq.1h1v.s7.63742c2c4c1f from=translated src=- shape=91a71f08 vocab=ee6e4a30
-/
theorem canonical_objective (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    objective ((cubeBSC 2 ρ hρ).apply canonical) = Real.sqrt 3 / 2 - twoNoiseR ρ := by
  unfold objective
  rw [UniformChannel.mean_apply, canonical_root_mean, canonical_posterior_root_mean]

/-- A full-noise Hellinger theorem for an actual nonlinear Boolean function,
with no moment estimates or posterior formula assumed.
@isnad1 id=le.1h1v.s7.4eabd834e37f from=translated src=- shape=9402f90f vocab=959d5f0c
-/
theorem canonical_hellinger (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    objective ((cubeBSC 2 ρ hρ).apply canonical) ≤ 1 - root ρ := by
  rw [canonical_objective]
  have hgap := twoNoiseR_gap_bound ρ hρ.1 hρ.2
  have hpos : 0 ≤ (4 + Real.sqrt (2 : ℝ) - 3 * Real.sqrt 3) / 4 * ρ ^ 2 :=
    mul_nonneg (le_of_lt two_gap_coefficient_pos) (sq_nonneg _)
  unfold root
  linarith

/-- Strictness for the canonical nonlinear Boolean function at every `ρ > 0`.
@isnad1 id=lt.2h1v.s7.f5ff25e55b85 from=translated src=- shape=1b68f4aa vocab=3129d81b
-/
theorem canonical_hellinger_strict (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (hρpos : 0 < ρ) :
    objective ((cubeBSC 2 ρ hρ).apply canonical) < 1 - root ρ := by
  rw [canonical_objective]
  exact twoNoiseR_hellinger_strict ρ hρpos hρ.2

/-- The Boolean function negative at one specified vertex and positive elsewhere.-/
def pointPhase (p : Bool × Bool) (x : Fin 2 → Bool) : ℝ :=
  if x 0 = p.1 ∧ x 1 = p.2 then -1 else 1

/--
@isnad1 id=eq.0h1v.s6.ed4403317061 from=translated src=- shape=2e3049b6 vocab=a650c678
-/
theorem pointPhase_mean (p : Bool × Bool) : mean (pointPhase p) = (1 : ℝ) / 2 := by
  rcases p with ⟨p₀, p₁⟩
  cases p₀ <;> cases p₁ <;> norm_num [mean, sum_two_bits, pointPhase]

/-- All four posterior values, simultaneously for each of the four negative-vertex choices.
@isnad1 id=eq.1h4v.s8.87b4d62f4209 from=translated src=- shape=0324d8ff vocab=8f09a17e
-/
theorem pointPhase_posterior (p : Bool × Bool) (y₀ y₁ : Bool)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    (cubeBSC 2 ρ hρ).apply (pointPhase p) ![y₀, y₁] =
      if y₀ = p.1 then
        (if y₁ = p.2 then (1 - 2 * ρ - ρ ^ 2) / 2 else (1 + ρ ^ 2) / 2)
      else
        (if y₁ = p.2 then (1 + ρ ^ 2) / 2 else (1 + 2 * ρ - ρ ^ 2) / 2) := by
  rcases p with ⟨p₀, p₁⟩
  cases p₀ <;> cases p₁ <;> cases y₀ <;> cases y₁ <;>
    simp [UniformChannel.apply, sum_two_bits, cubeBSC, UniformChannel.product,
      Fin.prod_univ_two, bsc, pointPhase] <;> ring

/--
@isnad1 id=eq.1h2v.s7.3d7ad2595e1b from=translated src=- shape=49632944 vocab=de204440
-/
theorem pointPhase_posterior_root_mean (p : Bool × Bool)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    mean (fun y => root ((cubeBSC 2 ρ hρ).apply (pointPhase p) y)) = twoNoiseR ρ := by
  simp only [mean, sum_two_bits, pointPhase_posterior]
  rcases p with ⟨p₀, p₁⟩
  cases p₀ <;> cases p₁ <;> norm_num [root, twoNoiseR] <;> ring

/--
@isnad1 id=eq.1h2v.s7.392a978af107 from=translated src=- shape=847391d5 vocab=909aa046
-/
theorem pointPhase_objective (p : Bool × Bool)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    objective ((cubeBSC 2 ρ hρ).apply (pointPhase p)) = Real.sqrt 3 / 2 - twoNoiseR ρ := by
  unfold objective
  rw [UniformChannel.mean_apply, pointPhase_mean, pointPhase_posterior_root_mean]
  have hr : root ((1 : ℝ) / 2) = Real.sqrt 3 / 2 := by
    simpa only [canonical_mean] using canonical_root_mean
  rw [hr]

/-- Output complementation leaves the biased Hellinger objective unchanged.
@isnad1 id=eq.0h3v.s5.b93af0d8bf2f from=translated src=- shape=140b6734 vocab=ba1b3d90
-/
theorem objective_apply_neg {Ω : Type*} [Fintype Ω]
    (K : UniformChannel Ω) (f : Ω → ℝ) :
    objective (K.apply (fun x => -f x)) = objective (K.apply f) := by
  have hk : K.apply (fun x => -f x) = fun x => -K.apply f x := by
    funext x
    simp [UniformChannel.apply, Finset.sum_neg_distrib]
  rw [hk]
  have hm : mean (fun x => -K.apply f x) = -mean (K.apply f) := by
    simp [mean, Finset.sum_neg_distrib]
  unfold objective
  rw [hm, root_neg]
  congr 1
  apply congrArg mean
  funext x
  exact root_neg _

/-- The eight truth tables obtained from four single-minus functions and their complements.-/
def eightPhase (p : Bool × Bool) (complement : Bool) (x : Fin 2 → Bool) : ℝ :=
  boolSign complement * pointPhase p x

/--
@isnad1 id=or.0h3v.s5.a8e5a2b41aed from=translated src=- shape=0de85bb9 vocab=82e8e49f
-/
theorem eightPhase_boolean (p : Bool × Bool) (complement : Bool) (x : Fin 2 → Bool) :
    eightPhase p complement x = -1 ∨ eightPhase p complement x = 1 := by
  cases complement <;> by_cases h : x 0 = p.1 ∧ x 1 = p.2 <;>
    simp [eightPhase, boolSign, pointPhase, h]

/-- Exact objective for every function in the eight-truth-table family.
@isnad1 id=eq.1h3v.s7.82a63fff6bae from=translated src=- shape=9f215231 vocab=ae1c8bdf
-/
theorem eightPhase_objective (p : Bool × Bool) (complement : Bool)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    objective ((cubeBSC 2 ρ hρ).apply (eightPhase p complement)) =
      Real.sqrt 3 / 2 - twoNoiseR ρ := by
  cases complement
  · have hf : eightPhase p false = pointPhase p := by funext x; simp [eightPhase, boolSign]
    rw [hf]
    exact pointPhase_objective p ρ hρ
  · have hf : eightPhase p true = fun x => -pointPhase p x := by
      funext x; simp [eightPhase, boolSign]
    rw [hf]
    exact (objective_apply_neg (cubeBSC 2 ρ hρ) (pointPhase p)).trans (pointPhase_objective p ρ hρ)

/-- Full-noise Hellinger inequality for all eight explicit two-bit truth tables.
@isnad1 id=le.1h3v.s7.9e5c758ef14a from=translated src=- shape=b146c5a4 vocab=5dc44010
-/
theorem eightPhase_hellinger (p : Bool × Bool) (complement : Bool)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    objective ((cubeBSC 2 ρ hρ).apply (eightPhase p complement)) ≤ 1 - root ρ := by
  rw [eightPhase_objective, ← canonical_objective ρ hρ]
  exact canonical_hellinger ρ hρ

/-- Strictness for all eight truth tables at every positive correlation.
@isnad1 id=lt.2h3v.s7.c20d83ebc24c from=translated src=- shape=46e0ad2e vocab=de27c04b
-/
theorem eightPhase_hellinger_strict (p : Bool × Bool) (complement : Bool)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρpos : 0 < ρ) :
    objective ((cubeBSC 2 ρ hρ).apply (eightPhase p complement)) < 1 - root ρ := by
  rw [eightPhase_objective, ← canonical_objective ρ hρ]
  exact canonical_hellinger_strict ρ hρ hρpos

/-- Normalized Walsh transform on the two-bit cube; the four frequencies are
indexed by `Bool × Bool`, and the dot product uses Boolean XOR.-/
def normalizedWalsh (f : (Fin 2 → Bool) → ℝ) (s : Bool × Bool) : ℝ :=
  mean (fun x => f x * boolSign (Bool.xor (s.1 && x 0) (s.2 && x 1)))

/-- The standard flat-Walsh definition of a two-bit bent real-valued phase.
Boolean-valuedness is a separate hypothesis in the final classification theorem.-/
def IsBent2 (f : (Fin 2 → Bool) → ℝ) : Prop :=
  ∀ s : Bool × Bool, normalizedWalsh f s ^ 2 = 1 / 4

/--
@isnad1 id=eq.0h1v.s6.cf16e5ed7e9b from=translated src=- shape=6dc68bfa vocab=8ae42209
-/
theorem normalizedWalsh_zero (f : (Fin 2 → Bool) → ℝ) :
    normalizedWalsh f (false, false) = mean f := by
  simp [normalizedWalsh, boolSign, mean]

/-- Every member of the eight-table family is indeed bent by the flat-Walsh definition.
@isnad1 id=isbent2.0h2v.s3.281e0dc064c6 from=translated src=- shape=d338bd8a vocab=da90417d
-/
theorem eightPhase_isBent2 (p : Bool × Bool) (complement : Bool) : IsBent2 (eightPhase p complement) := by
  intro s
  rcases p with ⟨p₀, p₁⟩
  rcases s with ⟨s₀, s₁⟩
  cases p₀ <;> cases p₁ <;> cases complement <;> cases s₀ <;> cases s₁ <;>
    norm_num [normalizedWalsh, mean, sum_two_bits, eightPhase, pointPhase, boolSign]

/--
@isnad1 id=eq.4h2v.s7.50fee3322be8 from=translated src=- shape=c00e661b vocab=ae2e42f5
-/
theorem two_bits_ext {f g : (Fin 2 → Bool) → ℝ}
    (hff : f ![false, false] = g ![false, false])
    (hft : f ![false, true] = g ![false, true])
    (htf : f ![true, false] = g ![true, false])
    (htt : f ![true, true] = g ![true, true]) : f = g := by
  funext x
  have hx : x = ![x 0, x 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  cases h₀ : x 0 <;> cases h₁ : x 1
  · simpa only [h₀, h₁] using hff
  · simpa only [h₀, h₁] using hft
  · simpa only [h₀, h₁] using htf
  · simpa only [h₀, h₁] using htt

/-- Boolean-valuedness and squared mean `1/4` already force one of the eight tables.
The proof is a kernel-checked exhaustion of the sixteen Boolean truth tables.
@isnad1 id=ex.2h1v.s7.e7dc3ffddd8e from=translated src=- shape=b3037ced vocab=f5beaf7c
-/
theorem classify_of_mean_sq (f : (Fin 2 → Bool) → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hm : mean f ^ 2 = 1 / 4) :
    ∃ p : Bool × Bool, ∃ complement : Bool, f = eightPhase p complement := by
  rcases hf ![false, false] with hff | hff <;>
    rcases hf ![false, true] with hft | hft <;>
    rcases hf ![true, false] with htf | htf <;>
    rcases hf ![true, true] with htt | htt
  all_goals norm_num [mean, sum_two_bits, hff, hft, htf, htt] at hm
  all_goals
    solve
    | refine ⟨(false, false), false, ?_⟩
      apply two_bits_ext <;> simp [eightPhase, pointPhase, boolSign, hff, hft, htf, htt]
    | refine ⟨(false, false), true, ?_⟩
      apply two_bits_ext <;> simp [eightPhase, pointPhase, boolSign, hff, hft, htf, htt]
    | refine ⟨(false, true), false, ?_⟩
      apply two_bits_ext <;> simp [eightPhase, pointPhase, boolSign, hff, hft, htf, htt]
    | refine ⟨(false, true), true, ?_⟩
      apply two_bits_ext <;> simp [eightPhase, pointPhase, boolSign, hff, hft, htf, htt]
    | refine ⟨(true, false), false, ?_⟩
      apply two_bits_ext <;> simp [eightPhase, pointPhase, boolSign, hff, hft, htf, htt]
    | refine ⟨(true, false), true, ?_⟩
      apply two_bits_ext <;> simp [eightPhase, pointPhase, boolSign, hff, hft, htf, htt]
    | refine ⟨(true, true), false, ?_⟩
      apply two_bits_ext <;> simp [eightPhase, pointPhase, boolSign, hff, hft, htf, htt]
    | refine ⟨(true, true), true, ?_⟩
      apply two_bits_ext <;> simp [eightPhase, pointPhase, boolSign, hff, hft, htf, htt]

/-- Complete two-variable bent classification, starting from Boolean and Walsh conditions.
@isnad1 id=ex.2h1v.s6.53b19d5df379 from=translated src=- shape=d21e99c2 vocab=0e070430
-/
theorem classify_bent2 (f : (Fin 2 → Bool) → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : IsBent2 f) :
    ∃ p : Bool × Bool, ∃ complement : Bool, f = eightPhase p complement := by
  apply classify_of_mean_sq f hf
  simpa only [normalizedWalsh_zero] using hb (false, false)

/-- Full-noise Hellinger theorem for every two-variable bent Boolean function,
under the actual finite product BSC, with no moment or classification hypothesis.
@isnad1 id=le.3h2v.s7.dcb7de59a901 from=translated src=- shape=ed3b3e89 vocab=1c848b5a
-/
theorem bent2_hellinger (f : (Fin 2 → Bool) → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : IsBent2 f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    objective ((cubeBSC 2 ρ hρ).apply f) ≤ 1 - root ρ := by
  obtain ⟨p, complement, rfl⟩ := classify_bent2 f hf hb
  exact eightPhase_hellinger p complement ρ hρ

/-- Strictness for every two-variable bent Boolean function when `ρ > 0`.
@isnad1 id=lt.4h2v.s7.aa161ce7783d from=translated src=- shape=ae4a3c7c vocab=94571655
-/
theorem bent2_hellinger_strict (f : (Fin 2 → Bool) → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : IsBent2 f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρpos : 0 < ρ) :
    objective ((cubeBSC 2 ρ hρ).apply f) < 1 - root ρ := by
  obtain ⟨p, complement, rfl⟩ := classify_bent2 f hf hb
  exact eightPhase_hellinger_strict p complement ρ hρ hρpos

end Hellinger.TwoBitCase
