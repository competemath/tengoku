/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.CVaRDenseSupremum
import Tengoku.Randomsettheory.RandomSetTheory.FiniteFutureValue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Signed classes and absolute suprema

An absolute supremum is an ordinary supremum after adjoining the negatives
of all members of the class.  This file implements that elementary bridge
with the disjoint sum `T ⊕ T`.  The construction works both for finite
classes and for continuous classes: the sum topology makes continuity a
componentwise statement.

The identities in this file are deterministic.  In particular, they make no
probabilistic or maximal-inequality assumption and can be reused by the Rio
endpoint without duplicating its martingale argument.
-/

open Real Set Finset MeasureTheory TopologicalSpace
open scoped BigOperators ProbabilityTheory ENNReal NNReal Topology

noncomputable section

namespace ProbabilityTheory

variable {Omega T Z : Type*} {mOmega : MeasurableSpace Omega}
  [MeasurableSpace Z]

/-- Adjoin a positive and a negative copy of every member of a finite class.-/
def signedFinset (s : Finset T) : Finset (T ⊕ T) :=
  s.disjSum s

omit [MeasurableSpace Z] in
theorem signedFinset_nonempty {s : Finset T} (hs : s.Nonempty) :
    (signedFinset s).Nonempty := by
  exact ⟨Sum.inl hs.choose, by simp [signedFinset, hs.choose_spec]⟩

/-- The signed extension of a scalar class.  The left copy carries the
original value and the right copy its negative.-/
def signedClass (f : T → ℝ) : T ⊕ T → ℝ :=
  Sum.elim f fun t ↦ -f t

omit [MeasurableSpace Z] in
@[simp]
theorem signedClass_inl (f : T → ℝ) (t : T) :
    signedClass f (Sum.inl t) = f t := rfl

omit [MeasurableSpace Z] in
@[simp]
theorem signedClass_inr (f : T → ℝ) (t : T) :
    signedClass f (Sum.inr t) = -f t := rfl

/-- Signed extension of coordinatewise additive kernels.-/
def signedCoordinateKernel (W : Fin n → Z → T → ℝ) :
    Fin n → Z → T ⊕ T → ℝ :=
  fun j z ↦ signedClass (W j z)

omit [MeasurableSpace Z] in
@[simp]
theorem sum_signedCoordinateKernel_inl
    (W : Fin n → Z → T → ℝ) (x : Fin n → Z) (t : T) :
    (∑ j : Fin n, signedCoordinateKernel W j (x j) (Sum.inl t)) =
      ∑ j : Fin n, W j (x j) t := by
  rfl

omit [MeasurableSpace Z] in
@[simp]
theorem sum_signedCoordinateKernel_inr
    (W : Fin n → Z → T → ℝ) (x : Fin n → Z) (t : T) :
    (∑ j : Fin n, signedCoordinateKernel W j (x j) (Sum.inr t)) =
      -∑ j : Fin n, W j (x j) t := by
  simp [signedCoordinateKernel, signedClass]

/-- The absolute supremum of a finite additive class.-/
def finiteCoordinateSumAbsSupremum
    (s : Finset T) (hs : s.Nonempty)
    (W : Fin n → Z → T → ℝ) (x : Fin n → Z) : ℝ :=
  s.sup' hs fun t ↦ |∑ j : Fin n, W j (x j) t|

omit [MeasurableSpace Z] in
/-- A finite supremum over the signed class is exactly the absolute supremum
over the original class.-/
theorem finiteCoordinateSumSupremum_signedCoordinateKernel
    (s : Finset T) (hs : s.Nonempty)
    (W : Fin n → Z → T → ℝ) (x : Fin n → Z) :
    finiteCoordinateSumSupremum (signedFinset s)
        (signedFinset_nonempty hs) (signedCoordinateKernel W) x =
      finiteCoordinateSumAbsSupremum s hs W x := by
  unfold finiteCoordinateSumSupremum finiteCoordinateSumAbsSupremum
  apply le_antisymm
  · apply Finset.sup'_le (signedFinset_nonempty hs)
    intro u hu
    rcases u with t | t
    · have ht : t ∈ s := by simpa [signedFinset] using hu
      rw [sum_signedCoordinateKernel_inl]
      exact (le_abs_self (∑ j : Fin n, W j (x j) t)).trans
        (Finset.le_sup' (fun v ↦ |∑ j : Fin n, W j (x j) v|) ht)
    · have ht : t ∈ s := by simpa [signedFinset] using hu
      rw [sum_signedCoordinateKernel_inr]
      exact (neg_le_abs (∑ j : Fin n, W j (x j) t)).trans
        (Finset.le_sup' (fun v ↦ |∑ j : Fin n, W j (x j) v|) ht)
  · apply Finset.sup'_le hs
    intro t ht
    by_cases hnonneg : 0 ≤ ∑ j : Fin n, W j (x j) t
    · rw [abs_of_nonneg hnonneg]
      exact Finset.le_sup'
        (fun u ↦ ∑ j : Fin n, signedCoordinateKernel W j (x j) u)
        (by simpa [signedFinset] using ht : Sum.inl t ∈ signedFinset s)
    · rw [abs_of_neg (lt_of_not_ge hnonneg)]
      simpa only [sum_signedCoordinateKernel_inr] using
        (Finset.le_sup'
          (fun u ↦ ∑ j : Fin n, signedCoordinateKernel W j (x j) u)
          (by simpa [signedFinset] using ht : Sum.inr t ∈ signedFinset s))

theorem measurable_signedCoordinateKernel
    (W : Fin n → Z → T → ℝ)
    {j : Fin n} {u : T ⊕ T}
    (hW : ∀ t, Measurable (fun z ↦ W j z t)) :
    Measurable (fun z ↦ signedCoordinateKernel W j z u) := by
  cases u with
  | inl t => exact hW t
  | inr t =>
      change Measurable (fun z ↦ -W j z t)
      exact (hW t).neg

omit [MeasurableSpace Z] in
theorem abs_signedCoordinateKernel
    (W : Fin n → Z → T → ℝ) (j : Fin n) (z : Z) (u : T ⊕ T) :
    |signedCoordinateKernel W j z u| = |W j z (u.elim id id)| := by
  cases u <;> simp [signedCoordinateKernel, signedClass]

end ProbabilityTheory

namespace RandomSetTheory

variable {Omega T : Type*}

/-- Signed extension of a process.-/
def signedProcess (F : Omega → T → ℝ) : Omega → T ⊕ T → ℝ :=
  fun omega ↦ ProbabilityTheory.signedClass (F omega)

@[simp]
theorem signedProcess_inl (F : Omega → T → ℝ) (omega : Omega) (t : T) :
    signedProcess F omega (Sum.inl t) = F omega t := rfl

@[simp]
theorem signedProcess_inr (F : Omega → T → ℝ) (omega : Omega) (t : T) :
    signedProcess F omega (Sum.inr t) = -F omega t := rfl

variable [TopologicalSpace T]

/-- Continuity is preserved by signed extension.-/
theorem continuous_signedProcess
    (F : Omega → T → ℝ) (omega : Omega)
    (hF : Continuous (F omega)) :
    Continuous (signedProcess F omega) := by
  exact hF.sumElim hF.neg

omit [TopologicalSpace T] in
/-- The supremum of a bounded signed class is the supremum of the absolute
values of the original class.-/
theorem iSup_signedProcess_eq_iSup_abs
    [Nonempty T] (F : Omega → T → ℝ) (omega : Omega) (B : ℝ)
    (hB : ∀ t, |F omega t| ≤ B) :
    (⨆ u : T ⊕ T, signedProcess F omega u) = ⨆ t : T, |F omega t| := by
  have hBnonneg : 0 ≤ B :=
    (abs_nonneg (F omega (Classical.choice inferInstance))).trans (hB _)
  have hsignedBdd : BddAbove (Set.range (signedProcess F omega)) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨u, rfl⟩
    cases u with
    | inl t => exact (le_abs_self _).trans (hB t)
    | inr t => exact (neg_le_abs _).trans (hB t)
  have habsBdd : BddAbove (Set.range fun t ↦ |F omega t|) := by
    exact ⟨B, by rintro _ ⟨t, rfl⟩; exact hB t⟩
  apply le_antisymm
  · apply ciSup_le
    intro u
    cases u with
    | inl t =>
        exact (le_abs_self _).trans (le_ciSup habsBdd t)
    | inr t =>
        exact (neg_le_abs _).trans (le_ciSup habsBdd t)
  · apply ciSup_le
    intro t
    rw [abs_eq_max_neg]
    exact max_le
      (le_ciSup hsignedBdd (Sum.inl t))
      (le_ciSup hsignedBdd (Sum.inr t))

variable [SeparableSpace T] [Nonempty T] [MeasurableSpace Omega]

/-- A uniform finite-prefix CVaR estimate on the signed continuous class
passes to the centered full absolute supremum.  The finite prefixes are the
canonical dense prefixes of `T ⊕ T`, so this theorem plugs directly into a
finite-class endpoint such as `FiniteSupremumRioSigned`.-/
theorem conditionalValueAtRisk_centered_iSup_abs_le_of_signedDensePrefixes
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (F : Omega → T → ℝ) (B : Omega → ℝ)
    (hcontinuous : ∀ omega, Continuous (F omega))
    (hmeas : ∀ t, Measurable (fun omega ↦ F omega t))
    (hB : Integrable B mu)
    (hdom : ∀ omega t, |F omega t| ≤ |B omega|)
    {alpha C : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hfinite : ∀ n,
      ProbabilityTheory.conditionalValueAtRisk alpha
        (fun omega ↦
          densePrefixSupremum (signedProcess F omega) n -
            ∫ z, densePrefixSupremum (signedProcess F z) n ∂mu) mu ≤ C) :
    ProbabilityTheory.conditionalValueAtRisk alpha
        (fun omega ↦
          (⨆ t, |F omega t|) - ∫ z, (⨆ t, |F z t|) ∂mu) mu ≤ C := by
  let SF : Omega → T ⊕ T → ℝ := signedProcess F
  have hSFcontinuous : ∀ omega, Continuous (SF omega) := by
    intro omega
    exact continuous_signedProcess F omega (hcontinuous omega)
  have hSFmeasAll : ∀ u : T ⊕ T, Measurable (fun omega ↦ SF omega u) := by
    intro u
    cases u with
    | inl t => exact hmeas t
    | inr t =>
        change Measurable (fun omega ↦ -F omega t)
        exact (hmeas t).neg
  have hSFmeas : ∀ k,
      Measurable (fun omega ↦ SF omega (denseSeq (T ⊕ T) k)) := by
    intro k
    exact hSFmeasAll _
  have hSFdom : ∀ omega u, |SF omega u| ≤ |B omega| := by
    intro omega u
    cases u with
    | inl t => exact hdom omega t
    | inr t => simpa only [SF, signedProcess_inr, abs_neg] using hdom omega t
  have hsource := conditionalValueAtRisk_centered_iSup_le_of_densePrefixes
    SF B hSFcontinuous hSFmeas hB hSFdom halpha0 halpha1 (by
      intro n
      simpa only [SF] using hfinite n)
  have hsup : ∀ omega, (⨆ u, SF omega u) = ⨆ t, |F omega t| := by
    intro omega
    exact iSup_signedProcess_eq_iSup_abs F omega |B omega| (hdom omega)
  simpa only [hsup] using hsource

end RandomSetTheory
