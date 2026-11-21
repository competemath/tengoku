/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.FiniteSymmetrization
import Tengoku.Seed.Probability.HasLaw

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Independence of coordinatewise ghost differences

This file records the product-law step used in empirical-process
symmetrization.  If the finite restrictions of the coordinate processes
`X i` are independent, then the differences between two independent copies
are independent as process-valued random variables under `mu.prod mu`.
-/

open MeasureTheory
open scoped ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

variable {Omega T ι : Type*} [MeasurableSpace Omega]
  {mu : Measure Omega}

/-- Independent process-valued coordinates remain independent after taking
the coordinatewise difference of two independent copies.

The finite set `N` is built into the codomain.  This is the exact form needed
for finite-prefix symmetrization before passing to a dense continuous class.
@isnad1 id=iindepfu.2h6v.s8.8019d545f3b3 from=translated src=- shape=b37a7399 vocab=cdb8ac12
-/
theorem iIndepFun_finiteProcess_ghostDifference
    [Fintype ι] [IsProbabilityMeasure mu]
    (X : ι → Omega → T → ℝ) (N : Finset T)
    (hXmeas : ∀ i, Measurable (fun omega (t : N) ↦ X i omega t))
    (hXindep : iIndepFun
      (fun i omega (t : N) ↦ X i omega t) mu) :
    iIndepFun
      (fun i (z : Omega × Omega) (t : N) ↦
        X i z.1 t - X i z.2 t) (mu.prod mu) := by
  let V : ι → Omega → (N → ℝ) :=
    fun i omega t ↦ X i omega t
  let nu : ι → Measure (N → ℝ) := fun i ↦ mu.map (V i)
  have hVmeas : ∀ i, Measurable (V i) := by
    intro i
    exact hXmeas i
  have hVlaw : ∀ i, HasLaw (V i) (nu i) mu := by
    intro i
    exact
      { aemeasurable := (hVmeas i).aemeasurable
        map_eq := rfl }
  have hVindep : iIndepFun V mu := by
    simpa only [V] using hXindep
  have hJointLaw :
      HasLaw (fun omega i ↦ V i omega) (Measure.pi nu) mu :=
    hVindep.hasLaw_pi hVlaw
  let J : Omega → (ι → (N → ℝ)) := fun omega i ↦ V i omega
  have hJmeas : Measurable J := by
    exact measurable_pi_lambda _ hVmeas
  have hJlaw : HasLaw J (Measure.pi nu) mu := by
    simpa only [J] using hJointLaw
  have hcopiesIndep :
      IndepFun (fun z : Omega × Omega ↦ J z.1)
        (fun z : Omega × Omega ↦ J z.2) (mu.prod mu) :=
    indepFun_prod hJmeas hJmeas
  have hfstLaw : HasLaw (fun z : Omega × Omega ↦ J z.1)
      (Measure.pi nu) (mu.prod mu) := by
    simpa only [Function.comp_def] using
      hJlaw.comp (measurePreserving_fst.hasLaw :
        HasLaw Prod.fst mu (mu.prod mu))
  have hsndLaw : HasLaw (fun z : Omega × Omega ↦ J z.2)
      (Measure.pi nu) (mu.prod mu) := by
    simpa only [Function.comp_def] using
      hJlaw.comp (measurePreserving_snd.hasLaw :
        HasLaw Prod.snd mu (mu.prod mu))
  have hpairArrays : HasLaw
      (fun z : Omega × Omega ↦ (J z.1, J z.2))
      ((Measure.pi nu).prod (Measure.pi nu)) (mu.prod mu) :=
    hcopiesIndep.hasLaw_prod hfstLaw hsndLaw
  let pairByCoordinate :
      ((ι → (N → ℝ)) × (ι → (N → ℝ))) → (ι → ((N → ℝ) × (N → ℝ))) :=
    (MeasurableEquiv.arrowProdEquivProdArrow (N → ℝ) (N → ℝ) ι).symm
  have hpairByCoordinatePreserving : MeasurePreserving pairByCoordinate
      ((Measure.pi nu).prod (Measure.pi nu))
      (Measure.pi fun i ↦ (nu i).prod (nu i)) := by
    simpa only [pairByCoordinate] using
      (measurePreserving_arrowProdEquivProdArrow
        (N → ℝ) (N → ℝ) ι nu nu).symm
  have hallPairLaw : HasLaw
      (fun z : Omega × Omega ↦ pairByCoordinate (J z.1, J z.2))
      (Measure.pi fun i ↦ (nu i).prod (nu i)) (mu.prod mu) := by
    exact hpairByCoordinatePreserving.fun_comp_hasLaw hpairArrays
  let P : ι → (Omega × Omega) → ((N → ℝ) × (N → ℝ)) :=
    fun i z ↦ (V i z.1, V i z.2)
  have hPmeas : ∀ i, Measurable (P i) := by
    intro i
    exact ((hVmeas i).comp measurable_fst).prodMk
      ((hVmeas i).comp measurable_snd)
  have hPcoordLaw : ∀ i, HasLaw (P i) ((nu i).prod (nu i)) (mu.prod mu) := by
    intro i
    have hiIndep : IndepFun (fun z : Omega × Omega ↦ V i z.1)
        (fun z : Omega × Omega ↦ V i z.2) (mu.prod mu) :=
      indepFun_prod (hVmeas i) (hVmeas i)
    have hiFst : HasLaw (fun z : Omega × Omega ↦ V i z.1)
        (nu i) (mu.prod mu) := by
      simpa only [Function.comp_def] using
        (hVlaw i).comp (measurePreserving_fst.hasLaw :
          HasLaw Prod.fst mu (mu.prod mu))
    have hiSnd : HasLaw (fun z : Omega × Omega ↦ V i z.2)
        (nu i) (mu.prod mu) := by
      simpa only [Function.comp_def] using
        (hVlaw i).comp (measurePreserving_snd.hasLaw :
          HasLaw Prod.snd mu (mu.prod mu))
    simpa only [P] using hiIndep.hasLaw_prod hiFst hiSnd
  have hPairsIndep : iIndepFun P (mu.prod mu) := by
    apply (iIndepFun_iff_hasLaw_pi_pi hPcoordLaw).2
    have hcoordinateIdentity :
        (fun z : Omega × Omega ↦ pairByCoordinate (J z.1, J z.2)) =
          (fun z i ↦ (V i z.1, V i z.2)) := by
      funext z i
      rfl
    rw [hcoordinateIdentity] at hallPairLaw
    simpa only [P] using hallPairLaw
  have hDiff := hPairsIndep.comp
      (fun _ (v : (N → ℝ) × (N → ℝ)) t ↦ v.1 t - v.2 t)
      (fun _ ↦ by fun_prop)
  simpa only [P, V, Function.comp_def] using hDiff

/-- A finite maximum of absolute coordinates is integrable whenever it is
measurable coordinatewise and dominated by one integrable envelope.

This helper is intentionally phrased with `Finset.sup'`, so modules defining
their own finite-vector supremum can use it without creating an import cycle.
@isnad1 id=integrab.4h6v.s7.bf0ce86051a1 from=translated src=- shape=0fe74b52 vocab=ece4ca43
-/
theorem integrable_finsetSupAbs_of_le
    {Omega T : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega}
    (s : Finset T) (hs : s.Nonempty)
    (F : Omega → T → ℝ) (B : Omega → ℝ)
    (hFmeas : ∀ t ∈ s, Measurable (fun omega ↦ F omega t))
    (hBint : Integrable B mu)
    (hdom : ∀ omega t, t ∈ s → |F omega t| ≤ |B omega|) :
    Integrable
      (fun omega ↦ s.sup' hs (fun t ↦ |F omega t|)) mu := by
  let S : Omega → ℝ := fun omega ↦ s.sup' hs (fun t ↦ |F omega t|)
  have hSmeas : Measurable S := by
    have h : Measurable
        (s.sup' hs (fun t ↦ fun omega : Omega ↦ |F omega t|)) := by
      apply Finset.measurable_sup' hs
      intro t ht
      exact (hFmeas t ht).abs
    convert h using 1
    funext omega
    exact (Finset.sup'_apply hs
      (fun t ↦ fun z ↦ |F z t|) omega).symm
  apply hBint.abs.mono' hSmeas.aestronglyMeasurable
  exact ae_of_all mu fun omega ↦ by
    have hSnonneg : 0 ≤ S omega := by
      obtain ⟨t, ht⟩ := hs
      exact (abs_nonneg (F omega t)).trans
        (Finset.le_sup' (fun u ↦ |F omega u|) ht)
    have hSupper : S omega ≤ |B omega| := by
      apply Finset.sup'_le hs
      intro t ht
      exact hdom omega t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg hSnonneg] using hSupper

end ProbabilityTheory
