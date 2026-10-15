/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Tengoku

/-! # Tendstolems -/

@[expose] public section

open TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

/--
@isnad1 id=tendsto.1h2v.s6.5e8ab8ed26a9 from=translated src=- shape=f181c53a vocab=a2614528
-/
lemma pnat_tendsto_nat (f : ℕ → ℂ) (x : ℂ) (hf : Tendsto (fun n : ℕ+ => f n) atTop (𝓝 x)) :
  Tendsto f atTop (𝓝 x) := tendsto_comp_val_Ioi_atTop.mp hf

/--
@isnad1 id=tendsto.1h2v.s6.d17c9c00f8e9 from=translated src=- shape=8ac35f24 vocab=a2614528
-/
lemma nat_tendsto_pnat (f : ℕ → ℂ) (x : ℂ) (hf : Tendsto f atTop (𝓝 x)) :
  Tendsto (fun n : ℕ+ => f n) atTop (𝓝 x) := tendsto_comp_val_Ioi_atTop.mpr hf

/--
@isnad1 id=tendsto.2h3v.s6.208b499bb6fd from=translated src=- shape=928c1961 vocab=93a05d97
-/
lemma rest (f g : ℕ → ℂ) (x : ℂ) (hf : Tendsto f atTop (𝓝 x)) (hfg : Tendsto (g - f) atTop (𝓝 0)) :
  Tendsto g atTop (𝓝 x) := by simpa using Tendsto.add hf hfg

/--
@isnad1 id=tendsto.1h1v.s6.cbc019a24044 from=translated src=- shape=ad04f4b9 vocab=10c14afa
-/
lemma aux47 (r : ℂ) (hr : ‖r‖ < 1) : Tendsto (fun n : ℕ => 1 - r^n) atTop (𝓝 1) := by
  simpa using tendsto_const_nhds.sub <| tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr
