/-
Copyright (c) 2026 Imperial College London. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku.LeanPool.LeanPool.Odlyzko.DedekindZeta.LocalFactor
public import Tengoku

/-! TODO: Add doc-string. -/

@[expose] public section

open Ideal IsDedekindDomain

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

/-- A prime ideal norm used in the Odlyzko-bound argument. -/
noncomputable def primeIdealNorm (P : HeightOneSpectrum (𝓞 K)) : ℕ :=
  absNorm P.asIdeal

/--
@isnad1 id=lt.0h2v.s4.dddc5fef1724 from=translated src=- shape=a6d7fd62 vocab=3021c0e8
-/
lemma one_lt_primeIdealNorm (P : HeightOneSpectrum (𝓞 K)) :
    1 < primeIdealNorm K P := by
  apply Nat.one_lt_iff_ne_zero_and_ne_one.mpr
  constructor
  · simpa [primeIdealNorm, Ideal.absNorm_eq_zero_iff] using P.ne_bot
  · simpa [primeIdealNorm, Ideal.absNorm_eq_one_iff] using P.isPrime.ne_top

/-- A prime ideal factor used in the Odlyzko-bound argument. -/
noncomputable def primeIdealFactor (P : HeightOneSpectrum (𝓞 K)) (s : ℂ) : ℂ :=
  localFactor (primeIdealNorm K P) s

/--
@isnad1 id=ne.1h3v.s5.0ef09cb99ea3 from=translated src=- shape=eaa9d12d vocab=51c0a77e
-/
lemma primeIdealFactor_ne_zero (P : HeightOneSpectrum (𝓞 K)) {s : ℂ} (hs : 0 < s.re) :
    primeIdealFactor K P s ≠ 0 :=
  localFactor_ne_zero (one_lt_primeIdealNorm K P) hs

end NumberField.Odlyzko
