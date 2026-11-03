/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.BoundedDenom
import Tengoku.Seed.RingTheory.HahnSeries.Summable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # BPR §2.6 — the cumulative exponents and the limit Puiseux series `x̄`

Once the multiplicity stabilizes the recursion runs with `xₙ ≠ 0`, `ξₙ > 0`, and strictly increasing
exponents `ηₙ = Σ_{k≤n} ξₖ ∈ (1/M)ℤ`. This file builds the root `x̄ = Σₙ xₙ ε^{ηₙ}`.

* `InLattice M q` ("`q ∈ (1/M)ℤ`") + closure; `etaSeq`/`strictMono_etaSeq`/`etaSeq_inLattice`.
* The limit at integer-exponent level: `lfam : SummableFamily ℤ R ℕ`, `zlim := lfam.hsum`, and
  `xbar := puiseuxEmb R M zlim` — automatically a Puiseux series (`xbarP`), with its
  coefficients/order read off through `embDomain` (`xbar_coeff_eta`, `xbar_coeff_notMem`). -/

namespace Azurite.BPR

open Polynomial HahnSeries

variable {R : Type*} [Field R] [IsRealClosed R]

/-- `q` lies in the lattice `(1/M)ℤ`.-/
def InLattice (M : ℕ+) (q : ℚ) : Prop := ∃ k : ℤ, q = (k : ℚ) / (M : ℚ)

/-- The lattice grows as the denominator grows: `M₁ ∣ M₂ ⇒ (1/M₁)ℤ ⊆ (1/M₂)ℤ`.
@isnad1 id=inlattic.2h3v.s4.29b2d2254762 from=translated src=- shape=ccc714de vocab=bdf63b04
-/
theorem InLattice.mono {q : ℚ} {M₁ M₂ : ℕ+} (h : M₁ ∣ M₂) (hq : InLattice M₁ q) :
    InLattice M₂ q := by
  obtain ⟨k, hk⟩ := hq
  obtain ⟨t, ht⟩ := h
  have hdt : ((t : ℕ) : ℚ) ≠ 0 := by exact_mod_cast t.pos.ne'
  have hM₂ : ((M₂ : ℕ) : ℚ) = ((M₁ : ℕ) : ℚ) * ((t : ℕ) : ℚ) := by exact_mod_cast ht
  refine ⟨k * (t : ℤ), ?_⟩
  rw [hk, hM₂]; push_cast; rw [mul_div_mul_right _ _ hdt]

/--
@isnad1 id=inlattic.0h1v.s3.eaf625b4bea3 from=translated src=- shape=8ba9e24c vocab=97938a66
-/
theorem inLattice_zero (M : ℕ+) : InLattice M 0 := ⟨0, by simp⟩

/--
@isnad1 id=inlattic.2h3v.s4.6d548fe5330f from=translated src=- shape=d203bb48 vocab=98a88a7b
-/
theorem InLattice.add {M : ℕ+} {a b : ℚ} (ha : InLattice M a) (hb : InLattice M b) :
    InLattice M (a + b) := by
  obtain ⟨k, hk⟩ := ha; obtain ⟨l, hl⟩ := hb
  exact ⟨k + l, by rw [hk, hl]; push_cast; ring⟩

/--
@isnad1 id=inlattic.1h4v.s5.dcb667c1e153 from=translated src=- shape=7124f6c5 vocab=4f0102d1
-/
theorem InLattice.sum {M : ℕ+} {ι : Type*} (s : Finset ι) {f : ι → ℚ}
    (hf : ∀ i ∈ s, InLattice M (f i)) : InLattice M (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty]; exact inLattice_zero M
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a t)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Every rational lies in the lattice with denominator its own denominator.
@isnad1 id=inlattic.0h1v.s4.6a77a702bcb8 from=translated src=- shape=667b3f90 vocab=df0a03d8
-/
theorem inLattice_den (q : ℚ) : InLattice ⟨q.den, q.pos⟩ q := by
  refine ⟨q.num, ?_⟩
  show q = (q.num : ℚ) / (q.den : ℚ)
  exact (Rat.num_div_den q).symm

/-- Finitely many rationals share a common denominator.
@isnad1 id=ex.0h3v.s5.4f2a77294e96 from=translated src=- shape=bbd91eb6 vocab=e5792b6f
-/
theorem exists_inLattice_finset {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    ∃ M : ℕ+, ∀ i ∈ s, InLattice M (f i) := by
  classical
  refine ⟨∏ i ∈ s, ⟨(f i).den, (f i).pos⟩, fun i hi => ?_⟩
  exact (inLattice_den (f i)).mono (Finset.dvd_prod_of_mem _ hi)

/-- The cumulative exponent `ηₙ = ξ₀ + ⋯ + ξₙ`, where `xₙ` sits at exponent `ηₙ` in `x̄`.-/
noncomputable def etaSeq (s0 : RecState R) (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), xiSeq s0 k

/-- The cumulative exponents strictly increase (each increment `ξₙ > 0` away from the barrier).
@isnad1 id=strictmo.1h2v.s10.cc485cb65e57 from=translated src=- shape=4354d53d vocab=087330ef
-/
theorem strictMono_etaSeq (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) :
    StrictMono (etaSeq s0) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h : etaSeq s0 (n + 1) = etaSeq s0 n + xiSeq s0 (n + 1) := by
    simp only [etaSeq, Finset.sum_range_succ]
  rw [h]; linarith [xiSeq_pos s0 hnb (n + 1)]

/-- All cumulative exponents share one denominator: `ηₙ ∈ (1/M)ℤ`.
@isnad1 id=ex.0h2v.s4.9a1cd2a1cf26 from=translated src=- shape=e7a15df6 vocab=00858094
-/
theorem etaSeq_inLattice (s0 : RecState R) : ∃ M : ℕ+, ∀ n, InLattice M (etaSeq s0 n) := by
  obtain ⟨N, Mt, hmem⟩ := stateSeq_xibeta_mem s0
  obtain ⟨Mh, hMh⟩ := exists_inLattice_finset (Finset.range N) (xiSeq s0)
  refine ⟨Mh * Mt, fun n => ?_⟩
  rw [etaSeq]
  apply InLattice.sum
  intro k _
  rcases lt_or_ge k N with hkN | hkN
  · exact (hMh k (Finset.mem_range.mpr hkN)).mono (dvd_mul_right Mh Mt)
  · exact InLattice.mono (dvd_mul_left Mt Mh) (hmem k hkN).1

/-- A common denominator `M` for every cumulative exponent `ηₙ`.-/
noncomputable def limM (s0 : RecState R) : ℕ+ := (etaSeq_inLattice s0).choose

/-- `ηₙ = γₙ / M`: the integer numerator of the cumulative exponent.-/
noncomputable def gammaSeq (s0 : RecState R) (n : ℕ) : ℤ := ((etaSeq_inLattice s0).choose_spec n).choose

/--
@isnad1 id=eq.0h3v.s5.caf3aec6fce4 from=translated src=- shape=ca695269 vocab=77c06ac7
-/
theorem etaSeq_eq_gamma (s0 : RecState R) (n : ℕ) :
    etaSeq s0 n = (gammaSeq s0 n : ℚ) / (limM s0 : ℚ) :=
  ((etaSeq_inLattice s0).choose_spec n).choose_spec

/-- The integer numerators strictly increase (since `ηₙ` does and `M > 0`).
@isnad1 id=strictmo.1h2v.s10.7bfe3cc0d447 from=translated src=- shape=907fdd2a vocab=ccd110f7
-/
theorem strictMono_gammaSeq (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) :
    StrictMono (gammaSeq s0) := by
  intro a b hab
  have h := strictMono_etaSeq s0 hnb hab
  rw [etaSeq_eq_gamma, etaSeq_eq_gamma] at h
  have hM : (0 : ℚ) < (limM s0 : ℚ) := by exact_mod_cast (limM s0).pos
  rw [div_lt_div_iff_of_pos_right hM] at h
  exact_mod_cast h

/-- The summable family `n ↦ xₙ ε^{γₙ}` of integer-exponent monomials.-/
noncomputable def lfam (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) :
    SummableFamily ℤ R ℕ where
  toFun n := HahnSeries.single (gammaSeq s0 n) (xSeq s0 n)
  isPWO_iUnion_support' := by
    have hwf : WellFounded (Function.onFun (· < ·) (gammaSeq s0)) := by
      have heq : Function.onFun (· < ·) (gammaSeq s0) = ((· < ·) : ℕ → ℕ → Prop) := by
        ext a b; exact (strictMono_gammaSeq s0 hnb).lt_iff_lt
      rw [heq]; exact wellFounded_lt
    have hWF : (Set.range (gammaSeq s0)).IsWF := Set.wellFoundedOn_range.mpr hwf
    refine (hWF.isPWO).mono (Set.iUnion_subset (fun n => ?_))
    exact support_single_subset.trans (Set.singleton_subset_iff.mpr ⟨n, rfl⟩)
  finite_co_support' g := by
    refine Set.Finite.subset (s := {n | gammaSeq s0 n = g}) ?_ ?_
    · refine Set.Subsingleton.finite (fun a ha b hb => ?_)
      rw [Set.mem_ofPred_eq] at ha hb
      exact (strictMono_gammaSeq s0 hnb).injective (ha.trans hb.symm)
    · intro n hn
      rw [Set.mem_ofPred_eq] at hn ⊢
      by_contra hne
      exact hn (coeff_single_of_ne (Ne.symm hne))

/-- The integer-exponent limit `z = Σₙ xₙ ε^{γₙ} ∈ R⟦ℤ⟧`.-/
noncomputable def zlim (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) :
    HahnSeries ℤ R := (lfam s0 hnb).hsum

/-- The limit Puiseux series `x̄` as a raw Hahn series (`= ε`-scaling of `z`).-/
noncomputable def xbar (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) :
    HahnSeries ℚ R := puiseuxEmb R (limM s0) (zlim s0 hnb)

/--
@isnad1 id=mem.1h2v.s10.2c1131cd6d56 from=translated src=- shape=e4186ea6 vocab=41a9d490
-/
theorem xbar_mem (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) :
    xbar s0 hnb ∈ puiseuxSubfield R (limM s0) := by
  rw [xbar, puiseuxSubfield, RingHom.mem_fieldRange]; exact ⟨zlim s0 hnb, rfl⟩

/-- The limit as an element of the field `R⟨⟨ε⟩⟩` (it is a Laurent series in `ε^{1/M}`).-/
noncomputable def xbarP (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) :
    PuiseuxSeries R :=
  ⟨xbar s0 hnb, (mem_puiseuxSeries_iff R).mpr ⟨limM s0, xbar_mem s0 hnb⟩⟩

/--
@isnad1 id=eq.1h2v.s10.39e75c66807d from=translated src=- shape=97057c5f vocab=370b2052
-/
@[simp] theorem xbarP_coe (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) :
    ((xbarP s0 hnb : PuiseuxSeries R) : HahnSeries ℚ R) = xbar s0 hnb := rfl

end Azurite.BPR
