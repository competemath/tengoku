/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.RegularLocalBasics
import Tengoku.Seed.Algebra.Field.IsField
import Tengoku.Seed.Data.ENat.Basic
import Tengoku.Seed.Order.KrullDimension
import Tengoku.Seed.RingTheory.Filtration
import Tengoku.Seed.RingTheory.HopkinsLevitzki
import Tengoku.Seed.RingTheory.Ideal.Operations
import Tengoku.Seed.RingTheory.LocalRing.MaximalIdeal.Square
import Tengoku.Seed.RingTheory.RegularLocalRing.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Regular local rings are domains (P2.2)

Route (Stacks 00NP / Matsumura §14): the associated graded `⨁ mⁿ/mⁿ⁺¹` of a regular local
ring is a polynomial ring over the residue field, hence a domain; with Krull intersection
`⋂ mⁿ = 0` this forces `R` itself to be a domain.

This pin of Mathlib has Krull intersection (`Ideal.iInf_pow_eq_bot_of_isLocalRing`) but not the
associated-graded isomorphism, so the general case is out of immediate reach.  This file lands
the largest kernel-checked prefix on the induction route:

1. existence of a parameter `a ∈ m \ m²` in positive dimension;
2. `a ∉ m² ⇒ R/(a)` is again regular, of dimension `dim R - 1`;
3. `IsRegularLocalRing.isDomain` for `ringKrullDim ≤ 1` (dim 0 = field; dim 1 = principal
   maximal ideal + Krull intersection ⇒ unique factorization into a uniformizer).

The dim-2 / general domain statements remain blocked on the graded isomorphism (Stacks 00NO).
-/

noncomputable section

universe u

open IsLocalRing Ideal Module
open scoped Pointwise

variable {R : Type u} [CommRing R]

namespace IsRegularLocalRing

/-! ### Parameters outside `m²` -/

/-- In positive Krull dimension the square of the maximal ideal is proper, so a minimal generator
exists outside `m²`.
@isnad1 id=ex.1h1v.s7.12ed942f0c20 from=translated src=- shape=c755f867 vocab=449bbfbd
-/
theorem exists_mem_maximalIdeal_notMem_sq [IsRegularLocalRing R]
    (hdim : ringKrullDim R ≠ 0) :
    ∃ a : R, a ∈ maximalIdeal R ∧ a ∉ maximalIdeal R ^ 2 := by
  have hlt : maximalIdeal R ^ 2 < maximalIdeal R :=
    maximalIdeal_sq_lt_of_ringKrullDim_ne_zero hdim
  obtain ⟨a, ha, ha2⟩ := Set.exists_of_ssubset hlt
  exact ⟨a, ha, ha2⟩

/-- If `a ∈ m \ m²`, some minimal generating set of `m` contains `a`.
@isnad1 id=ex.2h2v.s8.36a6a572bc10 from=translated src=- shape=6ef1aed8 vocab=9735cbbb
-/
theorem exists_finset_span_card_eq_spanFinrank_containing
    [IsLocalRing R] [IsNoetherianRing R] [DecidableEq R]
    {a : R} (ha : a ∈ maximalIdeal R) (ha2 : a ∉ maximalIdeal R ^ 2) :
    ∃ t : Finset R, a ∈ t ∧ t.card = (maximalIdeal R).spanFinrank ∧
      Submodule.span R (t : Set R) = maximalIdeal R := by
  classical
  set κ := ResidueField R
  set m : Ideal R := maximalIdeal R
  set V := CotangentSpace R
  let v : V := m.toCotangent ⟨a, ha⟩
  have hv : v ≠ 0 := by
    rw [Ne, Ideal.toCotangent_eq_zero]
    exact ha2
  let b := Module.finBasis κ V
  choose w hw using fun i : Fin (Module.finrank κ V) =>
    (Ideal.toCotangent_surjective m) (b i)
  obtain ⟨jIdx, hj⟩ : ∃ jIdx : Fin (Module.finrank κ V), b.repr v jIdx ≠ 0 := by
    by_contra h
    push_neg at h
    have : v = 0 := by
      rw [← b.sum_repr v]
      exact Finset.sum_eq_zero fun i _ => by simp [h i]
    exact hv this
  -- Change-of-basis: `{v} ∪ {b i | i ≠ jIdx}` spans `V`.
  have hspan_cot :
      Submodule.span κ
        (insert v (b '' (Finset.univ.erase jIdx : Set (Fin (Module.finrank κ V))))) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    intro yi hyi
    obtain ⟨i, rfl⟩ := Set.mem_range.mp hyi
    by_cases hijIdx : i = jIdx
    · have hv_eq : v = ∑ idx, b.repr v idx • b idx := (b.sum_repr v).symm
      have hdecomp :
          (∑ idx, b.repr v idx • b idx) - ∑ idx ∈ Finset.univ.erase jIdx, b.repr v idx • b idx =
            b.repr v jIdx • b jIdx := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ jIdx)]
        abel
      have hv' :
          v - ∑ idx ∈ Finset.univ.erase jIdx, b.repr v idx • b idx = b.repr v jIdx • b jIdx :=
        (congrArg (fun w =>
            w - ∑ idx ∈ Finset.univ.erase jIdx, b.repr v idx • b idx) hv_eq).trans hdecomp
      have hbj :
          b jIdx =
            (b.repr v jIdx)⁻¹ •
              (v - ∑ idx ∈ Finset.univ.erase jIdx, b.repr v idx • b idx) := by
        have hinv := congrArg (fun z => (b.repr v jIdx)⁻¹ • z) hv'
        rw [smul_smul, inv_mul_cancel₀ hj, one_smul] at hinv
        exact hinv.symm
      have hv_mem :
          v ∈ Submodule.span κ
            (insert v (b '' (Finset.univ.erase jIdx : Set (Fin (Module.finrank κ V))))) :=
        Submodule.subset_span (Set.mem_insert _ _)
      have hrest :
          ∀ i ∈ Finset.univ.erase jIdx,
            b i ∈ Submodule.span κ
              (insert v (b '' (Finset.univ.erase jIdx : Set (Fin (Module.finrank κ V))))) := by
        intro i hi
        refine Submodule.subset_span (Or.inr ⟨i, hi, rfl⟩)
      rw [hijIdx, hbj]
      exact Submodule.smul_mem _ _
        (sub_mem hv_mem (sum_mem fun idx hi => Submodule.smul_mem _ _ (hrest idx hi)))
    · exact Submodule.subset_span
        (Or.inr ⟨i, Finset.mem_erase.mpr ⟨hijIdx, Finset.mem_univ i⟩, rfl⟩)
  let t : Finset R :=
    insert a ((Finset.univ.erase jIdx).image fun i => (w i : R))
  let ts : Set R := (↑t : Set R)
  let tm : Set m := {y : m | (y : R) ∈ ts}
  have val_span :
      ∀ {z : m}, z ∈ Submodule.span R tm → (z : R) ∈ Submodule.span R ts := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem (Submodule.span R ts)
    | add u v _ _ hu hv => exact add_mem hu hv
    | smul r y _ hy => exact Submodule.smul_mem (Submodule.span R ts) r hy
  have hat : a ∈ t := Finset.mem_insert_self a _
  have ha_ts : a ∈ ts := by simpa [ts, t] using hat
  -- Cotangent images of `t` span `V`, hence `t` generates `m`.
  have hspan : Submodule.span R ts = m := by
    have htop : Submodule.span κ (m.toCotangent '' {x : m | (x : R) ∈ ts}) = ⊤ := by
      rw [eq_top_iff, ← hspan_cot, Submodule.span_le]
      intro yi hyi
      simp only [Set.mem_insert_iff, Set.mem_image] at hyi
      rcases hyi with rfl | ⟨i, hi, rfl⟩
      · exact Submodule.subset_span ⟨⟨a, ha⟩, ha_ts, rfl⟩
      · have hi' : (w i : R) ∈ ts := by
          have : (w i : R) ∈
              insert a ((Finset.univ.erase jIdx).image (fun j : Fin (Module.finrank κ V) => (w j : R))) :=
            Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
          simpa [ts, t] using this
        exact Submodule.subset_span ⟨w i, hi', hw i⟩
    have htopR : Submodule.span R tm = ⊤ := by
      rwa [← CotangentSpace.span_image_eq_top_iff]
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro x hx
      have hx' : x ∈ ts := hx
      by_cases hxa : x = a
      · subst hxa; exact ha
      · have : x ∈ (Finset.univ.erase jIdx).image fun i => (w i : R) := by
          simpa [ts, t, hxa, not_false_eq_true, Finset.mem_insert, Finset.mem_image] using hx'
        obtain ⟨i, _, heq⟩ := Finset.mem_image.mp this
        rw [← heq]
        exact (w i).2
    · intro x hx
      have hmem : (⟨x, hx⟩ : m) ∈ Submodule.span R tm := by
        rw [htopR]
        exact Submodule.mem_top
      exact val_span (z := ⟨x, hx⟩) hmem
  -- Cardinality equals `spanFinrank`.
  have hfin : Module.finrank κ V = m.spanFinrank :=
    (spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)).symm
  have hcard_le : t.card ≤ Module.finrank κ V := by
    have hpos : 0 < Module.finrank κ V := by
      rw [Nat.pos_iff_ne_zero, ne_eq, finrank_cotangentSpace_eq_zero_iff]
      intro hf
      have hmbot : m = ⊥ := isField_iff_maximalIdeal_eq.mp hf
      have ha0 : a = 0 := Ideal.mem_bot.mp (hmbot ▸ ha)
      exact ha2 (by simp [ha0])
    have hle : t.card ≤ (Finset.univ.erase jIdx).card + 1 := by
      rw [show t = insert a ((Finset.univ.erase jIdx).image fun i => (w i : R)) from rfl]
      calc
        (insert a ((Finset.univ.erase jIdx).image fun i => (w i : R))).card
            ≤ ((Finset.univ.erase jIdx).image fun i => (w i : R)).card + 1 :=
          Finset.card_insert_le a _
        _ ≤ (Finset.univ.erase jIdx).card + 1 := Nat.add_le_add_right Finset.card_image_le 1
    have herase : (Finset.univ.erase jIdx).card + 1 = Module.finrank κ V := by
      have hpos' : 0 < Module.finrank κ V := hpos
      simp [Finset.card_erase_of_mem (Finset.mem_univ jIdx), Fintype.card_fin,
        Nat.sub_add_cancel (Nat.succ_le_iff.mp hpos')]
    exact Nat.le_trans hle (Nat.le_of_eq herase)
  have hcard_ge : m.spanFinrank ≤ t.card := by
    rw [← hspan]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite t.finite_toSet).trans
      (le_of_eq (Set.ncard_coe_finset (s := t)))
  refine ⟨t, hat, ?_, hspan⟩
  omega

/-! ### Quotient by a non-`m²` parameter stays regular -/

/-- Quotienting a regular local ring by a parameter outside `m²` drops both Krull dimension and
embedding dimension by exactly one, so the quotient is again regular.
@isnad1 id=isregula.2h2v.s7.243e64d15af9 from=translated src=- shape=99872ffe vocab=e51435d1
-/
theorem quotient_span_singleton_isRegularLocalRing [IsRegularLocalRing R]
    [DecidableEq R]
    {a : R} (ha : a ∈ maximalIdeal R) (ha2 : a ∉ maximalIdeal R ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span {a}) := by
  let Q := R ⧸ Ideal.span {a}
  letI : IsLocalRing Q := ModuleCat.quotientSpanIsLocalRing R a ha
  letI : IsNoetherianRing Q := Ideal.Quotient.isNoetherianRing _
  letI : DecidableEq Q := Classical.decEq Q
  obtain ⟨t, hat, hcard, hspan⟩ :=
    exists_finset_span_card_eq_spanFinrank_containing (R := R) ha ha2
  let t₀ : Finset Q := (t.erase a).image (Ideal.Quotient.mk (Ideal.span {a}))
  have hmap :
      (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {a})) = maximalIdeal Q :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hspanQ : Ideal.span (t₀ : Set Q) = maximalIdeal Q := by
    apply le_antisymm
    · refine Ideal.span_le.mpr ?_
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      have : Ideal.Quotient.mk (Ideal.span {a}) y ∈
          (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {a})) :=
        Ideal.mem_map_of_mem _
          (by
            rw [← hspan]
            exact Submodule.subset_span (Finset.mem_of_mem_erase hy))
      rwa [hmap] at this
    · rw [← hmap, ← hspan, Ideal.map_span]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨y, hy, rfl⟩
      by_cases hya : y = a
      · rw [show Ideal.Quotient.mk (Ideal.span {a}) y = 0 from by
          rw [hya, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_span_singleton_self a]
        exact Ideal.zero_mem (Ideal.span (t₀ : Set Q))
      · exact Ideal.subset_span
          (show Ideal.Quotient.mk (Ideal.span {a}) y ∈ (t₀ : Set Q) from
            Finset.mem_image.mpr ⟨y, Finset.mem_erase.mpr ⟨hya, hy⟩, rfl⟩)
  have hspanFin_le :
      (maximalIdeal Q).spanFinrank ≤ Nat.sub (maximalIdeal R).spanFinrank 1 := by
    have hle : (Ideal.span (t₀ : Set Q)).spanFinrank ≤ t₀.card :=
      (Submodule.spanFinrank_span_le_ncard_of_finite t₀.finite_toSet).trans_eq (by simp)
    have hle' : (maximalIdeal Q).spanFinrank ≤ t₀.card := by
      rwa [← hspanQ]
    have hcard₀ : t₀.card ≤ Nat.sub t.card 1 := by
      have := Finset.card_image_le (s := t.erase a)
        (f := Ideal.Quotient.mk (Ideal.span {a}))
      rwa [Finset.card_erase_of_mem hat] at this
    have hcard₁ : Nat.sub t.card 1 = Nat.sub (maximalIdeal R).spanFinrank 1 := by rw [hcard]
    exact Nat.le_trans hle' (hcard₀.trans (Nat.le_of_eq hcard₁))
  have hdim_le : ringKrullDim R ≤ ringKrullDim Q + 1 := by
    have h := ringKrullDim_le_ringKrullDim_quotSMulTop_succ (x := a) ha
    have hI : Ideal.span {a} = a • (⊤ : Ideal R) := by simp [← Submodule.ideal_span_singleton_smul]
    rw [show ringKrullDim (R ⧸ a • (⊤ : Ideal R)) = ringKrullDim (R ⧸ Ideal.span {a}) from
      ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquivAlgOfEq R hI).symm.toRingEquiv] at h
    simpa [Q] using h
  have hdpos : 1 ≤ (maximalIdeal R).spanFinrank := by
    by_contra h
    have h0 : (maximalIdeal R).spanFinrank = 0 := by omega
    have hmbot : maximalIdeal R = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).1 h0
    have ha0 : a = 0 := Ideal.mem_bot.mp (hmbot ▸ ha)
    exact ha2 (by simp [ha0])
  have hdimQ_ge : ↑(Nat.sub (maximalIdeal R).spanFinrank 1) ≤ ringKrullDim Q := by
    have hpos : 0 < IsRegularLocalRing.embeddingDimension R := by
      rw [IsRegularLocalRing.embeddingDimension]
      exact hdpos
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' hpos
    have hn1 : IsRegularLocalRing.embeddingDimension R = n + 1 := by
      simpa [Nat.succ_eq_add_one] using hn
    have this : (n : WithBot ℕ∞) + 1 ≤ ringKrullDim Q + 1 := by
      have h := hdim_le
      rw [← IsRegularLocalRing.coe_embeddingDimension_eq_ringKrullDim, hn1] at h
      exact h
    have hstep : (n : WithBot ℕ∞) ≤ ringKrullDim Q :=
      ENat.WithBot.add_le_add_natCast_right_iff.mp this
    have hsub : Nat.sub (maximalIdeal R).spanFinrank 1 = n := by
      rw [show (maximalIdeal R).spanFinrank = n + 1 from
        by rw [← IsRegularLocalRing.embeddingDimension, hn1]]
      rfl
    rw [hsub]
    exact_mod_cast hstep
  exact IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (R := Q) <|
    (Nat.cast_le.mpr hspanFin_le).trans hdimQ_ge

/-! ### Domain in dimension ≤ 1 -/

/-- Dimension-zero regular local rings are fields.
@isnad1 id=isfield.1h1v.s5.8d7787828f16 from=translated src=- shape=50208249 vocab=50c089dd
-/
theorem isField_of_ringKrullDim_eq_zero [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 0) : IsField R := by
  have hspan : (maximalIdeal R).spanFinrank = 0 := by
    have := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hdim] at this
    exact_mod_cast this
  have hm : maximalIdeal R = ⊥ :=
    (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).1 hspan
  exact isField_iff_maximalIdeal_eq.mpr hm

/-- In a one-dimensional regular local ring the maximal ideal is principal on a non-nilpotent.
@isnad1 id=ex.1h1v.s6.7ea2a4455f2a from=translated src=- shape=ecfe50e7 vocab=c500947f
-/
theorem exists_generator_maximalIdeal_of_ringKrullDim_eq_one [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 1) :
    ∃ ϖ : R, maximalIdeal R = Ideal.span {ϖ} ∧ ∀ n : ℕ, ϖ ^ n ≠ 0 := by
  have hfin : Module.finrank (ResidueField R) (CotangentSpace R) = 1 := by
    have := (iff_finrank_cotangentSpace (R := R)).mp inferInstance
    rw [hdim] at this
    exact_mod_cast this
  have hprin : (maximalIdeal R).IsPrincipal :=
    finrank_cotangentSpace_le_one_iff.mp (by omega)
  obtain ⟨ϖ, hϖ⟩ := hprin.principal
  refine ⟨ϖ, hϖ, fun n hn => ?_⟩
  have hpow : maximalIdeal R ^ n = ⊥ := by
    rw [hϖ, Ideal.span_singleton_pow, hn, span_singleton_eq_bot.mpr rfl]
  have hArt : IsArtinianRing R :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal R).mpr ⟨n, hpow⟩
  have h0 : Ring.KrullDimLE 0 R :=
    (isArtinianRing_iff_krullDimLE_zero (R := R)).mp hArt
  have hle0 : ringKrullDim R ≤ 0 := (Ring.krullDimLE_iff (n := 0)).mp h0
  rw [hdim] at hle0
  exact absurd hle0 (by decide)

/-- Factor nonzero elements in a one-dimensional regular local ring.
@isnad1 id=ex.3h3v.s7.6d0b38234617 from=translated src=- shape=77f582bf vocab=07f7a735
-/
theorem exists_unit_mul_pow_eq_of_ringKrullDim_eq_one [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 1) {ϖ : R}
    (hϖ : maximalIdeal R = Ideal.span {ϖ}) {a : R} (ha : a ≠ 0) :
    ∃ (u : Rˣ) (k : ℕ), a = u * ϖ ^ k := by
  have hiInf : ⨅ n : ℕ, maximalIdeal R ^ n = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top
  have hex : ∃ n : ℕ, a ∉ maximalIdeal R ^ n := by
    by_contra h
    push_neg at h
    have : a ∈ ⨅ n : ℕ, maximalIdeal R ^ n := by simp [h]
    rw [hiInf] at this
    exact ha (by simpa using this)
  classical
  let k := Nat.find hex
  have hk_not : a ∉ maximalIdeal R ^ k := Nat.find_spec hex
  have hk_pos : 0 < k := by
    rcases k with - | k
    · exfalso
      have : a ∈ maximalIdeal R ^ 0 := by simp [pow_zero]
      exact hk_not this
    · omega
  have hk_mem : a ∈ maximalIdeal R ^ (k - 1) := by
    have : ¬a ∉ maximalIdeal R ^ (k - 1) :=
      Nat.find_min hex (Nat.sub_lt hk_pos (by decide))
    simpa using this
  have : a ∈ Ideal.span {ϖ ^ (k - 1)} := by
    rwa [hϖ, Ideal.span_singleton_pow] at hk_mem
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp this
  have hr_unit : IsUnit r := by
    rw [← notMem_maximalIdeal]
    intro hrm
    have : a ∈ maximalIdeal R ^ k := by
      have hr' : r ∈ Ideal.span {ϖ} := by simpa [hϖ] using hrm
      obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hr'
      have hx : a = s * ϖ ^ k := by
        calc a
            _ = ϖ ^ (k - 1) * r := hr
            _ = ϖ ^ (k - 1) * (ϖ * s) := by rw [hs]
            _ = s * ϖ ^ k := by
              rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hk_pos]
              exact (mul_comm s (ϖ ^ k)).symm
      rw [hx, hϖ, Ideal.span_singleton_pow]
      exact Submodule.smul_mem (Ideal.span {ϖ ^ k}) s (Ideal.mem_span_singleton_self (ϖ ^ k))
    exact hk_not this
  obtain ⟨u, hu⟩ := hr_unit
  exact ⟨u, k - 1, by rw [hr, hu, mul_comm]⟩

/-- **P2.2 (dim ≤ 1).** A regular local ring of Krull dimension at most one is a domain.
@isnad1 id=isdomain.1h1v.s5.4b4b49d3084d from=translated src=- shape=50208249 vocab=37ff1a7f
-/
theorem isDomain_of_ringKrullDim_le_one [IsRegularLocalRing R]
    (hdim : ringKrullDim R ≤ 1) : IsDomain R := by
  have hspan_eq : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  have hle : (maximalIdeal R).spanFinrank ≤ 1 := by
    have : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ 1 := hspan_eq ▸ hdim
    exact_mod_cast this
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with hcard | hcard
  · have h0 : ringKrullDim R = 0 := by
      rw [← hspan_eq, hcard]; rfl
    exact (isField_of_ringKrullDim_eq_zero h0).isDomain
  · have h1 : ringKrullDim R = 1 := by
      rw [← hspan_eq, hcard]; rfl
    obtain ⟨ϖ, hϖ, hpow⟩ := exists_generator_maximalIdeal_of_ringKrullDim_eq_one h1
    have : NoZeroDivisors R := by
      refine ⟨fun {a b} hab => ?_⟩
      by_cases ha0 : a = 0
      · exact Or.inl ha0
      by_cases hb0 : b = 0
      · exact Or.inr hb0
      obtain ⟨u, i, rfl⟩ := exists_unit_mul_pow_eq_of_ringKrullDim_eq_one h1 hϖ ha0
      obtain ⟨v, j, rfl⟩ := exists_unit_mul_pow_eq_of_ringKrullDim_eq_one h1 hϖ hb0
      have hprod : (u * v : R) * ϖ ^ (i + j) = 0 := by
        convert hab using 1
        ring
      have : ϖ ^ (i + j) = 0 :=
        (IsUnit.mul_right_eq_zero (IsUnit.mul u.isUnit v.isUnit)).mp hprod
      exact absurd this (hpow _)
    exact NoZeroDivisors.to_isDomain R

/-- Brick P2.2 interface name, currently for `ringKrullDim ≤ 1`.

See module docstring: dim ≤ 2 / general cases need the associated-graded isomorphism.
@isnad1 id=isdomain.1h1v.s5.4b4b49d3084d from=translated src=- shape=50208249 vocab=37ff1a7f
-/
theorem isDomain [IsRegularLocalRing R] (hdim : ringKrullDim R ≤ 1) : IsDomain R :=
  isDomain_of_ringKrullDim_le_one hdim

end IsRegularLocalRing
