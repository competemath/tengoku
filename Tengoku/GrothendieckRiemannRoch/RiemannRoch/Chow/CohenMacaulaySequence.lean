/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.CohenMacaulay
import Tengoku.Seed.RingTheory.Filtration
import Tengoku.Seed.RingTheory.Ideal.AssociatedPrime.Basic
import Tengoku.Seed.RingTheory.Ideal.AssociatedPrime.Localization
import Tengoku.Seed.RingTheory.Ideal.MinimalPrime.Basic
import Tengoku.Seed.RingTheory.KrullDimension.Regular
import Tengoku.Seed.RingTheory.KrullDimension.NonZeroDivisors
import Tengoku.Seed.RingTheory.Nakayama
import Tengoku.Seed.RingTheory.Ideal.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Systems of parameters are weakly regular in CM local rings (P3.3)

In a Cohen--Macaulay Noetherian local ring, a list that drops Krull dimension by exactly its
length is a weakly regular sequence.  Induction on the list uses P3.2; the regular-element step
uses `depth ≤ dim(R⧸p)` for associated primes (Stacks `0BK4`).
-/

noncomputable section

universe u

open CategoryTheory Abelian RingTheory.Sequence IsLocalRing Ideal Pointwise

variable {R : Type u} [CommRing R] [IsLocalRing R]

namespace ModuleCat

/-! ### List dimension arithmetic -/

theorem mem_maximalIdeal_of_ringKrullDim_add_length_eq [IsNoetherianRing R]
    (rs : List R)
    (hdim : ringKrullDim (R ⧸ Ideal.ofList rs) + rs.length = ringKrullDim R)
    {r : R} (hr : r ∈ rs) : r ∈ maximalIdeal R := by
  by_contra hrm
  have hunit : IsUnit r := notMem_maximalIdeal.mp hrm
  have htop : Ideal.ofList rs = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span hr) hunit
  have hbot : ringKrullDim (R ⧸ Ideal.ofList rs) = ⊥ := by
    rw [htop]; exact ringKrullDim_eq_bot_of_subsingleton
  have hne : ringKrullDim R ≠ ⊥ :=
    (lt_of_lt_of_le (WithBot.bot_lt_coe 0) ringKrullDim_nonneg_of_nontrivial).ne'
  exact hne (by simpa [hbot] using hdim.symm)

theorem ringKrullDim_le_ringKrullDim_ofList_add_length
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (rs : List R) (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.ofList rs) + rs.length := by
  induction hn : rs.length generalizing R rs with
  | zero =>
    have hrs : rs = [] := List.eq_nil_of_length_eq_zero hn
    subst hrs
    rw [Ideal.ofList_nil, Nat.cast_zero, add_zero,
      ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R)]
  | succ n ih =>
    match rs with
    | [] => cases hn
    | r :: rs =>
      have hrm : r ∈ maximalIdeal R := hmem r (by simp)
      have hmem' : ∀ a ∈ rs, a ∈ maximalIdeal R := fun a ha ↦ hmem a (by simp [ha])
      have hspan : (r • (⊤ : Ideal R)) = Ideal.span {r} := by
        ext y
        simp [Ideal.mem_span_singleton, Submodule.mem_smul_pointwise_iff_exists, eq_comm,
          dvd_iff_exists_eq_mul_right]
      have h1 : ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {r}) + 1 := by
        rw [← hspan]
        exact ringKrullDim_le_ringKrullDim_quotSMulTop_succ hrm
      let Q := R ⧸ Ideal.span {r}
      letI : IsLocalRing Q := quotientSpanIsLocalRing R r hrm
      letI : IsNoetherianRing Q := Ideal.Quotient.isNoetherianRing _
      letI : IsLocalHom (Ideal.Quotient.mk (Ideal.span {r})) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      let rsQ : List Q := rs.map (Ideal.Quotient.mk (Ideal.span {r}))
      have hmemQ : ∀ q ∈ rsQ, q ∈ maximalIdeal Q := by
        intro q hq
        rcases List.mem_map.mp hq with ⟨a, ha, rfl⟩
        exact map_nonunit _ a (hmem' a ha)
      have hlen : rsQ.length = n := by
        simp only [rsQ, List.length_map]
        simpa [List.length_cons] using hn
      have h2 :
          ringKrullDim Q ≤ ringKrullDim (Q ⧸ Ideal.ofList rsQ) + rsQ.length := by
        simpa [hlen] using ih (R := Q) rsQ hmemQ hlen
      have hrsQ :
          Ideal.ofList rsQ =
            Ideal.map (Ideal.Quotient.mk (Ideal.span {r})) (Ideal.ofList rs) := by
        dsimp [rsQ]
        exact (Ideal.map_ofList (Ideal.Quotient.mk (Ideal.span {r})) rs).symm
      have e : Q ⧸ Ideal.ofList rsQ ≃+* R ⧸ Ideal.ofList (r :: rs) := by
        refine (Ideal.quotEquivOfEq hrsQ).trans ?_
        refine (DoubleQuot.quotQuotEquivQuotSup (Ideal.span {r}) (Ideal.ofList rs)).trans ?_
        exact Ideal.quotEquivOfEq (by simp [Ideal.ofList_cons, sup_comm])
      have h2' :
          ringKrullDim (R ⧸ Ideal.span {r}) ≤
            ringKrullDim (R ⧸ Ideal.ofList (r :: rs)) + rs.length := by
        simpa [ringKrullDim_eq_of_ringEquiv e.symm, List.length_map, Q, rsQ] using h2
      have hrs_len : rs.length = n := Nat.succ_injective (by simpa [List.length_cons] using hn)
      refine le_trans h1 ?_
      have h2'' :
          ringKrullDim (R ⧸ Ideal.span {r}) + 1 ≤
            ringKrullDim (R ⧸ Ideal.ofList (r :: rs)) + ↑(n + 1) := by
        simpa [hrs_len, Nat.cast_succ, add_comm, add_left_comm, add_assoc] using
          add_le_add_right h2' 1
      exact h2''

theorem ringKrullDim_quotient_span_singleton_add_one_of_ofList_cons [IsNoetherianRing R]
    (r : R) (rs : List R)
    (hdim : ringKrullDim (R ⧸ Ideal.ofList (r :: rs)) + (rs.length + 1) = ringKrullDim R) :
    r ∈ maximalIdeal R ∧
      ringKrullDim (R ⧸ Ideal.span {r}) + 1 = ringKrullDim R ∧
      ringKrullDim (R ⧸ Ideal.ofList (r :: rs)) + rs.length =
        ringKrullDim (R ⧸ Ideal.span {r}) := by
  have hmem_all : ∀ a ∈ r :: rs, a ∈ maximalIdeal R := fun a ha ↦
    mem_maximalIdeal_of_ringKrullDim_add_length_eq (r :: rs) (by simpa using hdim) ha
  have hrm : r ∈ maximalIdeal R := hmem_all r (by simp)
  have hmem_tail : ∀ a ∈ rs, a ∈ maximalIdeal R := fun a ha ↦ hmem_all a (by simp [ha])
  have hspan : (r • (⊤ : Ideal R)) = Ideal.span {r} := by
    ext y
    simp [Ideal.mem_span_singleton, Submodule.mem_smul_pointwise_iff_exists, eq_comm,
      dvd_iff_exists_eq_mul_right]
  have hle₁ : ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {r}) + 1 := by
    rw [← hspan]
    exact ringKrullDim_le_ringKrullDim_quotSMulTop_succ hrm
  let Q := R ⧸ Ideal.span {r}
  letI : IsLocalRing Q := quotientSpanIsLocalRing R r hrm
  letI : IsNoetherianRing Q := Ideal.Quotient.isNoetherianRing _
  letI : IsLocalHom (Ideal.Quotient.mk (Ideal.span {r})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let rsQ : List Q := rs.map (Ideal.Quotient.mk (Ideal.span {r}))
  have hmemQ : ∀ q ∈ rsQ, q ∈ maximalIdeal Q := by
    intro q hq
    rcases List.mem_map.mp hq with ⟨a, ha, rfl⟩
    exact map_nonunit _ a (hmem_tail a ha)
  have hle₂ :
      ringKrullDim (R ⧸ Ideal.span {r}) ≤
        ringKrullDim (R ⧸ Ideal.ofList (r :: rs)) + rs.length := by
    have h := ringKrullDim_le_ringKrullDim_ofList_add_length (R := Q) rsQ hmemQ
    have hrsQ :
        Ideal.ofList rsQ =
          Ideal.map (Ideal.Quotient.mk (Ideal.span {r})) (Ideal.ofList rs) := by
      dsimp [rsQ]
      exact (Ideal.map_ofList (Ideal.Quotient.mk (Ideal.span {r})) rs).symm
    have e : Q ⧸ Ideal.ofList rsQ ≃+* R ⧸ Ideal.ofList (r :: rs) := by
      refine (Ideal.quotEquivOfEq hrsQ).trans ?_
      refine (DoubleQuot.quotQuotEquivQuotSup (Ideal.span {r}) (Ideal.ofList rs)).trans ?_
      exact Ideal.quotEquivOfEq (by simp [Ideal.ofList_cons, sup_comm])
    simpa [ringKrullDim_eq_of_ringEquiv e.symm, List.length_map, Q, rsQ] using h
  have hdrop : ringKrullDim (R ⧸ Ideal.span {r}) + 1 = ringKrullDim R := by
    apply le_antisymm
    · calc
        ringKrullDim (R ⧸ Ideal.span {r}) + 1
            ≤ ringKrullDim (R ⧸ Ideal.ofList (r :: rs)) + rs.length + 1 := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hle₂ 1
        _ = ringKrullDim R := by rw [← hdim, add_assoc, add_comm (rs.length : WithBot ℕ∞)]
    · exact hle₁
  have hsum :
      ringKrullDim (R ⧸ Ideal.ofList (r :: rs)) + rs.length + 1 =
        ringKrullDim (R ⧸ Ideal.span {r}) + 1 := by
    have h1 : ringKrullDim (R ⧸ Ideal.ofList (r :: rs)) + rs.length + 1 = ringKrullDim R := by
      rw [← hdim, add_assoc, add_comm (rs.length : WithBot ℕ∞)]
    rw [h1, hdrop]
  have heq : ringKrullDim (R ⧸ Ideal.ofList (r :: rs)) + rs.length =
      ringKrullDim (R ⧸ Ideal.span {r}) :=
    (ENat.WithBot.add_one_cancel).mp hsum
  exact ⟨hrm, hdrop, heq⟩

/-! ### Depth drop by a regular element -/

theorem ringDepth_eq_of_quotIdeal_eq [IsNoetherianRing R]
    {I J : Ideal R} [IsLocalRing (R ⧸ I)] [IsLocalRing (R ⧸ J)] (hIJ : I = J) :
    ringDepth (R ⧸ I) = ringDepth (R ⧸ J) := by
  subst hIJ
  rfl

/-! ### Associated-prime depth bound (Stacks 0BK4) -/

/-- Powers of regular elements remain regular.-/
theorem isSMulRegular_pow {x : R} (hx : IsSMulRegular R x) :
    ∀ n : ℕ, IsSMulRegular R (x ^ n)
  | 0 => IsSMulRegular.of_right_eq_zero_of_smul fun a ha => by simpa using ha
  | n + 1 => by
    refine IsSMulRegular.of_right_eq_zero_of_smul fun a ha => ?_
    have hx' : x • (x ^ n • a) = 0 := by
      simpa [pow_succ', smul_eq_mul, mul_assoc] using ha
    exact (isSMulRegular_pow hx n).right_eq_zero_of_smul (hx.right_eq_zero_of_smul hx')

/-- Transfer Ass from the `R`-module `R/I` to the ring `R/I`.-/
theorem associatedPrimes_map_quotient_mk [IsNoetherianRing R]
    {I q : Ideal R} (hle : I ≤ q)
    (hq : q ∈ associatedPrimes R (R ⧸ I)) :
    q.map (Ideal.Quotient.mk I) ∈ associatedPrimes (R ⧸ I) (R ⧸ I) := by
  haveI : q.IsPrime := (AssociatedPrimes.mem_iff.mp hq).isPrime
  haveI : (q.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hle
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hq ⊢
  obtain ⟨_hqPrime, x, hqcolon⟩ := hq
  refine ⟨inferInstance, x, SetLike.ext fun a => ?_⟩
  have hcolon {b : R} : b ∈ q ↔ (Ideal.Quotient.mk I) b • x = 0 := by
    constructor
    · intro hb
      have hb' := Submodule.mem_colon_singleton.mp (hqcolon ▸ hb)
      simpa [Submodule.mem_bot, Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using hb'
    · intro hb
      exact hqcolon ▸ Submodule.mem_colon_singleton.mpr (by
        simpa [Submodule.mem_bot, Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using hb)
  constructor
  · intro ha
    obtain ⟨b, hb, hab⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp ha
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    rw [← hab, hcolon.mp hb]
  · intro ha
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at ha
    refine (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).2 ?_
    refine ⟨Quotient.out a, hcolon.mpr ?_, Ideal.Quotient.mk_out a⟩
    rw [Ideal.Quotient.mk_out]
    exact ha

/-- Local ring structure on `R ⧸ (x)ⁿ` for `x ∈ m` and `n > 0`.-/
@[reducible]
def quotientPowSpanIsLocalRing (x : R) (n : ℕ) (hx : x ∈ maximalIdeal R) (hn : 0 < n) :
    IsLocalRing (R ⧸ (Ideal.span {x} ^ n : Ideal R)) := by
  letI : Nontrivial (R ⧸ (Ideal.span {x} ^ n : Ideal R)) :=
    Ideal.Quotient.nontrivial_iff.mpr fun htop => by
      have hle : Ideal.span {x} ^ n ≤ maximalIdeal R :=
        (Ideal.pow_le_self hn.ne').trans (Ideal.span_le.mpr (by simpa using hx))
      exact (hle.trans_lt (maximalIdeal.isMaximal R).lt_top).ne htop
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- Stacks `0CN5`.-/
theorem exists_mem_associatedPrimes_quotient_pow_of_mem_minimalPrimes_sup [IsNoetherianRing R]
    {p : Ideal R} (hp : p ∈ associatedPrimes R R) (x : R)
    {q : Ideal R} (hq : q ∈ (p ⊔ Ideal.span {x}).minimalPrimes) :
    ∃ n > 0, q ∈ associatedPrimes R (R ⧸ (Ideal.span {x} ^ n : Ideal R)) := by
  classical
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff_exists_injective_linearMap] at hp
  obtain ⟨_, ⟨f, hf⟩⟩ := hp
  let N : Submodule R R := LinearMap.range f
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (Ideal.span {x}) N
  set n := k + 1
  have hnpos : 0 < n := Nat.succ_pos _
  have hAR : (Ideal.span {x} ^ n : Ideal R) • (⊤ : Submodule R R) ⊓ N ≤ Ideal.span {x} • N := by
    have h := hk n (Nat.le_succ _)
    have hk' : n - k = 1 := by
      dsimp [n]
      omega
    calc
      (Ideal.span {x} ^ n : Ideal R) • (⊤ : Submodule R R) ⊓ N
          = (Ideal.span {x} ^ (n - k)) • ((Ideal.span {x} ^ k : Ideal R) • (⊤ : Submodule R R) ⊓ N) := h
      _ = Ideal.span {x} • ((Ideal.span {x} ^ k : Ideal R) • (⊤ : Submodule R R) ⊓ N) := by
          rw [Ideal.span_singleton_pow x (n - k), hk', pow_one]
      _ ≤ Ideal.span {x} • N := by
          gcongr
          exact inf_le_right
  let I : Ideal R := Ideal.span {x} ^ n
  let Nbar : Submodule R (R ⧸ I) := N.map (Submodule.mkQ I)
  have hp_le_ann : p ≤ Module.annihilator R Nbar := by
    intro b hb
    refine Module.mem_annihilator.mpr fun y => ?_
    obtain ⟨z, hz, heq⟩ := Submodule.mem_map.mp y.property
    obtain ⟨t, ht, hft⟩ := LinearMap.mem_range.mp hz
    have hbt : b • t = 0 := by
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hb]
      exact zero_mul t
    have hb0 : b • f t = 0 := by rw [← f.map_smul, hbt, map_zero]
    apply Subtype.ext
    show b • (y : R ⧸ I) = 0
    calc b • (y : R ⧸ I)
        = b • (Submodule.mkQ I) (f t) := by rw [← heq]
      _ = (Submodule.mkQ I) (b • f t) := (Submodule.Quotient.mk_smul I b (f t)).symm
      _ = 0 := by rw [hb0, map_zero]
  have hx_rad : x ∈ (Module.annihilator R Nbar).radical :=
    Ideal.mem_radical_iff.mpr ⟨n, Module.mem_annihilator.mpr fun y => by
      obtain ⟨z, hz, heq⟩ := Submodule.mem_map.mp y.property
      obtain ⟨t, ht, hft⟩ := LinearMap.mem_range.mp hz
      have hxI : x ^ n ∈ I := by
        simpa [I] using Ideal.pow_mem_pow (Ideal.mem_span_singleton_self x) n
      apply Subtype.ext
      show (x ^ n) • (y : R ⧸ I) = 0
      calc (x ^ n) • (y : R ⧸ I)
          = (x ^ n) • (Submodule.mkQ I) (f t) := by rw [← heq]
        _ = (Submodule.mkQ I) ((x ^ n) • f t) := (Submodule.Quotient.mk_smul I (x ^ n) (f t)).symm
        _ = (Submodule.mkQ I) (x ^ n * f t) := by simp [Algebra.smul_def]
        _ = 0 := (Submodule.Quotient.mk_eq_zero I).mpr (Ideal.mul_mem_right _ _ hxI)⟩
  have hsup_rad : p ⊔ Ideal.span {x} ≤ (Module.annihilator R Nbar).radical :=
    sup_le (hp_le_ann.trans Ideal.le_radical)
      (Ideal.span_le.mpr (by simpa using hx_rad))
  have hAnn_le_sup : Module.annihilator R Nbar ≤ p ⊔ Ideal.span {x} := by
    intro a ha
    have hf1mem : Ideal.Quotient.mk I (f 1) ∈ Nbar :=
      Submodule.mem_map.mpr ⟨f 1, LinearMap.mem_range_self f 1, rfl⟩
    have hzero : a • (⟨Ideal.Quotient.mk I (f 1), hf1mem⟩ : ↥Nbar) = 0 :=
      Module.mem_annihilator.mp ha ⟨Ideal.Quotient.mk I (f 1), hf1mem⟩
    have hzero' : Ideal.Quotient.mk I (a * f 1) = 0 := by
      rw [(Ideal.Quotient.mk I).map_mul a (f 1), ← Ideal.Quotient.algebraMap_eq, ← Algebra.smul_def]
      exact Subtype.ext_iff.mp hzero
    have haf : a • f 1 ∈ I := (Submodule.Quotient.mk_eq_zero I).mp hzero'
    have hfa : f (Ideal.Quotient.mk p a) = a • f 1 := by
      rw [← f.map_smul a (1 : R ⧸ p)]
      congr 1
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one]
    have haf' : f (Ideal.Quotient.mk p a) ∈ I := hfa ▸ haf
    have hxN : f (Ideal.Quotient.mk p a) ∈ x • N := by
      have hmem_top : f (Ideal.Quotient.mk p a) ∈ I • (⊤ : Submodule R R) := by
        rw [← mul_one (f (Ideal.Quotient.mk p a)), ← smul_eq_mul]
        exact Submodule.smul_mem_smul haf' Submodule.mem_top
      have := hAR ⟨hmem_top, LinearMap.mem_range_self f (Ideal.Quotient.mk p a)⟩
      rwa [Submodule.ideal_span_singleton_smul] at this
    obtain ⟨y, hy, heq⟩ := (Submodule.mem_smul_pointwise_iff_exists _ x N).mp hxN
    obtain ⟨t, ht, hft⟩ := LinearMap.mem_range.mp hy
    have heq' : Ideal.Quotient.mk p a = x • t := by
      apply hf
      rw [map_smul]
      exact heq.symm
    have : Ideal.Quotient.mk p a =
        Ideal.Quotient.mk p (x * Quotient.out t) := by
      rw [heq', (Ideal.Quotient.mk p).map_mul x (Quotient.out t), Ideal.Quotient.mk_out t,
        Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
    have hmem : a - x * Quotient.out t ∈ p :=
      Ideal.Quotient.eq_zero_iff_mem.mp (by simp [this])
    have hxterm : x * Quotient.out t ∈ Ideal.span {x} :=
      Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self x)
    rw [show a = a - x * Quotient.out t + x * Quotient.out t from by ring]
    exact Submodule.add_mem_sup hmem hxterm
  have hAnn_le_q : Module.annihilator R Nbar ≤ q := hAnn_le_sup.trans hq.1.2
  haveI : Module.Finite R (R ⧸ p) := inferInstance
  haveI : Module.Finite R N := Module.Finite.range f
  haveI : Module.Finite R Nbar := inferInstance
  have hq_min : q ∈ (Module.annihilator R Nbar).minimalPrimes := by
    have hsup_le_of_ann {r : Ideal R} [hr : r.IsPrime]
        (hran : Module.annihilator R Nbar ≤ r) : p ⊔ Ideal.span {x} ≤ r :=
      hsup_rad.trans (Ideal.radical_mono hran) |>.trans (IsPrime.radical hr).le
    refine ⟨⟨hq.1.1, hAnn_le_q⟩, ?_⟩
    intro r ⟨hrPrime, hran⟩ hrle
    exact hq.2 ⟨hrPrime, hsup_le_of_ann hran⟩ hrle
  exact ⟨n, hnpos,
    associatedPrimes.subset_of_injective Nbar.injective_subtype
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
        (R := R) (M := Nbar) hq_min)⟩

/-! ### Main theorem -/

end ModuleCat
