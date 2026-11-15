import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicLevel
import Tengoku.Seed.NumberTheory.Padics.HeightOneSpectrum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open Rat.HeightOneSpectrum NumberField.AdelicLevel

namespace RatIdele

local notation "𝔸ℚ" => AdeleRing (𝓞 ℚ) ℚ
local notation "𝔸ℚf" => FiniteAdeleRing (𝓞 ℚ) ℚ

section Primes

/--
@isnad1 id=iff.0h2v.s7.8afe216250f4 from=translated src=- shape=a59a80cb vocab=46c37ad9
-/
theorem natCast_mem_asIdeal_iff (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    ((n : 𝓞 ℚ)) ∈ v.asIdeal ↔ natGenerator v ∣ n := by
  rw [natGenerator_dvd_iff,
    show ((n : ℕ) : ℤ) = Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) ((n : 𝓞 ℚ)) from (map_natCast _ n).symm]
  exact Ideal.apply_mem_of_equiv_iff.symm

/--
@isnad1 id=ne.0h1v.s6.e65dcaca703f from=translated src=- shape=de50522d vocab=dc33fc48
-/
theorem natCast_natGenerator_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) : ((natGenerator v : ℕ) : 𝓞 ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (prime_natGenerator v).ne_zero

/--
@isnad1 id=prime.0h1v.s5.d6f256df5198 from=translated src=- shape=826bd511 vocab=c8766760
-/
theorem prime_natCast_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) : Prime ((natGenerator v : ℕ) : 𝓞 ℚ) := by
  have hcast : ((natGenerator v : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((natGenerator v : ℕ) : ℤ) :=
    (map_natCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm
  rw [hcast]
  exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr
    (Nat.prime_iff_prime_int.mp (prime_natGenerator v))

/--
@isnad1 id=eq.0h1v.s6.c0fcddd3186d from=translated src=- shape=a116be91 vocab=318c37c5
-/
theorem asIdeal_eq_span_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal = Ideal.span {((natGenerator v : ℕ) : 𝓞 ℚ)} := by
  have hmax : (Ideal.span {((natGenerator v : ℕ) : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (natCast_natGenerator_ne_zero v)).mpr
      (prime_natCast_natGenerator v)).isMaximal
      ((Ideal.span_singleton_eq_bot (α := 𝓞 ℚ)).not.mpr (natCast_natGenerator_ne_zero v))
  exact (hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr
    ((natCast_mem_asIdeal_iff v _).mpr dvd_rfl))).symm

/--
@isnad1 id=eq.0h1v.s6.3550a748cb05 from=translated src=- shape=1bf911a7 vocab=fcd1867e
-/
theorem valuation_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.valuation ℚ ((natGenerator v : ℕ) : ℚ) = exp (-1 : ℤ) := by
  rw [show ((natGenerator v : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((natGenerator v : ℕ) : 𝓞 ℚ) from
      (map_natCast (algebraMap (𝓞 ℚ) ℚ) _).symm, valuation_of_algebraMap]
  exact intValuation_singleton v (natCast_natGenerator_ne_zero v) (asIdeal_eq_span_natGenerator v)

/--
@isnad1 id=eq.1h2v.s6.4f9eecc92564 from=translated src=- shape=b277c16b vocab=8a2ae954
-/
theorem valuation_natCast_of_not_dvd (v : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (h : ¬ natGenerator v ∣ n) :
    v.valuation ℚ ((n : ℕ) : ℚ) = 1 := by
  rw [show ((n : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((n : ℕ) : 𝓞 ℚ) from (map_natCast (algebraMap (𝓞 ℚ) ℚ) _).symm,
    valuation_of_algebraMap]
  exact intValuation_eq_one_iff.mpr fun hmem => h ((natCast_mem_asIdeal_iff v n).mp hmem)

theorem eq_of_natGenerator_eq {v w : HeightOneSpectrum (𝓞 ℚ)} (h : natGenerator v = natGenerator w) : v = w :=
  (primesEquiv (R := 𝓞 ℚ)).injective (Subtype.ext h)

/--
@isnad1 id=eq.1h2v.s6.8f4fd8d0b532 from=translated src=- shape=74a40b47 vocab=5b192f58
-/
theorem valuation_natGenerator_of_ne {v w : HeightOneSpectrum (𝓞 ℚ)} (h : v ≠ w) :
    w.valuation ℚ ((natGenerator v : ℕ) : ℚ) = 1 :=
  valuation_natCast_of_not_dvd w fun hd =>
    h (eq_of_natGenerator_eq
      ((Nat.prime_dvd_prime_iff_eq (prime_natGenerator w) (prime_natGenerator v)).mp hd)).symm

/--
@isnad1 id=eq.0h1v.s6.b893d0dd1948 from=translated src=- shape=cf632ecf vocab=f08705af
-/
theorem natGenerator_primesEquiv_symm (p : Nat.Primes) :
    natGenerator ((primesEquiv (R := 𝓞 ℚ)).symm p) = (p : ℕ) :=
  congrArg Subtype.val ((primesEquiv (R := 𝓞 ℚ)).apply_symm_apply p)

/--
@isnad1 id=eq.0h2v.s9.855ecbd84dfd from=translated src=- shape=99a5a5bc vocab=bebd3a09
-/
theorem valued_algebraMap_rat (v : HeightOneSpectrum (𝓞 ℚ)) (q : ℚ) :
    Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) = v.valuation ℚ q := by
  rw [algebraMap_adicCompletion]
  exact valuedAdicCompletion_eq_valuation' v q

/--
@isnad1 id=eq.0h2v.s9.6ed21c69e074 from=translated src=- shape=03033abb vocab=4f112a9e
-/
theorem algebraMap_adeleRing_snd (q : ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (algebraMap ℚ 𝔸ℚ q).2 v = algebraMap ℚ (v.adicCompletion ℚ) q := by
  rw [AdeleRing.algebraMap_snd_apply, algebraMap_adicCompletion]
  rfl

/--
@isnad1 id=ne.1h2v.s8.d66d87808d88 from=translated src=- shape=95a02e7f vocab=98e1e8f5
-/
theorem natCast_adicCompletion_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (hn : n ≠ 0) :
    ((n : ℕ) : v.adicCompletion ℚ) ≠ 0 := by
  rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)) n]
  exact (map_ne_zero (algebraMap ℚ (v.adicCompletion ℚ))).mpr (Nat.cast_ne_zero.mpr hn)

end Primes

section Arch

def archCoord (x : (𝔸ℚ)ˣ) : ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace ((x : 𝔸ℚ).1 Rat.infinitePlace)

/--
@isnad1 id=eq.0h2v.s9.88a58defac46 from=translated src=- shape=346d5861 vocab=add83303
-/
theorem archCoord_mul (x y : (𝔸ℚ)ˣ) : archCoord (x * y) = archCoord x * archCoord y := by
  unfold archCoord
  rw [← map_mul]
  rfl

/--
@isnad1 id=eq.0h0v.s7.0aeeb68b4190 from=translated src=- shape=84b43f05 vocab=bb0d967a
-/
theorem archCoord_one : archCoord 1 = 1 := by
  unfold archCoord
  rw [show ((1 : (𝔸ℚ)ˣ) : 𝔸ℚ).1 Rat.infinitePlace = 1 from rfl, map_one]

/--
@isnad1 id=ne.0h1v.s6.3dcafc11147c from=translated src=- shape=f1d237fb vocab=bb0d967a
-/
theorem archCoord_ne_zero (x : (𝔸ℚ)ˣ) : archCoord x ≠ 0 := by
  intro h
  have h1 := archCoord_mul x x⁻¹
  rw [mul_inv_cancel, archCoord_one, h, zero_mul] at h1
  exact one_ne_zero h1

/--
@isnad1 id=eq.0h1v.s9.b4ff0b898b5f from=translated src=- shape=662c9426 vocab=78227b51
-/
theorem archCoord_principal (q : ℚˣ) :
    archCoord (Units.map (algebraMap ℚ 𝔸ℚ : ℚ →* 𝔸ℚ) q) = ((q : ℚ) : ℝ) :=
  eq_ratCast ((InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace :
      Rat.infinitePlace.Completion ≃+* ℝ).toRingHom.comp
    ((Pi.evalRingHom (fun w : InfinitePlace ℚ => w.Completion) Rat.infinitePlace).comp
      ((RingHom.fst _ _).comp (algebraMap ℚ 𝔸ℚ)))) (q : ℚ)

/--
@isnad1 id=eq.0h1v.s10.3ea17ac29d51 from=translated src=- shape=6ff3602f vocab=6bb33cfe
-/
theorem archCoord_finIncl (y : (𝔸ℚf)ˣ) : archCoord (Units.map (finIncl (𝓞 ℚ) ℚ) y) = 1 := by
  unfold archCoord
  rw [Units.coe_map, finIncl_apply_fst, show (1 : InfiniteAdeleRing ℚ) Rat.infinitePlace = 1 from rfl, map_one]

end Arch

section Order

def finPart : (𝔸ℚ)ˣ →* (𝔸ℚf)ˣ := Units.map (RingHom.snd (InfiniteAdeleRing ℚ) 𝔸ℚf).toMonoidHom

/--
@isnad1 id=eq.0h2v.s10.8b738098a649 from=translated src=- shape=2d2e37b8 vocab=f35beab0
-/
theorem finPart_apply (x : (𝔸ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((finPart x : (𝔸ℚf)ˣ) : 𝔸ℚf) v = (x : 𝔸ℚ).2 v := rfl

/--
@isnad1 id=eq.0h3v.s10.9d0594b5c9a5 from=translated src=- shape=590489bd vocab=df774731
-/
theorem valued_snd_mul (x y : (𝔸ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((((x * y : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v) = Valued.v ((x : 𝔸ℚ).2 v) * Valued.v ((y : 𝔸ℚ).2 v) := by
  rw [← map_mul]
  rfl

/--
@isnad1 id=ne.0h2v.s8.71a86d7162e3 from=translated src=- shape=66faee68 vocab=c89739d5
-/
theorem valued_snd_ne_zero (x : (𝔸ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) : Valued.v ((x : 𝔸ℚ).2 v) ≠ 0 := by
  rw [ne_eq, map_eq_zero]
  intro h
  have h1 : (((x * x⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v = 1 := by
    rw [mul_inv_cancel]
    rfl
  rw [show (((x * x⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v = (x : 𝔸ℚ).2 v * (((x⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v from rfl, h,
    zero_mul] at h1
  exact zero_ne_one h1

/--
@isnad1 id=eq.0h2v.s10.8891112fc9d9 from=translated src=- shape=8bd0073e vocab=5b10748e
-/
theorem valued_snd_inv_mul (x : (𝔸ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((((x⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v) * Valued.v ((x : 𝔸ℚ).2 v) = 1 := by
  rw [← valued_snd_mul, inv_mul_cancel]
  show Valued.v ((1 : 𝔸ℚf) v) = 1
  rw [show ((1 : 𝔸ℚf)) v = 1 from rfl, map_one]

def ordAt (v : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℚ)ˣ) : ℤ := -log (Valued.v ((x : 𝔸ℚ).2 v))

/--
@isnad1 id=eq.0h2v.s8.dae8339e8053 from=translated src=- shape=4e190086 vocab=f73a0054
-/
theorem valued_snd_eq (v : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℚ)ˣ) :
    Valued.v ((x : 𝔸ℚ).2 v) = exp (-ordAt v x) := by
  rw [ordAt, neg_neg, exp_log (valued_snd_ne_zero x v)]

/--
@isnad1 id=eq.0h3v.s9.9b7b509304d9 from=translated src=- shape=e492c751 vocab=22385aaa
-/
theorem ordAt_mul (v : HeightOneSpectrum (𝓞 ℚ)) (x y : (𝔸ℚ)ˣ) : ordAt v (x * y) = ordAt v x + ordAt v y := by
  unfold ordAt
  rw [valued_snd_mul, log_mul (valued_snd_ne_zero x v) (valued_snd_ne_zero y v), neg_add]

/--
@isnad1 id=eq.0h1v.s7.8cfb7dadc57c from=translated src=- shape=c22d3a25 vocab=38f11100
-/
theorem ordAt_one (v : HeightOneSpectrum (𝓞 ℚ)) : ordAt v 1 = 0 := by
  unfold ordAt
  rw [show ((1 : (𝔸ℚ)ˣ) : 𝔸ℚ).2 v = 1 from rfl, map_one, log_one, neg_zero]

/--
@isnad1 id=eq.2h2v.s10.e39db9a23525 from=translated src=- shape=58702e60 vocab=18861628
-/
theorem ordAt_eq_zero_of_le_one {v : HeightOneSpectrum (𝓞 ℚ)} {x : (𝔸ℚ)ˣ} (hx : Valued.v ((x : 𝔸ℚ).2 v) ≤ 1)
    (hxi : Valued.v ((((x⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v) ≤ 1) : ordAt v x = 0 := by
  have hmul := valued_snd_inv_mul x v
  have h1 : Valued.v ((x : 𝔸ℚ).2 v) = 1 := le_antisymm hx (by
    calc (1 : ℤᵐ⁰) = Valued.v ((((x⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v) * Valued.v ((x : 𝔸ℚ).2 v) := hmul.symm
      _ ≤ 1 * Valued.v ((x : 𝔸ℚ).2 v) := mul_le_mul_left hxi _
      _ = Valued.v ((x : 𝔸ℚ).2 v) := one_mul _)
  unfold ordAt
  rw [h1, log_one, neg_zero]

/--
@isnad1 id=finite.0h1v.s6.cbafbdfab57e from=translated src=- shape=5c7162b5 vocab=ae085852
-/
theorem finite_setOf_ordAt_ne_zero (x : (𝔸ℚ)ˣ) : {v : HeightOneSpectrum (𝓞 ℚ) | ordAt v x ≠ 0}.Finite := by
  have hx : ∀ᶠ v in Filter.cofinite, ((x : 𝔸ℚ).2 : 𝔸ℚf) v ∈ v.adicCompletionIntegers ℚ := ((x : 𝔸ℚ).2).2
  have hxi : ∀ᶠ v in Filter.cofinite, ((((x⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 : 𝔸ℚf) v ∈ v.adicCompletionIntegers ℚ :=
    ((((x⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2).2
  have hboth := hx.and hxi
  rw [Filter.eventually_cofinite] at hboth
  refine hboth.subset ?_
  intro v hv
  simp only [Set.mem_ofPred_eq] at hv ⊢
  intro hcon
  exact hv (ordAt_eq_zero_of_le_one ((mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp hcon.1)
    ((mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp hcon.2))

end Order

section Normalizer

def IsNormalizer (x : (𝔸ℚ)ˣ) (r : ℚ) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((x : 𝔸ℚ).2 v) = v.valuation ℚ r) ∧ 0 < archCoord x * (r : ℝ)

/--
@isnad1 id=ne.1h2v.s6.64f142b6b46f from=translated src=- shape=42d714f1 vocab=283a3085
-/
theorem IsNormalizer.ne_zero {x : (𝔸ℚ)ˣ} {r : ℚ} (h : IsNormalizer x r) : r ≠ 0 := by
  rintro rfl
  have := h.2
  rw [Rat.cast_zero, mul_zero] at this
  exact lt_irrefl _ this

def archSign (x : (𝔸ℚ)ˣ) : ℚ := if 0 < archCoord x then 1 else -1

/--
@isnad1 id=lt.0h1v.s6.b8f215e23e92 from=translated src=- shape=96710a95 vocab=183260e2
-/
theorem archCoord_mul_archSign_pos (x : (𝔸ℚ)ˣ) : 0 < archCoord x * (archSign x : ℝ) := by
  unfold archSign
  split_ifs with h
  · rw [Rat.cast_one, mul_one]
    exact h
  · rw [Rat.cast_neg, Rat.cast_one, mul_neg, mul_one]
    exact neg_pos.mpr (lt_of_le_of_ne (not_lt.mp h) (archCoord_ne_zero x))

/--
@isnad1 id=eq.0h2v.s7.9cd510803017 from=translated src=- shape=e9998ad1 vocab=98d28b05
-/
theorem valuation_archSign (w : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℚ)ˣ) : w.valuation ℚ (archSign x) = 1 := by
  unfold archSign
  split_ifs
  · exact map_one _
  · rw [Valuation.map_neg, map_one]

def ρ (x : (𝔸ℚ)ˣ) : ℚ :=
  archSign x * ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), ((natGenerator v : ℕ) : ℚ) ^ ordAt v x

/--
@isnad1 id=le.0h1v.s7.85a3f825a5f3 from=translated src=- shape=48f6baf7 vocab=d10a84cf
-/
theorem mulSupport_subset_toFinset (x : (𝔸ℚ)ˣ) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 ℚ) => ((natGenerator v : ℕ) : ℚ) ^ ordAt v x)
      ⊆ ((finite_setOf_ordAt_ne_zero x).toFinset : Set (HeightOneSpectrum (𝓞 ℚ))) := by
  intro v hv
  rw [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
  intro h0
  rw [Function.mem_mulSupport, h0, zpow_zero] at hv
  exact hv rfl

/--
@isnad1 id=lt.0h1v.s6.eb7f352dc1e9 from=translated src=- shape=50b08d17 vocab=0548e987
-/
theorem finprod_pow_ordAt_pos (x : (𝔸ℚ)ˣ) :
    (0 : ℚ) < ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), ((natGenerator v : ℕ) : ℚ) ^ ordAt v x :=
  finprod_induction (fun r : ℚ => 0 < r) one_pos (fun _ _ => mul_pos)
    fun v => zpow_pos (Nat.cast_pos.mpr (prime_natGenerator v).pos) _

/--
@isnad1 id=eq.0h2v.s9.9e58c4338d19 from=translated src=- shape=4f8026e9 vocab=fc85dab4
-/
theorem valuation_ρ (w : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℚ)ˣ) : w.valuation ℚ (ρ x) = Valued.v ((x : 𝔸ℚ).2 w) := by
  classical
  rw [ρ, map_mul, valuation_archSign, one_mul, finprod_eq_prod_of_mulSupport_subset _ (mulSupport_subset_toFinset x),
    map_prod, valued_snd_eq, Finset.prod_eq_single w]
  · rw [map_zpow₀, valuation_natGenerator, ← exp_zsmul, smul_eq_mul, mul_neg_one]
  · intro v _ hvw
    rw [map_zpow₀, valuation_natGenerator_of_ne hvw, one_zpow]
  · intro hw
    have h0 : ordAt w x = 0 := by
      by_contra h0
      exact hw ((Set.Finite.mem_toFinset _).mpr h0)
    rw [h0, zpow_zero, map_one]

/--
@isnad1 id=isnormal.0h1v.s6.8f4350ebcb77 from=translated src=- shape=a39cd560 vocab=50029add
-/
theorem ρ_spec (x : (𝔸ℚ)ˣ) : IsNormalizer x (ρ x) := by
  refine ⟨fun v => (valuation_ρ v x).symm, ?_⟩
  rw [ρ, Rat.cast_mul, ← mul_assoc]
  exact mul_pos (archCoord_mul_archSign_pos x) (by exact_mod_cast finprod_pow_ordAt_pos x)

/--
@isnad1 id=ex.0h1v.s6.88b56894c113 from=translated src=- shape=1de1dad5 vocab=283a3085
-/
theorem exists_isNormalizer (x : (𝔸ℚ)ˣ) : ∃ r : ℚ, IsNormalizer x r := ⟨ρ x, ρ_spec x⟩

/--
@isnad1 id=eq.2h1v.s6.0983dacf7c67 from=translated src=- shape=45dcb0c7 vocab=c3845b43
-/
theorem rat_eq_one_of_valuation_eq_one {q : ℚ} (hq : 0 < q)
    (h : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.valuation ℚ q = 1) : q = 1 := by
  have hq0 : q ≠ 0 := hq.ne'
  obtain ⟨z, hz⟩ := mem_integers_of_valuation_le_one ℚ q fun v => (h v).le
  obtain ⟨z', hz'⟩ := mem_integers_of_valuation_le_one ℚ q⁻¹ fun v => by rw [map_inv₀, h v, inv_one]
  have hzz' : z * z' = 1 :=
    IsFractionRing.injective (𝓞 ℚ) ℚ (by rw [map_mul, hz, hz', map_one, mul_inv_cancel₀ hq0])
  have hu : IsUnit z := isUnit_iff_exists_inv.mpr ⟨z', hzz'⟩
  have hzq : (z : ℚ) = q := by rw [RingOfIntegers.coe_eq_algebraMap]; exact hz
  rcases Rat.RingOfIntegers.isUnit_iff.mp hu with h1 | h1
  · rw [← hzq]; exact h1
  · exfalso
    rw [hzq] at h1
    rw [h1] at hq
    exact absurd hq (by norm_num)

/--
@isnad1 id=eq.2h3v.s6.e79b0d053216 from=translated src=- shape=fcf6a099 vocab=283a3085
-/
theorem IsNormalizer.unique {x : (𝔸ℚ)ˣ} {r r' : ℚ} (h : IsNormalizer x r) (h' : IsNormalizer x r') : r = r' := by
  have hr' := h'.ne_zero
  have hq : 0 < r / r' := by
    have h3 : (0 : ℝ) < (archCoord x * r) / (archCoord x * r') := div_pos h.2 h'.2
    rw [mul_div_mul_left _ _ (archCoord_ne_zero x)] at h3
    exact_mod_cast h3
  have hval : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.valuation ℚ (r / r') = 1 := fun v => by
    rw [map_div₀, ← h.1 v, ← h'.1 v, div_self (valued_snd_ne_zero x v)]
  have := rat_eq_one_of_valuation_eq_one hq hval
  rwa [div_eq_one_iff_eq hr'] at this

/--
@isnad1 id=ne.0h1v.s6.f6baf941ca37 from=translated src=- shape=3483810d vocab=a987c2da
-/
theorem ρ_ne_zero (x : (𝔸ℚ)ˣ) : ρ x ≠ 0 := (ρ_spec x).ne_zero

/--
@isnad1 id=eq.1h2v.s6.0b89c9423314 from=translated src=- shape=48ce8f0e vocab=50029add
-/
theorem ρ_eq_of_isNormalizer {x : (𝔸ℚ)ˣ} {r : ℚ} (h : IsNormalizer x r) : ρ x = r := (ρ_spec x).unique h

/--
@isnad1 id=eq.0h2v.s9.f9878e776e43 from=translated src=- shape=33ce4d03 vocab=16f796b4
-/
theorem ρ_mul (x y : (𝔸ℚ)ˣ) : ρ (x * y) = ρ x * ρ y := by
  refine ρ_eq_of_isNormalizer ⟨fun v => ?_, ?_⟩
  · rw [valued_snd_mul, (ρ_spec x).1 v, (ρ_spec y).1 v, map_mul]
  · rw [archCoord_mul, Rat.cast_mul, show archCoord x * archCoord y * (((ρ x : ℚ) : ℝ) * ((ρ y : ℚ) : ℝ))
        = (archCoord x * ((ρ x : ℚ) : ℝ)) * (archCoord y * ((ρ y : ℚ) : ℝ)) by ring]
    exact mul_pos (ρ_spec x).2 (ρ_spec y).2

/--
@isnad1 id=eq.0h1v.s9.d653b9990130 from=translated src=- shape=93da2077 vocab=e8df093d
-/
theorem ρ_principal (q : ℚˣ) : ρ (Units.map (algebraMap ℚ 𝔸ℚ : ℚ →* 𝔸ℚ) q) = (q : ℚ) := by
  refine ρ_eq_of_isNormalizer ⟨fun v => ?_, ?_⟩
  · rw [Units.coe_map, MonoidHom.coe_coe, algebraMap_adeleRing_snd, valued_algebraMap_rat]
  · rw [archCoord_principal]
    exact mul_self_pos.mpr (by exact_mod_cast q.ne_zero)

/--
@isnad1 id=eq.0h0v.s7.282f6874a978 from=translated src=- shape=040384d4 vocab=a987c2da
-/
theorem ρ_one : ρ 1 = 1 := by
  have := ρ_principal 1
  rwa [map_one, Units.val_one] at this

/--
@isnad1 id=eq.1h2v.s11.cce07fbc0e32 from=translated src=- shape=a7399b56 vocab=55429070
-/
theorem ρ_finIncl_localUnit_of_valued_one (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ)
    (ht : Valued.v (t : v.adicCompletion ℚ) = 1) :
    ρ (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v t)) = 1 := by
  refine ρ_eq_of_isNormalizer ⟨fun w => ?_, ?_⟩
  · rw [Units.coe_map, finIncl_apply_snd, map_one]
    by_cases hw : w = v
    · subst hw
      rw [localUnit_apply_self, ht]
    · rw [localUnit_apply_of_ne (𝓞 ℚ) ℚ v t hw, map_one]
  · rw [archCoord_finIncl, one_mul, Rat.cast_one]
    exact one_pos

end Normalizer

section UnitAt

def unitAt (v : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℚ)ˣ) : v.adicCompletion ℚ :=
  (x : 𝔸ℚ).2 v * (algebraMap ℚ (v.adicCompletion ℚ) (ρ x))⁻¹

/--
@isnad1 id=eq.0h2v.s8.1de0e3ae0437 from=translated src=- shape=50b393ca vocab=2a4e7e8b
-/
theorem valued_unitAt (v : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℚ)ˣ) : Valued.v (unitAt v x) = 1 := by
  unfold unitAt
  rw [map_mul, map_inv₀, valued_algebraMap_rat, ← (ρ_spec x).1 v, mul_inv_cancel₀ (valued_snd_ne_zero x v)]

/--
@isnad1 id=eq.0h3v.s9.9cd70acce5c7 from=translated src=- shape=b3c5f58e vocab=d37fe045
-/
theorem unitAt_mul (v : HeightOneSpectrum (𝓞 ℚ)) (x y : (𝔸ℚ)ˣ) : unitAt v (x * y) = unitAt v x * unitAt v y := by
  unfold unitAt
  rw [ρ_mul, map_mul, mul_inv, show (((x * y : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v = (x : 𝔸ℚ).2 v * (y : 𝔸ℚ).2 v from rfl]
  ring

/--
@isnad1 id=eq.0h1v.s8.ff9079f7b856 from=translated src=- shape=52096b6b vocab=d8687ee9
-/
theorem unitAt_one (v : HeightOneSpectrum (𝓞 ℚ)) : unitAt v 1 = 1 := by
  unfold unitAt
  rw [ρ_one, map_one, inv_one, mul_one]
  rfl

/--
@isnad1 id=eq.0h2v.s10.84c7ab3b7cb4 from=translated src=- shape=606ad144 vocab=ce634d82
-/
theorem unitAt_principal (v : HeightOneSpectrum (𝓞 ℚ)) (q : ℚˣ) :
    unitAt v (Units.map (algebraMap ℚ 𝔸ℚ : ℚ →* 𝔸ℚ) q) = 1 := by
  unfold unitAt
  rw [ρ_principal, Units.coe_map, MonoidHom.coe_coe, algebraMap_adeleRing_snd,
    mul_inv_cancel₀ ((map_ne_zero _).mpr q.ne_zero)]

/--
@isnad1 id=eq.1h2v.s11.11d25e4f1a46 from=translated src=- shape=6493a49c vocab=dd361107
-/
theorem unitAt_finIncl_localUnit_self (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ)
    (ht : Valued.v (t : v.adicCompletion ℚ) = 1) :
    unitAt v (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v t)) = t := by
  unfold unitAt
  rw [ρ_finIncl_localUnit_of_valued_one v t ht, map_one, inv_one, mul_one, Units.coe_map, finIncl_apply_snd,
    localUnit_apply_self]

/--
@isnad1 id=eq.2h3v.s11.3c1bd4234d09 from=translated src=- shape=a13b9d9e vocab=dd361107
-/
theorem unitAt_finIncl_localUnit_of_ne (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ)
    (ht : Valued.v (t : v.adicCompletion ℚ) = 1) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    unitAt w (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v t)) = 1 := by
  unfold unitAt
  rw [ρ_finIncl_localUnit_of_valued_one v t ht, map_one, inv_one, mul_one, Units.coe_map, finIncl_apply_snd,
    localUnit_apply_of_ne (𝓞 ℚ) ℚ v t hw]

def unitIntAt (v : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℚ)ˣ) : v.adicCompletionIntegers ℚ :=
  ⟨unitAt v x, (mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr (valued_unitAt v x).le⟩

/--
@isnad1 id=eq.0h2v.s8.8b418c631634 from=translated src=- shape=65232e65 vocab=b4f40f75
-/
theorem coe_unitIntAt (v : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℚ)ˣ) :
    (unitIntAt v x : v.adicCompletion ℚ) = unitAt v x := rfl

/--
@isnad1 id=eq.0h3v.s11.4359276ed654 from=translated src=- shape=c94a1f38 vocab=b9ce4af0
-/
theorem unitIntAt_mul (v : HeightOneSpectrum (𝓞 ℚ)) (x y : (𝔸ℚ)ˣ) :
    unitIntAt v (x * y) = unitIntAt v x * unitIntAt v y :=
  Subtype.ext (unitAt_mul v x y)

/--
@isnad1 id=eq.0h1v.s9.70292cebe8c7 from=translated src=- shape=f4e68909 vocab=2f59ad89
-/
theorem unitIntAt_one (v : HeightOneSpectrum (𝓞 ℚ)) : unitIntAt v 1 = 1 := Subtype.ext (unitAt_one v)

/--
@isnad1 id=isunit.0h2v.s9.bd30cd67e38c from=translated src=- shape=6a3799e7 vocab=e5a88624
-/
theorem isUnit_unitIntAt (v : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℚ)ˣ) : IsUnit (unitIntAt v x) :=
  isUnit_iff_exists_inv.mpr ⟨unitIntAt v x⁻¹, by rw [← unitIntAt_mul, mul_inv_cancel, unitIntAt_one]⟩

/--
@isnad1 id=eq.1h3v.s11.758d85a4387d from=translated src=- shape=5a579085 vocab=5b588de8
-/
theorem natCast_mul_unitIntAt_eq_one {v : HeightOneSpectrum (𝓞 ℚ)} {x : (𝔸ℚ)ˣ} {n : ℕ}
    (h : ((n : ℕ) : v.adicCompletion ℚ) * unitAt v x = 1) :
    ((n : ℕ) : v.adicCompletionIntegers ℚ) * unitIntAt v x = 1 :=
  Subtype.ext (by rw [MulMemClass.coe_mul, SubringClass.coe_natCast, OneMemClass.coe_one]; exact h)

end UnitAt

end RatIdele

end
