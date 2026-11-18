import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.Seed.RingTheory.PowerSeries.Expand
import Tengoku.Seed.FieldTheory.Finite.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_pow_char_eq_qExpand_of_coeff_fixed.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`, 3 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_pow_char_eq_qExpand_of_coeff_fixed

noncomputable section

open scoped PowerSeries.WithPiTopology
open PowerSeries HahnSeries

namespace ModularCurve
export _root_.ModularCurve (qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single ofPowerSeries_coeff_of_neg)
open _root_.ModularCurve

namespace CharL

section LaurentMap

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

def laurentMap (f : R →+* S) : LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map f
  map_one' := HahnSeries.map_one (R := R) (S := S) f.toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul (R := R) (S := S) f.toNonUnitalRingHom
  map_zero' := by
    ext k
    show f ((0 : LaurentSeries R).coeff k) = (0 : LaurentSeries S).coeff k
    rw [HahnSeries.coeff_zero, HahnSeries.coeff_zero, map_zero]
  map_add' x y := by
    ext k
    show f ((x + y).coeff k) = (x.map f + y.map f).coeff k
    rw [HahnSeries.coeff_add, HahnSeries.coeff_add, map_add]
    rfl

/--
@isnad1 id=eq.0h5v.s8.f0fbf698be42 from=translated src=- shape=91225d07 vocab=795da898
-/
@[scoped simp]
theorem laurentMap_coeff (f : R →+* S) (x : LaurentSeries R) (k : ℤ) :
    (laurentMap f x).coeff k = f (x.coeff k) := rfl

/--
@isnad1 id=eq.0h5v.s8.68ada7e9d217 from=translated src=- shape=d658a659 vocab=a22acb0e
-/
@[scoped simp]
theorem laurentMap_single (f : R →+* S) (k : ℤ) (r : R) :
    laurentMap f (HahnSeries.single k r) = HahnSeries.single k (f r) := by
  ext g
  rw [laurentMap_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single, apply_ite f,
    map_zero]

/--
@isnad1 id=eq.0h4v.s9.a314ddf55f2e from=translated src=- shape=3c04b3c9 vocab=a524e507
-/
theorem laurentMap_ofPowerSeries (f : R →+* S) (p : PowerSeries R) :
    laurentMap f (HahnSeries.ofPowerSeries ℤ R p) =
      HahnSeries.ofPowerSeries ℤ S (p.map f) := by
  ext k
  rw [laurentMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

end LaurentMap

section ExpandSeam

variable {R : Type*} [CommRing R] (p : ℕ) [NeZero p]

/--
@isnad1 id=eq.0h3v.s9.ba8346bf58b6 from=translated src=- shape=d05b2b85 vocab=9f6a54b0
-/
theorem qExpand_ofPowerSeries_eq_expand (u : PowerSeries R) :
    qExpand R p (HahnSeries.ofPowerSeries ℤ R u)
      = HahnSeries.ofPowerSeries ℤ R (PowerSeries.expand p (NeZero.ne p) u) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  ext k
  by_cases hpk : (p : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hpk
    rw [qExpand_coeff_mul]
    rcases lt_or_ge m 0 with hm | hm
    · have hpm : (p : ℤ) * m < 0 := mul_neg_of_pos_of_neg hp0 hm
      rw [ofPowerSeries_coeff_of_neg _ hm, ofPowerSeries_coeff_of_neg _ hpm]
    · lift m to ℕ using hm with m
      have hcast : ((p : ℤ) * (m : ℤ)) = ((p * m : ℕ) : ℤ) := by push_cast; ring
      rw [HahnSeries.ofPowerSeries_apply_coeff, hcast, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_expand_mul]
  · rw [qExpand_coeff_of_not_dvd p _ hpk]
    rcases lt_or_ge k 0 with hk | hk
    · exact (ofPowerSeries_coeff_of_neg _ hk).symm
    · lift k to ℕ using hk with k
      rw [HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_expand_of_not_dvd p (NeZero.ne p) u
          (fun ⟨m, hm⟩ => hpk ⟨m, by exact_mod_cast hm⟩)]

end ExpandSeam

section KeyLemma

variable {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

/--
@isnad1 id=eq.0h3v.s9.65f7890befa3 from=translated src=- shape=0abe97e2 vocab=d5cb7682
-/
theorem pow_char_single_one_eq (n : ℤ) :
    (HahnSeries.single n (1 : R)) ^ p
      = laurentMap (frobenius R p) (qExpand R p (HahnSeries.single n (1 : R))) := by
  haveI : ExpChar R p := ExpChar.prime (Fact.out : p.Prime)
  rw [HahnSeries.single_pow, one_pow, qExpand_single, laurentMap_single,
    show frobenius R p 1 = 1 from (frobenius R p).map_one,
    show (p • n : ℤ) = (p : ℤ) * n from nsmul_eq_mul p n]

/--
@isnad1 id=eq.0h3v.s9.77dd751fb3d0 from=translated src=- shape=580d5fd2 vocab=e4bd7d2d
-/
theorem pow_char_ofPowerSeries_eq (u : PowerSeries R) :
    (HahnSeries.ofPowerSeries ℤ R u) ^ p
      = laurentMap (frobenius R p)
          (qExpand R p (HahnSeries.ofPowerSeries ℤ R u)) := by
  haveI : ExpChar R p := ExpChar.prime (Fact.out : p.Prime)
  rw [qExpand_ofPowerSeries_eq_expand p u, laurentMap_ofPowerSeries, ← map_pow]
  congr 1
  exact (MvPowerSeries.map_frobenius_expand p (NeZero.ne p) (f := u)).symm

/--
@isnad1 id=eq.0h3v.s8.6c923fe8a1c8 from=translated src=- shape=b71fdaa4 vocab=28824f07
-/
theorem pow_char_eq_laurentMap_frobenius_qExpand (s : LaurentSeries R) :
    s ^ p = laurentMap (frobenius R p) (qExpand R p s) := by
  conv_lhs => rw [← LaurentSeries.single_order_mul_powerSeriesPart s]
  conv_rhs => rw [← LaurentSeries.single_order_mul_powerSeriesPart s]
  rw [mul_pow, map_mul, map_mul, pow_char_single_one_eq p s.order]
  congr 1
  exact pow_char_ofPowerSeries_eq p s.powerSeriesPart

/--
@isnad1 id=eq.1h3v.s8.46a0b38a648b from=translated src=- shape=d2cdd794 vocab=bed9d157
-/
theorem pow_char_eq_qExpand_of_coeff_fixed (s : LaurentSeries R)
    (hfix : ∀ k : ℤ, (s.coeff k) ^ p = s.coeff k) :
    s ^ p = qExpand R p s := by
  rw [pow_char_eq_laurentMap_frobenius_qExpand p s]
  ext k
  rw [laurentMap_coeff, frobenius_def]
  by_cases hpk : (p : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hpk
    rw [qExpand_coeff_mul, hfix m]
  · rw [qExpand_coeff_of_not_dvd p _ hpk, zero_pow (Fact.out : p.Prime).ne_zero]

end KeyLemma

section IntCastImage

variable {K : Type*} [CommRing K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

end IntCastImage

end CharL
open scoped _root_.P2MW.S_ModularCurve_pow_char_eq_qExpand_of_coeff_fixed.ModularCurve.CharL

end ModularCurve
open scoped _root_.P2MW.S_ModularCurve_pow_char_eq_qExpand_of_coeff_fixed.ModularCurve.CharL _root_.P2MW.S_ModularCurve_pow_char_eq_qExpand_of_coeff_fixed.ModularCurve

end
open scoped _root_.P2MW.S_ModularCurve_pow_char_eq_qExpand_of_coeff_fixed.ModularCurve.CharL _root_.P2MW.S_ModularCurve_pow_char_eq_qExpand_of_coeff_fixed.ModularCurve

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_pow_char_eq_qExpand_of_coeff_fixed.ModularCurve in
/--
@isnad1 id=eq.1h3v.s8.46a0b38a648b from=translated src=- shape=d2cdd794 vocab=bed9d157
-/
theorem solution {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (s : LaurentSeries R) (hfix : ∀ k : ℤ, (s.coeff k) ^ p = s.coeff k) :
    s ^ p = qExpand R p s :=
  ModularCurve.CharL.pow_char_eq_qExpand_of_coeff_fixed p s hfix
