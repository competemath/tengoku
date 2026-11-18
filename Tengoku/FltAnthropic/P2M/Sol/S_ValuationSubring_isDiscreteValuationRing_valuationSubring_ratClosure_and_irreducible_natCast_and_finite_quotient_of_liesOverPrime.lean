import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ValuationSubring_CompletionRatClosure
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ValuationSubring_isDiscreteValuationRing_valuationSubring_ratClosure_and_irreducible_natCast_and_finite_quotient_of_liesOverPrime.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ValuationSubring_isDiscreteValuationRing_valuationSubring_ratClosure_and_irreducible_natCast_and_finite_quotient_of_liesOverPrime

set_option autoImplicit false

open _root_.ValuationSubring

namespace ValuationSubring
export _root_.ValuationSubring (comap subtype ext mem_nonunits_iff mk ValueGroup valuation_le_one_iff valuation ratClosure coe_ratClosure natCast_mem_ratClosure LiesOverPrime)
namespace DVRkit
open _root_.ValuationSubring

/--
@isnad1 id=ex.2h3v.s6.30307ecd42d7 from=translated src=- shape=07250d1d vocab=6b2349d5
-/
theorem exists_nat_sub_mul_den_eq {r : ℕ} (hr : 0 < r) (q : ℚ) (hcop : (q.den).Coprime r) (N : ℕ) :
    ∃ a : ℕ, a < r ^ N ∧ ∃ w : ℤ, ((q - a) * q.den : ℚ) = (r : ℚ) ^ N * w := by
  have hcopN : (q.den).Coprime (r ^ N) := Nat.Coprime.pow_right N hcop
  obtain ⟨y, hy⟩ := Int.mod_coprime hcopN

  have hRpos : (0 : ℤ) < (r : ℤ) ^ N := by positivity
  set a : ℤ := (q.num * y) % ((r : ℤ) ^ N) with ha
  have ha0 : 0 ≤ a := Int.emod_nonneg _ hRpos.ne'
  have haR : a < (r : ℤ) ^ N := Int.emod_lt_of_pos _ hRpos
  have hdvd : ((r : ℤ) ^ N) ∣ q.num - a * q.den := by

    have h1 : a ≡ q.num * y [ZMOD (r : ℤ) ^ N] := Int.mod_modEq _ _
    have h2 : (q.den : ℤ) * y ≡ 1 [ZMOD (r : ℤ) ^ N] := by exact_mod_cast hy
    have h3 : a * q.den ≡ q.num [ZMOD (r : ℤ) ^ N] := by
      calc a * q.den ≡ q.num * y * q.den [ZMOD (r : ℤ) ^ N] := h1.mul_right _
        _ = q.num * (q.den * y) := by ring
        _ ≡ q.num * 1 [ZMOD (r : ℤ) ^ N] := h2.mul_left _
        _ = q.num := by ring
    exact (Int.modEq_iff_dvd.mp h3)
  obtain ⟨w, hw⟩ := hdvd
  refine ⟨a.toNat, ?_, w, ?_⟩
  · have : (a.toNat : ℤ) < (r : ℤ) ^ N := by rw [Int.toNat_of_nonneg ha0]; exact haR
    exact_mod_cast this
  · have hq : (q : ℚ) = q.num / q.den := (Rat.num_div_den q).symm
    have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
    have haa : ((a.toNat : ℕ) : ℚ) = (a : ℚ) := by exact_mod_cast Int.toNat_of_nonneg ha0
    have hw' : ((q.num - a * q.den : ℤ) : ℚ) = (((r : ℤ) ^ N * w : ℤ) : ℚ) := by exact_mod_cast hw
    push_cast at hw'
    rw [haa, ← hw', sub_mul, Rat.mul_den_eq_num]

section B

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {r : ℕ}

/--
@isnad1 id=eq.0h2v.s11.d7ce1a366342 from=translated src=- shape=894f39ac vocab=f7bbbe49
-/
theorem v_coe (x : AlgebraicClosure ℚ) : Valued.v (x : A.valuation.Completion) = A.valuation x := by
  rw [show (x : A.valuation.Completion) =
      (((WithVal.equiv A.valuation).symm x : WithVal A.valuation) : A.valuation.Completion) from rfl,
    Valued.valuedCompletion_apply]
  rfl

noncomputable def coeHom : AlgebraicClosure ℚ →+* A.valuation.Completion :=
  (UniformSpace.Completion.coeRingHom : WithVal A.valuation →+* A.valuation.Completion).comp
    (WithVal.equiv A.valuation).symm.toRingHom

/--
@isnad1 id=eq.0h2v.s10.c57404a35c7e from=translated src=- shape=83ff4f38 vocab=6cf11d55
-/
theorem coeHom_apply (x : AlgebraicClosure ℚ) : coeHom A x = (x : A.valuation.Completion) := rfl

/--
@isnad1 id=eq.0h2v.s10.b78051c39196 from=translated src=- shape=bf51c2d8 vocab=01f21390
-/
theorem coe_ratCast' (q : ℚ) : ((q : AlgebraicClosure ℚ) : A.valuation.Completion) = (q : A.valuation.Completion) := by
  rw [← coeHom_apply, map_ratCast]

/--
@isnad1 id=eq.0h2v.s10.7e9b9884e3b5 from=translated src=- shape=2b461f8a vocab=32508014
-/
theorem v_ratCast (q : ℚ) : Valued.v (q : A.valuation.Completion) = A.valuation (q : AlgebraicClosure ℚ) := by
  rw [← coe_ratCast', v_coe]

/--
@isnad1 id=eq.0h2v.s10.16bfccc0c938 from=translated src=- shape=d0d86291 vocab=e8ed199e
-/
theorem v_natCast (n : ℕ) : Valued.v (n : A.valuation.Completion) = A.valuation (n : AlgebraicClosure ℚ) := by
  rw [← Rat.cast_natCast, v_ratCast, Rat.cast_natCast]

/--
@isnad1 id=le.0h2v.s8.10f4e2851cb8 from=translated src=- shape=96f08dce vocab=935cc5a4
-/
theorem vA_natCast_le_one (n : ℕ) : A.valuation (n : AlgebraicClosure ℚ) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (natCast_mem A n)

/--
@isnad1 id=le.0h2v.s8.9ba93b9641b1 from=translated src=- shape=96f08dce vocab=1ce7aa5c
-/
theorem vA_intCast_le_one (n : ℤ) : A.valuation (n : AlgebraicClosure ℚ) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (intCast_mem A n)

/--
@isnad1 id=eq.2h3v.s7.930e09324715 from=translated src=- shape=fa117d21 vocab=6db8262e
-/
theorem vA_natCast_eq_one_of_coprime (hA : A.LiesOverPrime r) {d : ℕ} (hd : d.Coprime r) :
    A.valuation (d : AlgebraicClosure ℚ) = 1 := by
  refine le_antisymm (vA_natCast_le_one A d) (not_lt.mp fun hlt => ?_)
  have hAr : A.valuation (r : AlgebraicClosure ℚ) < 1 := A.mem_nonunits_iff.mp hA
  obtain ⟨u, t, hut⟩ := Nat.isCoprime_iff_coprime.mpr hd

  have h1 : (u : AlgebraicClosure ℚ) * d + t * r = 1 := by exact_mod_cast hut
  have hv : A.valuation ((u : AlgebraicClosure ℚ) * d + t * r) < 1 := by
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (vA_intCast_le_one A u) zero_le hlt
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (vA_intCast_le_one A t) zero_le hAr
  rw [h1, map_one] at hv
  exact lt_irrefl _ hv

/--
@isnad1 id=coprime.3h3v.s8.9683bdf15e64 from=translated src=- shape=049de089 vocab=5175bffc
-/
theorem den_coprime_of_vA_le_one (hr : r.Prime) (hA : A.LiesOverPrime r) {q : ℚ}
    (hq : A.valuation (q : AlgebraicClosure ℚ) ≤ 1) : (q.den).Coprime r := by
  rw [Nat.Coprime, Nat.gcd_comm, ← Nat.Coprime, hr.coprime_iff_not_dvd]
  intro hdvd
  have hAr : A.valuation (r : AlgebraicClosure ℚ) < 1 := A.mem_nonunits_iff.mp hA
  obtain ⟨k, hk⟩ := hdvd
  have hden : A.valuation (q.den : AlgebraicClosure ℚ) < 1 := by
    rw [hk, Nat.cast_mul, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hAr (vA_natCast_le_one A k)

  have hnum : (q.num.natAbs).Coprime r :=
    Nat.Coprime.coprime_dvd_right ⟨k, hk⟩ q.reduced
  have hvnum : A.valuation (q.num : AlgebraicClosure ℚ) = 1 := by
    have h := vA_natCast_eq_one_of_coprime A hA hnum
    have hcast : ((q.num.natAbs : ℕ) : AlgebraicClosure ℚ) = ((q.num.natAbs : ℤ) : AlgebraicClosure ℚ) := (Int.cast_natCast _).symm
    rcases Int.natAbs_eq q.num with hn | hn
    · rw [hn, ← hcast]; exact h
    · rw [hn, Int.cast_neg, Valuation.map_neg, ← hcast]; exact h
  have hden0 : A.valuation (q.den : AlgebraicClosure ℚ) ≠ 0 :=
    (map_ne_zero _).mpr (by exact_mod_cast q.den_nz)
  have hq' : A.valuation (q : AlgebraicClosure ℚ) = (A.valuation (q.den : AlgebraicClosure ℚ))⁻¹ := by
    rw [Rat.cast_def, map_div₀, hvnum, one_div]
  rw [hq'] at hq
  have : 1 ≤ A.valuation (q.den : AlgebraicClosure ℚ) := by
    rwa [inv_le_one₀ (zero_lt_iff.mpr hden0)] at hq
  exact absurd hden (not_lt.mpr this)

end B

section N

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {r : ℕ}

end N

section L

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {r : ℕ}

/--
@isnad1 id=eq.3h3v.s7.8f3c9bbcde09 from=translated src=- shape=de68acfd vocab=8f325696
-/
theorem vA_natCast_eq_one_of_not_dvd (hr : r.Prime) (hA : A.LiesOverPrime r) {d : ℕ} (hd : ¬ r ∣ d) :
    A.valuation (d : AlgebraicClosure ℚ) = 1 :=
  vA_natCast_eq_one_of_coprime A hA ((Nat.Prime.coprime_iff_not_dvd hr).mpr hd).symm

/--
@isnad1 id=ex.3h3v.s8.fd6f5e2e0f18 from=translated src=- shape=6bc851ee vocab=b1932c0c
-/
theorem vA_natCast_eq_zpow (hr : r.Prime) (hA : A.LiesOverPrime r) {n : ℕ} (hn : n ≠ 0) :
    ∃ e : ℕ, A.valuation (n : AlgebraicClosure ℚ) = A.valuation (r : AlgebraicClosure ℚ) ^ e := by
  obtain ⟨e, n', hnd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn r hr.ne_one
  refine ⟨e, ?_⟩
  rw [Nat.cast_mul, Nat.cast_pow, map_mul, map_pow, vA_natCast_eq_one_of_not_dvd A hr hA hnd, mul_one]

/--
@isnad1 id=ex.3h3v.s8.a022b40e4729 from=translated src=- shape=846573f7 vocab=3ba72eb4
-/
theorem vA_ratCast_eq_zpow (hr : r.Prime) (hA : A.LiesOverPrime r) {q : ℚ} (hq : q ≠ 0) :
    ∃ n : ℤ, A.valuation (q : AlgebraicClosure ℚ) = A.valuation (r : AlgebraicClosure ℚ) ^ n := by
  have hnum0 : q.num.natAbs ≠ 0 := by simpa using (Rat.num_ne_zero.mpr hq)
  obtain ⟨a, ha⟩ := vA_natCast_eq_zpow A hr hA hnum0
  obtain ⟨b, hb⟩ := vA_natCast_eq_zpow A hr hA q.den_nz
  have hvnum : A.valuation (q.num : AlgebraicClosure ℚ) = A.valuation (r : AlgebraicClosure ℚ) ^ a := by
    have hcast : ((q.num.natAbs : ℕ) : AlgebraicClosure ℚ) = ((q.num.natAbs : ℤ) : AlgebraicClosure ℚ) :=
      (Int.cast_natCast _).symm
    rcases Int.natAbs_eq q.num with hn | hn
    · rw [hn, ← hcast]; exact ha
    · rw [hn, Int.cast_neg, Valuation.map_neg, ← hcast]; exact ha
  refine ⟨(a : ℤ) - b, ?_⟩
  have hvr0 : A.valuation (r : AlgebraicClosure ℚ) ≠ 0 := (map_ne_zero _).mpr (by exact_mod_cast hr.ne_zero)
  rw [Rat.cast_def, map_div₀, hvnum, hb, zpow_sub₀ hvr0, zpow_natCast, zpow_natCast]

/--
@isnad1 id=ex.2h2v.s12.99fc9595ea9f from=translated src=- shape=99029845 vocab=6a7deb03
-/
theorem exists_rat_v_eq {x : A.valuation.Completion} (hx : x ∈ ratClosure A) (hx0 : x ≠ 0) :
    ∃ q : ℚ, Valued.v (q : A.valuation.Completion) = Valued.v x := by

  have hvx0 : Valued.v.restrict x ≠ 0 := (map_ne_zero _).mpr hx0
  have hopen : IsOpen {y : A.valuation.Completion | Valued.v.restrict y = Valued.v.restrict x} :=
    (Valued.isClopen_sphere _ hvx0).isOpen
  have hxmem : x ∈ closure ((⊥ : Subfield A.valuation.Completion) : Set A.valuation.Completion) := hx
  obtain ⟨y, hyV, hybot⟩ := mem_closure_iff.mp hxmem _ hopen rfl
  have : (⊥ : Subfield A.valuation.Completion) ≤ (Rat.castHom A.valuation.Completion).fieldRange := bot_le
  obtain ⟨q, hq⟩ := RingHom.mem_fieldRange.mp (this hybot)
  refine ⟨q, ?_⟩
  have hyx : Valued.v.restrict y = Valued.v.restrict x := hyV
  have h1 : Valued.v y ≤ Valued.v x := (Valuation.restrict_le_iff _).mp hyx.le
  have h2 : Valued.v x ≤ Valued.v y := (Valuation.restrict_le_iff _).mp hyx.ge
  rw [show (q : A.valuation.Completion) = y from hq]
  exact le_antisymm h1 h2

/--
@isnad1 id=ex.4h3v.s12.6c2675f82aa7 from=translated src=- shape=b7ae5120 vocab=5d46200d
-/
theorem v_eq_zpow_of_mem_ratClosure (hr : r.Prime) (hA : A.LiesOverPrime r) {x : A.valuation.Completion}
    (hx : x ∈ ratClosure A) (hx0 : x ≠ 0) :
    ∃ n : ℤ, Valued.v x = Valued.v ((r : A.valuation.Completion)) ^ n := by
  obtain ⟨q, hq⟩ := exists_rat_v_eq A hx hx0
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [Rat.cast_zero, map_zero] at hq
    exact hx0 ((map_eq_zero _).mp hq.symm)
  obtain ⟨n, hn⟩ := vA_ratCast_eq_zpow A hr hA hq0
  exact ⟨n, by rw [← hq, v_ratCast, hn, v_natCast]⟩

/--
@isnad1 id=le.4h3v.s12.7235d01d2f6b from=translated src=- shape=f6ac19f6 vocab=8eae9eca
-/
theorem v_le_v_natCast_of_lt_one (hr : r.Prime) (hA : A.LiesOverPrime r) {x : A.valuation.Completion}
    (hx : x ∈ ratClosure A) (hx1 : Valued.v x < 1) :
    Valued.v x ≤ Valued.v ((r : A.valuation.Completion)) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [map_zero]; exact zero_le
  obtain ⟨n, hn⟩ := v_eq_zpow_of_mem_ratClosure A hr hA hx hx0
  have hvr : Valued.v ((r : A.valuation.Completion)) = A.valuation (r : AlgebraicClosure ℚ) := v_natCast A r
  have hvr1 : Valued.v ((r : A.valuation.Completion)) < 1 := by rw [hvr]; exact A.mem_nonunits_iff.mp hA
  have hvr0 : 0 < Valued.v ((r : A.valuation.Completion)) := by
    rw [hvr]; exact zero_lt_iff.mpr ((map_ne_zero _).mpr (by exact_mod_cast hr.ne_zero))
  rw [hn] at hx1 ⊢
  have hn1 : 1 ≤ n := by
    by_contra h
    have h' : n ≤ 0 := by omega
    exact absurd hx1 (not_lt.mpr ((one_le_zpow_iff_right_of_lt_one₀ hvr0 hvr1).mpr h'))
  calc Valued.v ((r : A.valuation.Completion)) ^ n ≤ Valued.v ((r : A.valuation.Completion)) ^ (1 : ℤ) :=
        zpow_le_zpow_right_of_le_one₀ hvr0 hvr1.le hn1
    _ = _ := zpow_one _

end L

section M

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {r : ℕ}

noncomputable def vK : Valuation (↥(ratClosure A)) A.ValueGroup := Valued.v.comap (ratClosure A).subtype

noncomputable def O : ValuationSubring ↥(ratClosure A) := (vK A).valuationSubring

/--
@isnad1 id=eq.0h2v.s13.180948bd5dc0 from=translated src=- shape=805a39c1 vocab=26226672
-/
theorem vK_apply (x : ↥(ratClosure A)) : vK A x = Valued.v (x : A.valuation.Completion) := rfl

/--
@isnad1 id=integers.0h1v.s13.3cf13d0ea7a3 from=translated src=- shape=e9b3445d vocab=5dc19df3
-/
theorem integers : (vK A).Integers ↥(O A) :=
  { hom_inj := Subtype.val_injective
    map_le_one := fun x => (Valuation.mem_valuationSubring_iff _ _).mp x.2
    exists_of_le_one := fun x hx => ⟨⟨x, (Valuation.mem_valuationSubring_iff _ _).mpr hx⟩, rfl⟩ }

/--
@isnad1 id=eq.0h2v.s16.cdcbc861b323 from=translated src=- shape=86312964 vocab=8d864338
-/
theorem algebraMap_O_apply (x : ↥(O A)) : algebraMap (↥(O A)) (↥(ratClosure A)) x = (x : ↥(ratClosure A)) := rfl

/--
@isnad1 id=mem.2h2v.s12.5bc836e8d19f from=translated src=- shape=579f7a4d vocab=37ec674e
-/
theorem natCast_mem_O (hr : r.Prime) (hA : A.LiesOverPrime r) :
    (⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩ : ↥(ratClosure A)) ∈ O A := by
  rw [O, Valuation.mem_valuationSubring_iff, vK_apply, v_natCast]
  exact (A.mem_nonunits_iff.mp hA).le

noncomputable def varpi (hr : r.Prime) (hA : A.LiesOverPrime r) : ↥(O A) :=
  ⟨⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩, natCast_mem_O A hr hA⟩

/--
@isnad1 id=eq.2h2v.s16.872e404619da from=translated src=- shape=b63fdc56 vocab=73cb8c6e
-/
theorem v_varpi (hr : r.Prime) (hA : A.LiesOverPrime r) :
    vK A (algebraMap (↥(O A)) (↥(ratClosure A)) (varpi A hr hA)) = Valued.v ((r : A.valuation.Completion)) := rfl

/--
@isnad1 id=lt.2h2v.s10.2c1c7c483db1 from=translated src=- shape=460cc8e7 vocab=3e2eaef9
-/
theorem v_natCast_lt_one (hr : r.Prime) (hA : A.LiesOverPrime r) : Valued.v ((r : A.valuation.Completion)) < 1 := by
  rw [v_natCast]; exact A.mem_nonunits_iff.mp hA

/--
@isnad1 id=lt.1h2v.s10.05e26902d92c from=translated src=- shape=1090c9ae vocab=cca003e5
-/
theorem v_natCast_pos (hr : r.Prime) : 0 < Valued.v ((r : A.valuation.Completion)) := by
  rw [v_natCast]; exact zero_lt_iff.mpr ((map_ne_zero _).mpr (by exact_mod_cast hr.ne_zero))

/--
@isnad1 id=ex.3h3v.s17.aa1c06e27120 from=translated src=- shape=ee0d4617 vocab=bae2aba1
-/
theorem exists_v_eq_pow (hr : r.Prime) (hA : A.LiesOverPrime r) (x : ↥(O A)) (hx0 : x ≠ 0) :
    ∃ n : ℕ, vK A (algebraMap (↥(O A)) (↥(ratClosure A)) x) = Valued.v ((r : A.valuation.Completion)) ^ n := by
  have hxC0 : ((x : ↥(ratClosure A)) : A.valuation.Completion) ≠ 0 := by
    intro h; apply hx0; apply Subtype.ext; apply Subtype.ext; exact h
  obtain ⟨n, hn⟩ := v_eq_zpow_of_mem_ratClosure A hr hA (x : ↥(ratClosure A)).2 hxC0
  have hle : Valued.v ((r : A.valuation.Completion)) ^ n ≤ 1 := by rw [← hn]; exact (integers A).map_le_one x
  have hn0 : 0 ≤ n := by
    by_contra h
    have : (1 : A.ValueGroup) < Valued.v ((r : A.valuation.Completion)) ^ n :=
      (one_lt_zpow_iff_right_of_lt_one₀ (v_natCast_pos A hr) (v_natCast_lt_one A hr hA)).mpr (by omega)
    exact absurd hle (not_le.mpr this)
  refine ⟨n.toNat, ?_⟩
  rw [algebraMap_O_apply, vK_apply, hn, ← zpow_natCast, Int.toNat_of_nonneg hn0]

/--
@isnad1 id=irreduci.2h2v.s14.6d1eb0f6599c from=translated src=- shape=926f1fb6 vocab=47a7c89c
-/
theorem irreducible_varpi (hr : r.Prime) (hA : A.LiesOverPrime r) : Irreducible (varpi A hr hA) := by
  have hv := integers A
  have hvr1 := v_natCast_lt_one A hr hA
  have hvrpos := v_natCast_pos A hr
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have := Valuation.Integers.one_of_isUnit hv hu
    rw [v_varpi] at this; exact absurd this hvr1.ne
  · by_contra hne
    push Not at hne
    obtain ⟨ha, hb⟩ := hne
    have ha1 : vK A (algebraMap (↥(O A)) (↥(ratClosure A)) a) < 1 :=
      lt_of_le_of_ne (hv.map_le_one a) (fun h => ha (Valuation.Integers.isUnit_of_one' hv h))
    have hb1 : vK A (algebraMap (↥(O A)) (↥(ratClosure A)) b) < 1 :=
      lt_of_le_of_ne (hv.map_le_one b) (fun h => hb (Valuation.Integers.isUnit_of_one' hv h))
    have ha2 := v_le_v_natCast_of_lt_one A hr hA (a : ↥(ratClosure A)).2 ha1
    have hb2 := v_le_v_natCast_of_lt_one A hr hA (b : ↥(ratClosure A)).2 hb1
    have hprod : Valued.v ((r : A.valuation.Completion)) =
        vK A (algebraMap (↥(O A)) (↥(ratClosure A)) a) * vK A (algebraMap (↥(O A)) (↥(ratClosure A)) b) := by
      rw [← map_mul, ← map_mul, ← hab]; exact (v_varpi A hr hA).symm
    have : Valued.v ((r : A.valuation.Completion)) ≤
        Valued.v ((r : A.valuation.Completion)) * Valued.v ((r : A.valuation.Completion)) := by
      calc Valued.v ((r : A.valuation.Completion)) = _ := hprod
        _ ≤ _ := mul_le_mul' ha2 hb2
    have h1 : (1 : A.ValueGroup) ≤ Valued.v ((r : A.valuation.Completion)) := by
      rwa [le_mul_iff_one_le_left hvrpos] at this
    exact absurd hvr1 (not_lt.mpr h1)

/--
@isnad1 id=isdiscre.2h2v.s13.d616dc35a8ae from=translated src=- shape=c08fcc64 vocab=39be9bce
-/
theorem isDiscreteValuationRing_O (hr : r.Prime) (hA : A.LiesOverPrime r) : IsDiscreteValuationRing ↥(O A) := by
  have hv := integers A
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨varpi A hr hA, irreducible_varpi A hr hA, ?_⟩
  intro x hx0
  obtain ⟨n, hn⟩ := exists_v_eq_pow A hr hA x hx0
  have h1 : vK A (algebraMap (↥(O A)) (↥(ratClosure A)) x) =
      vK A (algebraMap (↥(O A)) (↥(ratClosure A)) (varpi A hr hA ^ n)) := by
    rw [hn, map_pow, map_pow, v_varpi]
  exact ⟨n, associated_of_dvd_dvd (Valuation.Integers.dvd_of_le hv h1.le) (Valuation.Integers.dvd_of_le hv h1.ge)⟩

/--
@isnad1 id=ex.2h3v.s16.ef095a01dba7 from=translated src=- shape=4c724ac7 vocab=9fd071a0
-/
theorem exists_nat_lt_varpi_dvd_sub (hr : r.Prime) (hA : A.LiesOverPrime r) (x : ↥(O A)) :
    ∃ a : ℕ, a < r ∧ varpi A hr hA ∣ ((a : ℕ) : ↥(O A)) - x := by
  have hv := integers A
  have hvr1 := v_natCast_lt_one A hr hA
  have hvr0 : Valued.v ((r : A.valuation.Completion)) ≠ 0 := (v_natCast_pos A hr).ne'
  let xC : A.valuation.Completion := ((x : ↥(ratClosure A)) : A.valuation.Completion)
  have hxmem : xC ∈ closure ((⊥ : Subfield A.valuation.Completion) : Set A.valuation.Completion) := by
    rw [← coe_ratClosure]; exact (x : ↥(ratClosure A)).2

  have hunit : Valued.v.restrict ((r : A.valuation.Completion)) ≠ 0 :=
    (map_ne_zero _).mpr (fun h => hvr0 (by rw [h, map_zero]))
  have hW : {y : A.valuation.Completion | Valued.v.restrict (y - xC) < ↑(Units.mk0 _ hunit)} ∈ nhds xC :=
    Valued.mem_nhds.mpr ⟨Units.mk0 _ hunit, subset_rfl⟩
  obtain ⟨y, hyW, hybot⟩ := mem_closure_iff_nhds.mp hxmem _ hW
  have hbotle : (⊥ : Subfield A.valuation.Completion) ≤ (Rat.castHom A.valuation.Completion).fieldRange := bot_le
  obtain ⟨q, hq⟩ := RingHom.mem_fieldRange.mp (hbotle hybot)
  have hyq : (q : A.valuation.Completion) = y := hq
  have hqx : Valued.v ((q : A.valuation.Completion) - xC) < Valued.v ((r : A.valuation.Completion)) := by
    have h : Valued.v.restrict (y - xC) < Valued.v.restrict ((r : A.valuation.Completion)) := by
      simpa only [Set.mem_ofPred_eq, Units.val_mk0] using hyW
    rw [hyq]
    exact lt_of_not_ge fun h' => (not_le.mpr h) ((Valuation.restrict_le_iff _).mpr h')

  have hx1 : Valued.v xC ≤ 1 := hv.map_le_one x
  have hq1 : A.valuation (q : AlgebraicClosure ℚ) ≤ 1 := by
    rw [← v_ratCast]
    have : (q : A.valuation.Completion) = ((q : A.valuation.Completion) - xC) + xC := by ring
    rw [this]
    exact le_trans (Valuation.map_add _ _ _) (max_le (hqx.le.trans hvr1.le) hx1)
  have hcop := den_coprime_of_vA_le_one A hr hA hq1
  obtain ⟨a, ha, w, hw⟩ := exists_nat_sub_mul_den_eq hr.pos q hcop 1
  rw [pow_one] at ha
  have hqa : Valued.v ((q : A.valuation.Completion) - (a : A.valuation.Completion)) ≤
      Valued.v ((r : A.valuation.Completion)) := by
    have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
    have key : (q - a : ℚ) = (r : ℚ) * w / q.den := by
      rw [eq_div_iff hden]; rw [pow_one] at hw; exact hw
    have hc : ((q : A.valuation.Completion) - (a : A.valuation.Completion)) = ((q - a : ℚ) : A.valuation.Completion) := by
      push_cast; rfl
    rw [hc, v_ratCast, key, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast, Rat.cast_natCast,
      map_div₀, map_mul, vA_natCast_eq_one_of_coprime A hA hcop, div_one, ← v_natCast]
    exact mul_le_of_le_one_right zero_le (vA_intCast_le_one A w)
  have hax : Valued.v ((a : A.valuation.Completion) - xC) ≤ Valued.v ((r : A.valuation.Completion)) := by
    have : ((a : A.valuation.Completion) - xC) = ((q : A.valuation.Completion) - xC) - ((q : A.valuation.Completion) - a) := by
      ring
    rw [this]
    exact le_trans (Valuation.map_sub _ _ _) (max_le hqx.le hqa)
  refine ⟨a, ha, Valuation.Integers.dvd_of_le hv ?_⟩
  rw [v_varpi, algebraMap_O_apply, vK_apply]
  convert hax using 2
  rfl

theorem eq_of_varpi_dvd_sub (hr : r.Prime) (hA : A.LiesOverPrime r) {a b : ℕ} (ha : a < r) (hb : b < r)
    (h : varpi A hr hA ∣ ((a : ℕ) : ↥(O A)) - ((b : ℕ) : ↥(O A))) : a = b := by
  have hv := integers A
  by_contra hab
  have hle := Valuation.Integers.le_of_dvd hv h
  rw [v_varpi, algebraMap_O_apply, vK_apply] at hle
  push_cast at hle

  have hval : Valued.v ((a : A.valuation.Completion) - (b : A.valuation.Completion))
      = A.valuation (((a : ℤ) - b : ℤ) : AlgebraicClosure ℚ) := by
    rw [← Rat.cast_natCast (a), ← Rat.cast_natCast (b), ← Rat.cast_sub, v_ratCast]
    push_cast; rfl
  rw [hval] at hle
  have hnd : ¬ r ∣ ((a : ℤ) - b).natAbs := by
    intro hdvd
    have hlt : ((a : ℤ) - b).natAbs < r := by omega
    have hpos : 0 < ((a : ℤ) - b).natAbs := by omega
    exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt)
  have h1 : A.valuation (((a : ℤ) - b : ℤ) : AlgebraicClosure ℚ) = 1 := by
    have h := vA_natCast_eq_one_of_not_dvd A hr hA hnd
    have hcast : ((((a : ℤ) - b).natAbs : ℕ) : AlgebraicClosure ℚ) = ((((a : ℤ) - b).natAbs : ℤ) : AlgebraicClosure ℚ) :=
      (Int.cast_natCast _).symm
    rcases Int.natAbs_eq ((a : ℤ) - b) with hn | hn
    · rw [hn, ← hcast]; exact h
    · rw [hn, Int.cast_neg, Valuation.map_neg, ← hcast]; exact h
  rw [h1] at hle
  exact absurd (v_natCast_lt_one A hr hA) (not_lt.mpr hle)

/--
@isnad1 id=bijectiv.2h2v.s20.7dce0e0a772c from=translated src=- shape=dba3d83e vocab=e652fcb7
-/
theorem bijective_quotient (hr : r.Prime) (hA : A.LiesOverPrime r) :
    Function.Bijective (fun a : Fin r => Ideal.Quotient.mk (Ideal.span {varpi A hr hA}) (((a : ℕ) : ↥(O A)))) := by
  constructor
  · intro a b hab
    apply Fin.ext
    have h := (Ideal.Quotient.eq.mp hab)
    rw [Ideal.mem_span_singleton] at h
    exact eq_of_varpi_dvd_sub A hr hA a.2 b.2 h
  · intro c
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨a, ha, hdvd⟩ := exists_nat_lt_varpi_dvd_sub A hr hA x
    exact ⟨⟨a, ha⟩, (Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr hdvd))⟩

end M

end ValuationSubring.DVRkit

open ValuationSubring.DVRkit in

/--
@isnad1 id=and.1h2v.s18.8810864910b5 from=translated src=- shape=ba0cd517 vocab=05cd1f8a
-/
theorem solution
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    (⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩ : ↥(ratClosure A)) ∈ (Valued.v.comap (ratClosure A).subtype).valuationSubring ∧
    IsDiscreteValuationRing ↥(Valued.v.comap (ratClosure A).subtype).valuationSubring ∧
    (∀ h : (⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩ : ↥(ratClosure A)) ∈ (Valued.v.comap (ratClosure A).subtype).valuationSubring,
      Irreducible (⟨(⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩ : ↥(ratClosure A)), h⟩ : ↥(Valued.v.comap (ratClosure A).subtype).valuationSubring) ∧
      Finite (↥(Valued.v.comap (ratClosure A).subtype).valuationSubring ⧸ Ideal.span {(⟨(⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩ : ↥(ratClosure A)), h⟩ : ↥(Valued.v.comap (ratClosure A).subtype).valuationSubring)}) ∧
      Nat.card (↥(Valued.v.comap (ratClosure A).subtype).valuationSubring ⧸ Ideal.span {(⟨(⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩ : ↥(ratClosure A)), h⟩ : ↥(Valued.v.comap (ratClosure A).subtype).valuationSubring)}) = r) := by
  have hrp : r.Prime := Fact.out
  refine ⟨natCast_mem_O A hrp hA, isDiscreteValuationRing_O A hrp hA, fun h => ⟨irreducible_varpi A hrp hA, ?_, ?_⟩⟩
  · exact Finite.of_surjective _ (bijective_quotient A hrp hA).2
  · have hc := Nat.card_eq_of_bijective _ (bijective_quotient A hrp hA)
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hc
    exact hc.symm
