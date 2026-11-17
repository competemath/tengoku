import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HahnSeries_RamificationBound

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HahnSeries_hasRamBound_one_of_forall_ringEquiv_apply_eq.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`, 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HahnSeries_hasRamBound_one_of_forall_ringEquiv_apply_eq

set_option maxHeartbeats 3200000

namespace HahnSeries
export _root_.HahnSeries (support orderTop support_eq_empty_iff isPWO_support order mem_support coeff_mul coeff coeff_one coeff_zero map orderTop_of_ne_zero coeff_add isPWO_support' HasRamBound)
namespace PuiseuxTwist
open _root_.HahnSeries

variable {K : Type*} [Field K]

def twist (χ : Multiplicative ℚ →* Kˣ) (x : HahnSeries ℚ K) : HahnSeries ℚ K where
  coeff q := (χ (Multiplicative.ofAdd q) : K) * x.coeff q
  isPWO_support' := x.isPWO_support.mono (by
    intro q hq
    rw [Function.mem_support] at hq
    rw [HahnSeries.mem_support]
    intro h
    exact hq (by rw [h, mul_zero]))

/--
@isnad1 id=eq.0h4v.s8.d9e43f60e64b from=translated src=- shape=7111beed vocab=0510ebc3
-/
@[scoped simp] theorem coeff_twist (χ : Multiplicative ℚ →* Kˣ) (x : HahnSeries ℚ K) (q : ℚ) :
    (twist χ x).coeff q = (χ (Multiplicative.ofAdd q) : K) * x.coeff q := rfl

/--
@isnad1 id=eq.0h3v.s6.d45d0dd2b780 from=translated src=- shape=d7d8499a vocab=f4b43d67
-/
theorem support_twist (χ : Multiplicative ℚ →* Kˣ) (x : HahnSeries ℚ K) :
    (twist χ x).support = x.support := by
  ext q
  rw [HahnSeries.mem_support, HahnSeries.mem_support, coeff_twist]
  constructor
  · intro h hx
    exact h (by rw [hx, mul_zero])
  · intro h hx
    exact h ((mul_eq_zero.mp hx).resolve_left (Units.ne_zero _))

/--
@isnad1 id=eq.0h4v.s8.4eb2b773538b from=translated src=- shape=fe67b309 vocab=c8d33c5e
-/
theorem twist_add (χ : Multiplicative ℚ →* Kˣ) (x y : HahnSeries ℚ K) :
    twist χ (x + y) = twist χ x + twist χ y := by
  ext q
  simp only [coeff_twist, HahnSeries.coeff_add, mul_add]

/--
@isnad1 id=eq.0h2v.s7.6790e8db395e from=translated src=- shape=1c8b2f08 vocab=1c6aa64c
-/
theorem twist_one (χ : Multiplicative ℚ →* Kˣ) : twist χ (1 : HahnSeries ℚ K) = 1 := by
  ext q
  simp only [coeff_twist, HahnSeries.coeff_one]
  split_ifs with h
  · subst h
    rw [ofAdd_zero, map_one, Units.val_one, one_mul]
  · rw [mul_zero]

open Finset in
/--
@isnad1 id=eq.0h4v.s8.1972bbc2e434 from=translated src=- shape=fe67b309 vocab=aab9105a
-/
theorem twist_mul (χ : Multiplicative ℚ →* Kˣ) (x y : HahnSeries ℚ K) :
    twist χ (x * y) = twist χ x * twist χ y := by
  ext a
  rw [coeff_twist, HahnSeries.coeff_mul, HahnSeries.coeff_mul, Finset.mul_sum]
  have hset : antidiagonal (twist χ x).isPWO_support (twist χ y).isPWO_support a
      = antidiagonal x.isPWO_support y.isPWO_support a := by
    ext ij
    simp only [Finset.mem_antidiagonal, support_twist]
  rw [hset]
  refine Finset.sum_congr rfl (fun ij hij => ?_)
  rw [Finset.mem_antidiagonal] at hij
  obtain ⟨-, -, hsum⟩ := hij
  simp only [coeff_twist]
  rw [← hsum, ofAdd_add, map_mul, Units.val_mul]
  ring

def twistRingHom (χ : Multiplicative ℚ →* Kˣ) : HahnSeries ℚ K →+* HahnSeries ℚ K where
  toFun := twist χ
  map_one' := twist_one χ
  map_mul' := twist_mul χ
  map_zero' := by ext q; simp only [coeff_twist, HahnSeries.coeff_zero, mul_zero]
  map_add' := twist_add χ

/--
@isnad1 id=eq.2h3v.s8.e8f2e0603586 from=translated src=- shape=8b3400c5 vocab=7970761e
-/
theorem twist_eq_self_of_hasRamBound_one {χ : Multiplicative ℚ →* Kˣ}
    (hχ : ∀ k : ℤ, χ (Multiplicative.ofAdd (k : ℚ)) = 1) {z : HahnSeries ℚ K}
    (hz : HahnSeries.HasRamBound 1 z) : twist χ z = z := by
  ext q
  rw [coeff_twist]
  by_cases hq : q ∈ z.support
  · obtain ⟨k, hk⟩ := hz hq
    simp only [Nat.cast_one, div_one] at hk
    rw [← hk, hχ k, Units.val_one, one_mul]
  · rw [HahnSeries.mem_support, not_not] at hq
    rw [hq, mul_zero]

section Character

variable [IsAlgClosed K] (ζ : Kˣ)

noncomputable def rootSeq : ℕ → Kˣ
  | 0 => ζ
  | m + 1 =>
    Units.mk0 (Classical.choose (IsAlgClosed.exists_pow_nat_eq ((rootSeq m : Kˣ) : K) m.succ_pos))
      (by
        intro h0
        have h := Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq ((rootSeq m : Kˣ) : K) m.succ_pos)
        rw [h0, zero_pow (Nat.succ_ne_zero m)] at h
        exact (rootSeq m).ne_zero h.symm)

/--
@isnad1 id=eq.0h2v.s5.e342b8614b95 from=translated src=- shape=cf7c878d vocab=8256e341
-/
theorem rootSeq_zero : rootSeq ζ 0 = ζ := rfl

/--
@isnad1 id=eq.0h3v.s7.e232372224ca from=translated src=- shape=7220e300 vocab=4cc49abf
-/
theorem rootSeq_succ_pow (m : ℕ) : (rootSeq ζ (m + 1)) ^ (m + 1) = rootSeq ζ m := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  show (Classical.choose (IsAlgClosed.exists_pow_nat_eq ((rootSeq ζ m : Kˣ) : K) m.succ_pos)) ^ (m+1) = _
  exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq ((rootSeq ζ m : Kˣ) : K) m.succ_pos)

/--
@isnad1 id=eq.0h4v.s7.2eeb737db476 from=translated src=- shape=5598159f vocab=20bb5b6d
-/
theorem rootSeq_add_pow (m j : ℕ) :
    (rootSeq ζ (m + j)) ^ ((m + j).factorial / m.factorial) = rootSeq ζ m := by
  induction j with
  | zero => simp [Nat.div_self (Nat.factorial_pos m)]
  | succ j ih =>
    rw [← add_assoc, Nat.factorial_succ, Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial (Nat.le_add_right m j)),
      pow_mul, rootSeq_succ_pow, ih]

/--
@isnad1 id=eq.1h4v.s7.b0dd89d727e3 from=translated src=- shape=92804ee3 vocab=b07532e4
-/
theorem rootSeq_pow_of_le {m M : ℕ} (h : m ≤ M) :
    (rootSeq ζ M) ^ (M.factorial / m.factorial) = rootSeq ζ m := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  exact rootSeq_add_pow ζ m j

variable (b : ℕ)

noncomputable def charFun (x : ℚ) : Kˣ :=
  (rootSeq ζ x.den) ^ (x.num * (((b * x.den.factorial) / x.den : ℕ) : ℤ))

variable {b}

/--
@isnad1 id=eq.1h6v.s7.fa70571e1fa8 from=translated src=- shape=44513b78 vocab=d94ff986
-/
theorem charFun_eq (x : ℚ) (m : ℕ) (k : ℤ) (hk : x * ((b * m.factorial : ℕ) : ℚ) = k) :
    charFun ζ b x = (rootSeq ζ m) ^ k := by
  have hd0 : x.den ≠ 0 := x.den_nz
  have hdvd : x.den ∣ x.den.factorial := Nat.dvd_factorial x.den_pos le_rfl

  rw [charFun, ← rootSeq_pow_of_le ζ (Nat.le_add_right x.den m),
    ← rootSeq_pow_of_le ζ (Nat.le_add_left m x.den),
    ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
  congr 1

  apply mul_left_cancel₀ (show (x.den : ℤ) ≠ 0 by exact_mod_cast hd0)
  have e1 : (((x.den + m).factorial / x.den.factorial : ℕ) : ℤ) * (x.den.factorial : ℤ)
      = ((x.den + m).factorial : ℤ) := by
    exact_mod_cast Nat.div_mul_cancel (Nat.factorial_dvd_factorial (Nat.le_add_right x.den m))
  have e2 : (((b * x.den.factorial) / x.den : ℕ) : ℤ) * (x.den : ℤ) = b * x.den.factorial := by
    exact_mod_cast Nat.div_mul_cancel (Dvd.dvd.mul_left hdvd b)
  have e3 : (((x.den + m).factorial / m.factorial : ℕ) : ℤ) * (m.factorial : ℤ) = ((x.den + m).factorial : ℤ) := by
    exact_mod_cast Nat.div_mul_cancel (Nat.factorial_dvd_factorial (Nat.le_add_left m x.den))

  have e4 : (k : ℤ) * x.den = x.num * (b * m.factorial : ℕ) := by
    have hq : (k : ℚ) * x.den = x.num * (b * m.factorial : ℕ) := by
      rw [← hk, mul_right_comm, Rat.mul_den_eq_num]
    exact_mod_cast hq
  calc (x.den : ℤ) * ((((x.den + m).factorial / x.den.factorial : ℕ) : ℤ)
          * (x.num * (((b * x.den.factorial) / x.den : ℕ) : ℤ)))
      = x.num * ((((b * x.den.factorial) / x.den : ℕ) : ℤ) * x.den)
          * (((x.den + m).factorial / x.den.factorial : ℕ) : ℤ) := by ring
    _ = x.num * (b * x.den.factorial) * (((x.den + m).factorial / x.den.factorial : ℕ) : ℤ) := by rw [e2]
    _ = x.num * b * ((((x.den + m).factorial / x.den.factorial : ℕ) : ℤ) * x.den.factorial) := by ring
    _ = x.num * b * ((x.den + m).factorial : ℤ) := by rw [e1]
    _ = x.num * b * ((((x.den + m).factorial / m.factorial : ℕ) : ℤ) * m.factorial) := by rw [e3]
    _ = (x.num * (b * m.factorial : ℕ)) * (((x.den + m).factorial / m.factorial : ℕ) : ℤ) := by
          push_cast; ring
    _ = (k * x.den) * (((x.den + m).factorial / m.factorial : ℕ) : ℤ) := by rw [e4]
    _ = (x.den : ℤ) * ((((x.den + m).factorial / m.factorial : ℕ) : ℤ) * k) := by ring

/--
@isnad1 id=ex.1h3v.s5.b60341166f42 from=translated src=- shape=0e22853c vocab=defed4c6
-/
theorem exists_int_eq (b : ℕ) (x : ℚ) (m : ℕ) (hm : x.den ∣ m.factorial) :
    ∃ k : ℤ, x * ((b * m.factorial : ℕ) : ℚ) = k := by
  obtain ⟨c, hc⟩ := Dvd.dvd.mul_left hm b
  refine ⟨x.num * c, ?_⟩
  rw [hc]
  push_cast
  rw [← mul_assoc, Rat.mul_den_eq_num]

variable (b)

noncomputable def char : Multiplicative ℚ →* Kˣ where
  toFun q := charFun ζ b (Multiplicative.toAdd q)
  map_one' := by
    show charFun ζ b 0 = 1
    rw [charFun_eq ζ 0 0 0 (by simp), zpow_zero]
  map_mul' x y := by
    show charFun ζ b (Multiplicative.toAdd x + Multiplicative.toAdd y)
      = charFun ζ b (Multiplicative.toAdd x) * charFun ζ b (Multiplicative.toAdd y)
    have hm0 : 0 < (Multiplicative.toAdd x).den * (Multiplicative.toAdd y).den :=
      Nat.pos_of_ne_zero (Nat.mul_ne_zero (Multiplicative.toAdd x).den_nz (Multiplicative.toAdd y).den_nz)
    have hfac : (Multiplicative.toAdd x).den * (Multiplicative.toAdd y).den ∣
        ((Multiplicative.toAdd x).den * (Multiplicative.toAdd y).den).factorial :=
      Nat.dvd_factorial hm0 le_rfl
    have hu : (Multiplicative.toAdd x).den ∣
        ((Multiplicative.toAdd x).den * (Multiplicative.toAdd y).den).factorial :=
      (Dvd.intro _ rfl).trans hfac
    have hv : (Multiplicative.toAdd y).den ∣
        ((Multiplicative.toAdd x).den * (Multiplicative.toAdd y).den).factorial :=
      (Dvd.intro_left _ rfl).trans hfac
    have huv : (Multiplicative.toAdd x + Multiplicative.toAdd y).den ∣
        ((Multiplicative.toAdd x).den * (Multiplicative.toAdd y).den).factorial :=
      (Rat.add_den_dvd _ _).trans hfac
    obtain ⟨ku, hku⟩ := exists_int_eq b _ _ hu
    obtain ⟨kv, hkv⟩ := exists_int_eq b _ _ hv
    have hkuv : (Multiplicative.toAdd x + Multiplicative.toAdd y)
        * ((b * ((Multiplicative.toAdd x).den * (Multiplicative.toAdd y).den).factorial : ℕ) : ℚ)
        = (ku + kv : ℤ) := by
      rw [add_mul, hku, hkv]
      push_cast
      ring
    rw [charFun_eq ζ _ _ _ hkuv, charFun_eq ζ _ _ _ hku, charFun_eq ζ _ _ _ hkv, zpow_add]

/--
@isnad1 id=eq.0h4v.s7.9cac64559aa4 from=translated src=- shape=1a763adc vocab=211b62e3
-/
theorem char_apply (x : ℚ) : char ζ b (Multiplicative.ofAdd x) = charFun ζ b x := rfl

variable {b}

/--
@isnad1 id=eq.1h4v.s8.e0cf5d78d03a from=translated src=- shape=4d52b7e2 vocab=e5787fd1
-/
theorem char_intCast (hζ : ζ ^ b = 1) (k : ℤ) :
    char ζ b (Multiplicative.ofAdd (k : ℚ)) = 1 := by
  rw [char_apply, charFun_eq ζ (k : ℚ) 0 (k * b) (by push_cast; simp), rootSeq_zero,
    mul_comm, zpow_mul, zpow_natCast, hζ, one_zpow]

/--
@isnad1 id=eq.1h4v.s8.a638bc23bd53 from=translated src=- shape=9b28a1c4 vocab=1049fdc4
-/
theorem char_div (hb : 0 < b) (a : ℤ) :
    char ζ b (Multiplicative.ofAdd ((a : ℚ) / b)) = ζ ^ a := by
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [char_apply, charFun_eq ζ ((a : ℚ) / b) 0 a (by push_cast; simp; field_simp), rootSeq_zero]

end Character

def twistRingEquiv (χ : Multiplicative ℚ →* Kˣ) : HahnSeries ℚ K ≃+* HahnSeries ℚ K where
  toFun := twist χ
  invFun := twist χ⁻¹
  left_inv x := by
    ext q
    rw [coeff_twist, coeff_twist, MonoidHom.inv_apply, ← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by
    ext q
    rw [coeff_twist, coeff_twist, MonoidHom.inv_apply, ← mul_assoc, Units.mul_inv, one_mul]
  map_mul' := twist_mul χ
  map_add' := twist_add χ

/--
@isnad1 id=eq.0h3v.s8.bc8403ecae1b from=translated src=- shape=bc72ba69 vocab=84726da2
-/
@[scoped simp] theorem twistRingEquiv_apply (χ : Multiplicative ℚ →* Kˣ) (x : HahnSeries ℚ K) :
    twistRingEquiv χ x = twist χ x := rfl

/--
@isnad1 id=eq.0h2v.s7.185ba783d59e from=translated src=- shape=1c8b2f08 vocab=1c6aa64c
-/
theorem twist_zero (χ : Multiplicative ℚ →* Kˣ) : twist χ (0 : HahnSeries ℚ K) = 0 :=
  map_zero (twistRingHom χ)

/--
@isnad1 id=eq.0h3v.s6.95a3732e311a from=translated src=- shape=d7d8499a vocab=633c5f56
-/
theorem orderTop_twist (χ : Multiplicative ℚ →* Kˣ) (z : HahnSeries ℚ K) :
    (twist χ z).orderTop = z.orderTop := by
  by_cases hz : z = 0
  · subst hz
    rw [twist_zero]
  · have hz' : twist χ z ≠ 0 := by
      intro h
      apply hz
      rw [← HahnSeries.support_eq_empty_iff] at h ⊢
      rwa [support_twist] at h

    first
      | rw [HahnSeries.orderTop_of_ne_zero hz, HahnSeries.orderTop_of_ne_zero hz', WithTop.coe_eq_coe]
      | rw [HahnSeries.orderTop_of_ne hz, HahnSeries.orderTop_of_ne hz', WithTop.coe_eq_coe]
    apply le_antisymm
    · exact Set.IsWF.min_le _ _ (by rw [support_twist]; exact Set.IsWF.min_mem _ _)
    · exact Set.IsWF.min_le _ _ (by rw [← support_twist χ z]; exact Set.IsWF.min_mem _ _)

end HahnSeries.PuiseuxTwist
open scoped _root_.P2MW.S_HahnSeries_hasRamBound_one_of_forall_ringEquiv_apply_eq.HahnSeries _root_.P2MW.S_HahnSeries_hasRamBound_one_of_forall_ringEquiv_apply_eq.HahnSeries.PuiseuxTwist
open scoped _root_.P2MW.S_HahnSeries_hasRamBound_one_of_forall_ringEquiv_apply_eq.HahnSeries

open HahnSeries.PuiseuxTwist in
/--
@isnad1 id=hasrambo.1h2v.s10.6de34c1a145a from=translated src=- shape=9eacb36c vocab=e3006c25
-/
theorem solution
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {x : HahnSeries ℚ K}
    (hx : ∀ σ : HahnSeries ℚ K ≃+* HahnSeries ℚ K,
      (∀ z : HahnSeries ℚ K, (σ z).orderTop = z.orderTop) →
      (∀ z : HahnSeries ℚ K, HahnSeries.HasRamBound 1 z → σ z = z) → σ x = x) :
    HahnSeries.HasRamBound 1 x := by
  intro q hq
  have hb : 0 < q.den := q.den_pos
  haveI : NeZero q.den := ⟨q.den_nz⟩

  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K q.den
  obtain ⟨ζ, rfl⟩ : IsUnit μ := by
    first | exact hμ.isUnit q.den_nz | exact hμ.isUnit hb
  have hζ : IsPrimitiveRoot ζ q.den := IsPrimitiveRoot.coe_units_iff.mp hμ
  have hζ1 : ζ ^ q.den = 1 := hζ.pow_eq_one

  have hfix : twist (char ζ q.den) x = x := by
    have h := hx (twistRingEquiv (char ζ q.den))
      (fun z => by rw [twistRingEquiv_apply]; exact orderTop_twist _ z)
      (fun z hz => by rw [twistRingEquiv_apply]; exact twist_eq_self_of_hasRamBound_one (char_intCast ζ hζ1) hz)
    rwa [twistRingEquiv_apply] at h

  have hc : ((char ζ q.den (Multiplicative.ofAdd q) : Kˣ) : K) * x.coeff q = x.coeff q := by
    have h := congrArg (fun y : HahnSeries ℚ K => y.coeff q) hfix
    simpa only [coeff_twist] using h
  have hxq : x.coeff q ≠ 0 := by rwa [HahnSeries.mem_support] at hq
  have hc1 : ((char ζ q.den (Multiplicative.ofAdd q) : Kˣ) : K) = 1 :=
    mul_right_cancel₀ hxq (hc.trans (one_mul _).symm)
  have hval : char ζ q.den (Multiplicative.ofAdd q) = ζ ^ q.num := by
    have e : Multiplicative.ofAdd q = Multiplicative.ofAdd ((q.num : ℚ) / (q.den : ℚ)) := by
      rw [Rat.num_div_den]
    rw [e, char_div ζ hb]
  have hpow : ζ ^ q.num = 1 := by
    rw [← hval]
    exact Units.val_eq_one.mp hc1

  have hdvd : (q.den : ℤ) ∣ q.num := (hζ.zpow_eq_one_iff_dvd q.num).mp hpow
  have hdvd' : q.den ∣ q.num.natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr hdvd
    rwa [Int.natAbs_natCast] at h
  have hden : q.den = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm q.reduced) hdvd'
  refine ⟨q.num, ?_⟩
  have h := Rat.num_div_den q
  rw [hden] at h
  simpa only [Nat.cast_one, div_one] using h
