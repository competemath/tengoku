import Tengoku.MagicSquaresFieldsLean.MagicSquares.Jacobi.Characters
import Tengoku.MagicSquaresFieldsLean.MagicSquares.PowerResidue
import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterOne.PowerIndex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
/-- The kernel of a character of order `d` consists exactly of the
nonzero `d`-th powers.
@isnad1 id=iff.1h3v.s7.e6bb5a56d2bd from=translated src=- shape=6d26aae1 vocab=50272d3b
-/
theorem mulChar_eq_one_iff_power_order (chi : MulChar F ℂ) {x : F} (hx : x ≠ 0) :
    chi x = 1 ↔ IsNthPower (orderOf chi) x := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
    let ev : MulChar F ℂ →* ℂ :=
      { toFun := fun tau => tau (g : F)
        map_one' := MulChar.one_apply_coe g
        map_mul' := fun _ _ => rfl }
    have hevinj : Function.Injective ev := fun tau psi he => (MulChar.eq_iff hg tau psi).mpr he
    have horder : orderOf (chi (g : F)) = orderOf chi := orderOf_injective ev hevinj chi
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (Units.mk0 x hx) g).mp
      (mem_powers_iff_mem_zpowers.mpr (hg (Units.mk0 x hx)))
    have hxg : (g : F) ^ k = x := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_mk0] using
        congrArg (fun u : Fˣ => (u : F)) hk
    have hdvd : orderOf chi ∣ k := by
      rw [← horder]
      exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxg, h])
    refine ⟨(g : F) ^ (k / orderOf chi), ?_⟩
    rw [← pow_mul, Nat.div_mul_cancel hdvd, hxg]
  · rintro ⟨y, rfl⟩
    have hy : y ≠ 0 := by intro h; simp [h, chi.orderOf_pos.ne'] at hx
    rw [map_pow, ← chi.pow_apply' chi.orderOf_pos.ne', pow_orderOf_eq_one]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hy)

omit [DecidableEq F] in
/-- Bézout's identity identifies `n`-th powers with `gcd(n,q-1)`-th
powers in the unit group.
@isnad1 id=iff.2h3v.s6.5a3e63e8522d from=translated src=- shape=e3cb0fd2 vocab=4ceed21c
-/
theorem isNthPower_powerIndex_iff {n : ℕ} (hn : 0 < n) {x : F} (hx : x ≠ 0) :
    IsNthPower (powerIndex n (Fintype.card F)) x ↔ IsNthPower n x := by
  let q := Fintype.card F - 1
  let d := Nat.gcd n q
  have hd : 0 < d := Nat.gcd_pos_of_pos_left q hn
  constructor
  · rintro ⟨y, hy⟩
    change y ^ d = x at hy
    have hy0 : y ≠ 0 := by
      intro he
      rw [he, zero_pow hd.ne'] at hy
      exact hx hy.symm
    let u : Fˣ := Units.mk0 y hy0
    have huq : u ^ q = 1 := by
      apply Units.ext
      exact FiniteField.pow_card_sub_one_eq_one y hy0
    have hbez : u ^ d = (u ^ Nat.gcdA n q) ^ n := by
      rw [← zpow_natCast u d, Nat.gcd_eq_gcd_ab, zpow_add, zpow_mul,
        zpow_mul, zpow_natCast, zpow_natCast, huq, one_zpow, mul_one]
      rw [← zpow_natCast u n, ← zpow_mul,
        ← zpow_natCast (u ^ Nat.gcdA n q) n, ← zpow_mul]
      congr 1
      ring
    refine ⟨((u ^ Nat.gcdA n q : Fˣ) : F), ?_⟩
    have hfield := congrArg (fun v : Fˣ => (v : F)) hbez
    simpa only [Units.val_pow_eq_pow_val, u, Units.val_mk0] using hfield.symm.trans hy
  · rintro ⟨y, rfl⟩
    refine ⟨y ^ (n / d), ?_⟩
    change (y ^ (n / d)) ^ d = y ^ n
    rw [← pow_mul, Nat.div_mul_cancel (Nat.gcd_dvd_left n q)]

omit [DecidableEq F] in
/-- A character of order `gcd(n,q-1)` detects nonzero `n`-th powers.
@isnad1 id=iff.3h4v.s7.3f6f6b185c51 from=translated src=- shape=443b6e41 vocab=1f2d62f9
-/
theorem mulChar_eq_one_iff_nthPower {n : ℕ} (hn : 0 < n) (chi : MulChar F ℂ)
    (horder : orderOf chi = powerIndex n (Fintype.card F)) {x : F} (hx : x ≠ 0) :
    chi x = 1 ↔ IsNthPower n x := by
  rw [mulChar_eq_one_iff_power_order chi hx, horder, isNthPower_powerIndex_iff hn hx]

/-- The unnormalized indicator has weight one at zero and weight `d`
at nonzero powers.-/
noncomputable def powerIndicatorNumerator (n d : ℕ) (x : F) : ℝ :=
  if x = 0 then 1 else if IsNthPower n x then d else 0

/-- Exact geometric-series identity, with the paper's convention that
the zeroth character power is one even at zero.
@isnad1 id=eq.4h5v.s7.fd4a301a26a3 from=translated src=- shape=c0fd2325 vocab=a74891bf
-/
theorem sum_character_powers_eq_indicator
    {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (chi : MulChar F ℂ)
    (horder : orderOf chi = d) (hdgcd : d = powerIndex n (Fintype.card F)) (x : F) :
    (∑ j : Fin d, chi x ^ (j : ℕ)) = (powerIndicatorNumerator n d x : ℂ) := by
  rw [Fin.sum_univ_eq_sum_range]
  by_cases hx : x = 0
  · simp only [hx, MulChar.map_zero, powerIndicatorNumerator, ite_true, Complex.ofReal_one]
    rw [geom_sum_eq (by norm_num : (0 : ℂ) ≠ 1), zero_pow hd.ne']
    norm_num
  · have hroot : chi x ^ d = 1 := by
      rw [← horder, ← chi.pow_apply' chi.orderOf_pos.ne', pow_orderOf_eq_one]
      exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
    have hkernel := mulChar_eq_one_iff_nthPower hn chi (horder.trans hdgcd) hx
    by_cases h : chi x = 1
    · have hpower := hkernel.mp h
      simp [h, powerIndicatorNumerator, hx, hpower]
    · have hpower : ¬ IsNthPower n x := mt hkernel.mpr h
      rw [geom_sum_eq h, hroot]
      simp [powerIndicatorNumerator, hx, hpower]

omit [Fintype F] in
/--
@isnad1 id=le.0h4v.s4.4a06639a8737 from=translated src=- shape=b9165939 vocab=7001e6b7
-/
theorem powerIndicatorNumerator_nonneg (n d : ℕ) (x : F) :
    0 ≤ powerIndicatorNumerator n d x := by
  unfold powerIndicatorNumerator
  split_ifs <;> positivity

omit [Fintype F] in
/--
@isnad1 id=le.1h4v.s5.e314659f4433 from=translated src=- shape=fe6454ea vocab=552e3a17
-/
theorem powerIndicatorNumerator_le {n d : ℕ} (hd : 0 < d) (x : F) :
    powerIndicatorNumerator n d x ≤ d := by
  unfold powerIndicatorNumerator
  split_ifs <;> norm_num
  exact_mod_cast hd

omit [Fintype F] in
/-- Positive indicator weight certifies an actual power, including zero.
@isnad1 id=eq.2h4v.s5.557c6420c8bf from=translated src=- shape=ff9a6010 vocab=39b50ada
-/
theorem powerIndicatorNumerator_eq_zero_of_not_power {n d : ℕ} (hn : 0 < n) {x : F}
    (hx : ¬ IsNthPower n x) : powerIndicatorNumerator n d x = 0 := by
  have hx0 : x ≠ 0 := by
    intro h
    apply hx
    exact ⟨0, by simp [h, hn.ne']⟩
  simp [powerIndicatorNumerator, hx0, hx]

end MagicSquares
