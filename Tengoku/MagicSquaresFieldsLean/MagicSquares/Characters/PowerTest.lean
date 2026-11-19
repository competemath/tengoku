import Tengoku.MagicSquaresFieldsLean.MagicSquares.Characters.PowerIndicator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Algorithm 1, nonzero case.** The exact finite-field power membership
test uses one exponentiation, with exponent `(q-1)/gcd(n,q-1)`.
@isnad1 id=iff.2h3v.s6.93a6af44b03a from=translated src=- shape=433b835d vocab=4b4df0a4
-/
theorem isNthPower_iff_pow_card_sub_one_div_eq_one {n : ℕ} (hn : 0 < n)
    {x : F} (hx : x ≠ 0) :
    IsNthPower n x ↔ x ^ ((Fintype.card F - 1) / powerIndex n (Fintype.card F)) = 1 := by
  let q := Fintype.card F
  let d := powerIndex n q
  let c := (q - 1) / d
  have hd : 0 < d := powerIndex_pos hn
  have hq : 0 < q - 1 := Nat.sub_pos_of_lt Fintype.one_lt_card
  have hdvd : d ∣ q - 1 := Nat.gcd_dvd_right n (q - 1)
  have hc : 0 < c := Nat.div_pos (Nat.le_of_dvd hq hdvd) hd
  have hmul : d * c = q - 1 := Nat.mul_div_cancel' hdvd
  obtain ⟨chi, hchi⟩ := MulChar.exists_mulChar_orderOf F hdvd
    (Complex.isPrimitiveRoot_exp d hd.ne')
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hgorder : orderOf g = q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      Fintype.card_units]
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (Units.mk0 x hx) g).mp
    (mem_powers_iff_mem_zpowers.mpr (hg (Units.mk0 x hx)))
  have hxg : (g : F) ^ k = x := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_mk0] using
      congrArg (fun u : Fˣ => (u : F)) hk
  let ev : MulChar F ℂ →* ℂ :=
    { toFun := fun tau => tau (g : F)
      map_one' := MulChar.one_apply_coe g
      map_mul' := fun _ _ => rfl }
  have hevinj : Function.Injective ev := fun tau psi he => (MulChar.eq_iff hg tau psi).mpr he
  have horder : orderOf (chi (g : F)) = d :=
    (orderOf_injective ev hevinj chi).trans hchi
  have hleft : IsNthPower n x ↔ d ∣ k := by
    rw [← mulChar_eq_one_iff_nthPower hn chi hchi hx,
      ← hxg, map_pow, ← orderOf_dvd_iff_pow_eq_one, horder]
  have hright : x ^ c = 1 ↔ g ^ (k * c) = 1 := by
    constructor
    · intro h
      apply Units.ext
      simpa only [Units.val_pow_eq_pow_val, Units.val_one, pow_mul, hxg] using h
    · intro h
      have hh := congrArg (fun u : Fˣ => (u : F)) h
      simpa only [Units.val_pow_eq_pow_val, Units.val_one, pow_mul, hxg] using hh
  change IsNthPower n x ↔ x ^ c = 1
  rw [hleft, hright, ← orderOf_dvd_iff_pow_eq_one, hgorder, ← hmul]
  exact (Nat.mul_dvd_mul_iff_right hc).symm

/-- **Algorithm 1**, including the convention that zero is a power.
@isnad1 id=iff.1h3v.s6.29f618e76fae from=translated src=- shape=5a4b6635 vocab=4b4df0a4
-/
theorem isNthPower_iff_zero_or_pow_eq_one {n : ℕ} (hn : 0 < n) (x : F) :
    IsNthPower n x ↔ x = 0 ∨
      x ^ ((Fintype.card F - 1) / powerIndex n (Fintype.card F)) = 1 := by
  by_cases hx : x = 0
  · subst x
    exact iff_of_true ⟨0, zero_pow hn.ne'⟩ (Or.inl rfl)
  · simp only [hx, false_or]
    exact isNthPower_iff_pow_card_sub_one_div_eq_one hn hx

end MagicSquares
