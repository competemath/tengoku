import Tengoku.MagicSquaresFieldsLean.MagicSquares.Characters.PowerIndicator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Lemma 12.1.** The sign obstruction expressed in terms of the power index.
@isnad1 id=iff.2h2v.s6.80a6f14647c9 from=translated src=- shape=a029351f vocab=9eff8556
-/
theorem isNthPower_neg_one_iff_powerIndex_dvd_half {n : ℕ} (hn : 0 < n)
    (hodd : ringChar F ≠ 2) :
    IsNthPower n (-1 : F) ↔ powerIndex n (Fintype.card F) ∣ (Fintype.card F - 1) / 2 := by
  let q := Fintype.card F
  let d := powerIndex n q
  have hd : 0 < d := powerIndex_pos hn
  obtain ⟨chi, hchi⟩ := MulChar.exists_mulChar_orderOf F
    (Nat.gcd_dvd_right n (q - 1)) (Complex.isPrimitiveRoot_exp d hd.ne')
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hgorder : orderOf g = q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      Fintype.card_units]
  have hq2 : 1 < q := Fintype.one_lt_card
  have hqodd : q % 2 = 1 := FiniteField.odd_card_of_char_ne_two hodd
  have hhalf : (q - 1) / 2 * 2 = q - 1 := by omega
  have hpow : ((g : F) ^ ((q - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul, hhalf]
    exact FiniteField.pow_card_sub_one_eq_one _ g.ne_zero
  have hneg : (g : F) ^ ((q - 1) / 2) = -1 := by
    rw [pow_two] at hpow
    rcases mul_self_eq_one_iff.mp hpow with h | h
    · have hu : g ^ ((q - 1) / 2) = 1 := by
        apply Units.ext
        simpa only [Units.val_pow_eq_pow_val, Units.val_one] using h
      have hdvd := orderOf_dvd_of_pow_eq_one hu
      rw [hgorder] at hdvd
      have hpos : 0 < (q - 1) / 2 := by omega
      have hle := Nat.le_of_dvd hpos hdvd
      omega
    · exact h
  let ev : MulChar F ℂ →* ℂ :=
    { toFun := fun tau => tau (g : F)
      map_one' := MulChar.one_apply_coe g
      map_mul' := fun _ _ => rfl }
  have hevinj : Function.Injective ev := fun tau psi he => (MulChar.eq_iff hg tau psi).mpr he
  have horder : orderOf (chi (g : F)) = d :=
    (orderOf_injective ev hevinj chi).trans hchi
  rw [← mulChar_eq_one_iff_nthPower hn chi hchi (neg_ne_zero.mpr one_ne_zero),
    ← hneg, map_pow, ← orderOf_dvd_iff_pow_eq_one, horder]

end MagicSquares
