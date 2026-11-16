import Tengoku.Seed.FieldTheory.PurelyInseparable.Basic
import Tengoku.Seed.FieldTheory.SeparableClosure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_IsSeparable_of_coprime_finrank_expChar.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_IsSeparable_of_coprime_finrank_expChar

set_option autoImplicit false

/--
@isnad1 id=issepara.1h3v.s6.ef352511aefb from=translated src=- shape=3c4f3d6f vocab=b8bfdb3c
-/
theorem solution (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (q : ℕ) [ExpChar F q] (h : Nat.Coprime (Module.finrank F E) q) :
    Algebra.IsSeparable F E := by
  rw [← Field.finSepDegree_eq_finrank_iff]

  haveI : ExpChar (separableClosure F E) q :=
    expChar_of_injective_algebraMap (algebraMap F (separableClosure F E)).injective q
  haveI : IsPurelyInseparable (separableClosure F E) E := separableClosure.isPurelyInseparable F E
  obtain ⟨n, hn⟩ := IsPurelyInseparable.finrank_eq_pow (separableClosure F E) E q
  have hins : Field.finInsepDegree F E = q ^ n := hn
  have hmul := Field.finSepDegree_mul_finInsepDegree F E
  rw [hins] at hmul

  have hdvd : q ^ n ∣ Module.finrank F E := ⟨Field.finSepDegree F E, by rw [mul_comm]; exact hmul.symm⟩
  have hone : q ^ n = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left n h.symm) hdvd
  rw [hone, mul_one] at hmul
  exact hmul
