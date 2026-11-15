import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open scoped NNReal
open HahnSeries

namespace LaurentSeries.XAdic

variable (F : Type*) [Field F]

/--
@isnad1 id=eq.0h1v.s8.76cb0cf802f7 from=translated src=- shape=d6ab1d4c vocab=313d7321
-/
theorem valued_single_one_one :
    (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ)))
        (HahnSeries.single (1 : ℤ) (1 : F))
      = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  simpa [WithZero.exp] using LaurentSeries.valuation_single_zpow (K := F) 1

/--
@isnad1 id=ne.0h1v.s8.c8dc2ed36325 from=translated src=- shape=fe7de9d9 vocab=7bbbce0a
-/
theorem single_one_one_ne_zero : (HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ≠ 0 := by
  intro h
  have hv := valued_single_one_one F
  rw [h, map_zero] at hv
  exact WithZero.zero_ne_coe hv

scoped instance rankOne :
    (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ))).RankOne := by
  haveI hnt : (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨⟨HahnSeries.single (1 : ℤ) (1 : F),
      by rw [valued_single_one_one]; exact WithZero.coe_ne_zero,
      by
        rw [valued_single_one_one]
        intro h
        have h' := Multiplicative.ofAdd.injective (WithZero.coe_inj.mp (h.trans rfl : _ =
          ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))))
        norm_num at h'⟩⟩
  haveI hle : (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ))).RankLeOne :=
    Valuation.RankLeOne.mk
      ((WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0)).comp
        MonoidWithZeroHom.ValueGroup₀.embedding)
      (fun a b hab =>
        WithZeroMulInt.toNNReal_strictMono (by norm_num : (1 : ℝ≥0) < 2)
          (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono hab))
  exact Valuation.RankOne.mk

scoped instance nontriviallyNormedField : NontriviallyNormedField (LaurentSeries F) :=
  Valued.toNontriviallyNormedField (LaurentSeries F) (WithZero (Multiplicative ℤ))

/--
@isnad1 id=isultram.0h1v.s6.d63aee33cd3b from=translated src=- shape=1666ae32 vocab=b20a9f51
-/
scoped instance isUltrametricDist : IsUltrametricDist (LaurentSeries F) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (Valued.isNonarchimedean_norm (LaurentSeries F) (WithZero (Multiplicative ℤ)))

scoped instance (priority := low) decidableEq : DecidableEq (LaurentSeries F) := Classical.decEq _

/--
@isnad1 id=lt.0h1v.s8.7bdb7da3bcb1 from=translated src=- shape=067d7be1 vocab=7c243aae
-/
theorem norm_X_lt_one : ‖(HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F)‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff, valued_single_one_one]
  exact WithZero.coe_lt_coe.mpr (Multiplicative.ofAdd_lt.mpr (by norm_num))

/--
@isnad1 id=lt.0h1v.s8.bc245002b50b from=translated src=- shape=067d7be1 vocab=f2f758fa
-/
theorem nnnorm_X_lt_one : ‖(HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F)‖₊ < 1 := by
  rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
  exact norm_X_lt_one F

/--
@isnad1 id=lt.1h2v.s9.7df5f6e07dff from=translated src=- shape=3f5f4972 vocab=84d98fc4
-/
theorem nnnorm_X_pow_lt_one {N : ℕ} (hN : N ≠ 0) :
    ‖(HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ N‖₊ < 1 := by
  rw [nnnorm_pow]
  exact pow_lt_one₀ zero_le (nnnorm_X_lt_one F) hN

/--
@isnad1 id=ne.0h2v.s8.602746725ba8 from=translated src=- shape=2ad5378e vocab=a73575f8
-/
theorem X_pow_ne_zero (N : ℕ) : (HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ N ≠ 0 :=
  pow_ne_zero N (single_one_one_ne_zero F)

/--
@isnad1 id=charzero.0h1v.s6.864a6c058b39 from=translated src=- shape=d96e9922 vocab=b3843a03
-/
theorem charZero [CharZero F] : CharZero (LaurentSeries F) :=
  charZero_of_injective_ringHom (f := (HahnSeries.C : F →+* LaurentSeries F)) HahnSeries.C_injective

end LaurentSeries.XAdic

end
