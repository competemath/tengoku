module

public import Tengoku.Seed.NumberTheory.NumberField.Cyclotomic.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Compatibility helpers for primitive roots as units

These names restore the old `IsPrimitiveRoot.unit'` API in terms of the
current `toInteger_isPrimitiveRoot.isUnit` construction.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped NumberField

namespace IsPrimitiveRoot

noncomputable def unit' {K : Type*} [Field K] [CharZero K] {ζ : K} {k : ℕ}
    [NeZero k] (hζ : IsPrimitiveRoot ζ k) : (𝓞 K)ˣ :=
  (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne k)).unit

/--
@isnad1 id=isprimit.1h3v.s6.a5dea534c528 from=translated src=- shape=8e6e032b vocab=99027ecb
-/
lemma unit'_coe {K : Type*} [Field K] [CharZero K] {ζ : K} {k : ℕ}
    [NeZero k] (hζ : IsPrimitiveRoot ζ k) : IsPrimitiveRoot (hζ.unit' : 𝓞 K) k :=
  hζ.toInteger_isPrimitiveRoot

/--
@isnad1 id=eq.1h3v.s7.23f4c5dc1d78 from=translated src=- shape=b8413e22 vocab=e6dc1791
-/
lemma unit'_pow {K : Type*} [Field K] [CharZero K] {ζ : K} {k : ℕ}
    [NeZero k] (hζ : IsPrimitiveRoot ζ k) : hζ.unit' ^ k = 1 :=
  Units.ext hζ.toInteger_isPrimitiveRoot.pow_eq_one

lemma eq_one_mod_sub_of_pow {A : Type*} [CommRing A] [IsDomain A] {ζ μ : A} {k : ℕ}
    [NeZero k] (hζ : IsPrimitiveRoot ζ k) (hμ : μ ^ k = 1) :
    algebraMap A (A ⧸ Ideal.span ({ζ - 1} : Set A)) μ = 1 := by
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hμ
  rw [← hi, map_pow]
  have hζ_mod : algebraMap A (A ⧸ Ideal.span ({ζ - 1} : Set A)) ζ = 1 := by
    rw [← map_one (algebraMap A (A ⧸ Ideal.span ({ζ - 1} : Set A))), ← sub_eq_zero,
      ← map_sub, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [hζ_mod, one_pow]

end IsPrimitiveRoot

end
