import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Ideal_height_eq_one_iff_mem_minimalPrimes_span_singleton_of_mem.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Ideal_height_eq_one_iff_mem_minimalPrimes_span_singleton_of_mem

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {x : R} (hx : x ≠ 0) (P : Ideal R) [P.IsPrime] (hxP : x ∈ P) :
    P.height = 1 ↔ P ∈ (Ideal.span {x}).minimalPrimes := by
  have hle : Ideal.span {x} ≤ P := (Ideal.span_singleton_le_iff_mem _).mpr hxP
  have hx' : x ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hx
  have hxu : ¬ IsUnit x := fun hu => Ideal.IsPrime.ne_top' (Ideal.eq_top_of_isUnit_mem P hxP hu)
  have hspan : (Ideal.span {x}).height = 1 := Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors hx' hxu
  constructor
  · intro hP
    exact Ideal.mem_minimalPrimes_of_height_le hle (by rw [hP, hspan])
  · intro hP
    apply le_antisymm
    · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) P hP
    · exact hspan ▸ Ideal.height_mono hle
