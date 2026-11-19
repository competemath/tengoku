import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterOne.BadParameters
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace Square3

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# What avoiding the nine bad parameters buys us
-/

omit [Fintype F] in
/-- A parameter outside `centerOneBadT b` is nonzero.
@isnad1 id=ne.1h3v.s5.a7fbbe29c5b1 from=translated src=- shape=f324efa8 vocab=527246e6
-/
theorem ne_zero_of_not_mem_centerOneBadT
    {b t : F}
    (ht : t ∉ centerOneBadT b) :
    t ≠ 0 := by
  intro h
  subst t
  exact ht (zero_mem_centerOneBadT b)

omit [Fintype F] [DecidableEq F] in
/-- If the coefficient at a position is nonzero and its corresponding linear
form vanishes, then `t` is the expected bad value `-1/λ`.-/
theorem eq_bad_parameter_of_linear_eq_zero
    {b t : F} {k : Fin 9}
    (hk : centerOneCoeff b k ≠ 0)
    (hzero : 1 + centerOneCoeff b k * t = 0) :
    t = (-1 : F) / centerOneCoeff b k := by
  apply (eq_div_iff hk).2
  linear_combination hzero

omit [Fintype F] in
/-- Outside the bad set, no non-center entry can vanish.
@isnad1 id=ne.3h4v.s7.d9dbfd5d3956 from=translated src=- shape=55c62e8d vocab=563f66a5
-/
theorem centerOne_linear_ne_zero_of_not_bad
    {b t : F}
    (hb : CenterOneGoodB b)
    (ht : t ∉ centerOneBadT b)
    {k : Fin 9}
    (hk : k ≠ 4) :
    1 + centerOneCoeff b k * t ≠ 0 := by
  intro hzero
  have hc : centerOneCoeff b k ≠ 0 :=
    centerOneCoeff_ne_zero_of_good hb hk
  have heq : t = (-1 : F) / centerOneCoeff b k :=
    eq_bad_parameter_of_linear_eq_zero hc hzero
  apply ht
  unfold centerOneBadT
  refine Finset.mem_image.mpr ⟨k, by simp, ?_⟩
  exact heq.symm

end Square3
end MagicSquares
