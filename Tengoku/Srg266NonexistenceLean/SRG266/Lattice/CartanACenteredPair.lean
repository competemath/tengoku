/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.CartanADualMinimum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

/--
@isnad1 id=eq.2h5v.s7.34a0dd445835 from=translated src=- shape=6df285fd vocab=e1335c0a
-/
theorem centered_integer_pair_identity {ι : Type*} [Fintype ι] [Nonempty ι]
    (z w : ι → ℤ) (a b : ℤ) (hz : (∑ i, z i) = a) (hw : (∑ i, w i) = b) :
    (∑ i, ((z i : ℚ)-(a : ℚ)/Fintype.card ι)*
      ((w i : ℚ)-(b : ℚ)/Fintype.card ι)) =
      ((∑ i, z i*w i : ℤ) : ℚ)-(a : ℚ)*b/Fintype.card ι := by
  have hn : (Fintype.card ι : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hzQ : (∑ i, (z i : ℚ)) = (a : ℚ) := by exact_mod_cast hz
  have hwQ : (∑ i, (w i : ℚ)) = (b : ℚ) := by exact_mod_cast hw
  have hp (s t : ℚ) : (s-(a : ℚ)/Fintype.card ι)*(t-(b : ℚ)/Fintype.card ι) =
      s*t-((b : ℚ)/Fintype.card ι)*s-((a : ℚ)/Fintype.card ι)*t+
        (a : ℚ)*b/(Fintype.card ι)^2 := by ring
  simp_rw [hp]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [hzQ, hwQ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  field_simp
  ring

end SRG266.Lattice
