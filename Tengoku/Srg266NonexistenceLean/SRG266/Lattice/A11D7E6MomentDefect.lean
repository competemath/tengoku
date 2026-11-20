/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.A11D7E6SecondMoment

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

variable {W U Y : Type*} [AddCommGroup W] [Module ℚ W] [AddCommGroup U] [Module ℚ U]
  [AddCommGroup Y] [Module ℚ Y]

/--
@isnad1 id=eq.2h9v.s12.89612ecb77cf from=translated src=- shape=4a185bab vocab=dd06aeae
-/
theorem marked_product_frame_second_moment {ι : Type*} [Fintype ι]
    (B : LinearMap.BilinForm ℚ W) (C : LinearMap.BilinForm ℚ U)
    (g : ι → W) (s : Fin 7 → ℚ) (a : ℚ)
    (hm : ∀ w, (∑ i, (B w (g i))^2) = a*B w w)
    (r : (W × (Fin 7 → ℚ)) × U) (hr : r.1.2 = 0) :
    (∑ i, (prodForm (prodForm B (standardRatForm 7)) C r ((g i, s), 0))^2) =
      a*(prodForm (prodForm B (standardRatForm 7)) C r r-C r.2 r.2) := by
  simpa only [prodForm_apply, hr, map_zero, LinearMap.zero_apply, add_zero,
    add_sub_cancel_right] using hm r.1.1

end SRG266.Lattice
