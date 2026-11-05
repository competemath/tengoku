/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Config.MeetEquations
import Tengoku.AclGeom.AclGeom.Geometry.Representatives

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The meets `G`, `H`, `I` and `E` after normalizing `P` and `Q`

Let `a, b, c, d, x` be independent and let `η ∈ k`.  Translating by `η` gives the shifted table
coordinates `b' = b - η` and `d' = d + (c - 1) η`, with `a`, `c` and `x` unchanged.  Then
`b' c + d' = b c + d - η`, `a x + b' = a x + b - η` and `c (a x + b') + d' = c (a x + b) + d - η`,
so the points `P`, `R`, `Y` and `Z` of the table keep their closures.

* `algebraicIndependent_table_Q_shift`: the shifted coordinates are again independent.
* `racl_shifted_G_H_I_E_of_normalized_P_Q`: if `acl(p) = acl(b)`, `acl(q) = acl(d')` and
  `acl(r) = acl(b c + d)`, then points `g, h, i, e`, not algebraic over `k`, with the incidences
  of the meets `G = (P ∨ T) ∧ (Q ∨ R)`, `H = (U ∨ G) ∧ A`, `I = (H ∨ X) ∧ (P ∨ Y)` and
  `E = (T ∨ Y) ∧ (Q ∨ Z)` of `Ψ` are the shifted table entries `b' c`, `a / b'`, `a x / b'` and
  `c (a x + b')`.

The meets are the soundness meets `qWitness_meet_G`, `qWitness_meet_H`, `qWitness_meet_I` and
`qWitness_meet_E` of the shifted table, reused verbatim.  The meet `H` uses the plane
`A = acl(a, b)`, which the shift does not change.  The second theorem is conditional on the
normalized `P`, `Q` and `R`; it makes no uniqueness or common-shift claim.

**Status:** conditional `G/H/I/E` normalization proved (#27, P3b), with no ACF hypothesis.
The actual PRIVATE 274-line two-family consumer derives `P`, `D/F/R` and `Q` before these
four rows and final independence, under explicit base/ambient ACF, supplied fresh INPUT families,
strong `Q`-producer non-memberships and raw `I/E` incidences/nonconstancy. Both original curves
precede all corresponding inputs; no normal-form or output-freshness oracle. An actual PRIVATE
zero-origin example uses arbitrary raw representatives with no ACF. The initial action chart,
actual guarded-`Ψ` input derivation, input existence/enlargement/descent, combined generator
presentation, actions, extraction and completeness remain open; #11 and frozen117 are independent.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Translating `b` and `d` by a constant** (#27).  If `a, b, c, d, x` are independent and
`η ∈ k`, then so are `a`, `b - η`, `c`, `d + (c - 1) η` and `x`: the change of coordinates is
triangular with an inverse of the same form.
@isnad1 id=algebrai.1h8v.s8.7e79550256d5 from=translated src=- shape=701af912 vocab=712cc3a0
-/
theorem algebraicIndependent_table_Q_shift {a b c d x : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x]) (η : k) :
    AlgebraicIndependent k ![a, b - algebraMap k K η,
      c, d + (c - 1) * algebraMap k K η, x] := by
  obtain ⟨t, ht⟩ : ∃ t, algebraMap k K η = t := ⟨_, rfl⟩
  rw [ht]
  have htS (S : Set K) : t ∈ racl k S := by
    rw [← ht]
    exact (racl k S).algebraMap_mem η
  refine AlgebraicIndependent.of_racl_range_eq hind (racl_range_eq_of_mem ?_ ?_)
  · have hm (i : Fin 5) : ![a, b, c, d, x] i ∈ racl k (Set.range ![a, b, c, d, x]) :=
      subset_racl k _ ⟨i, rfl⟩
    intro i
    fin_cases i
    · exact hm 0
    · exact sub_mem (hm 1) (htS _)
    · exact hm 2
    · exact add_mem (hm 3) (mul_mem (sub_mem (hm 2) (one_mem _)) (htS _))
    · exact hm 4
  · have hm (i : Fin 5) : ![a, b - t, c, d + (c - 1) * t, x] i ∈
        racl k (Set.range ![a, b - t, c, d + (c - 1) * t, x]) :=
      subset_racl k _ ⟨i, rfl⟩
    intro i
    fin_cases i
    · exact hm 0
    · change b ∈ _
      have h := add_mem (hm 1) (htS _)
      change b - t + t ∈ _ at h
      rwa [sub_add_cancel] at h
    · exact hm 2
    · change d ∈ _
      have h := sub_mem (hm 3) (mul_mem (sub_mem (hm 2) (one_mem _)) (htS _))
      change d + (c - 1) * t - (c - 1) * t ∈ _ at h
      rwa [add_sub_cancel_right] at h
    · exact hm 4

end

end AclGeom
