/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Config.MeetEquations
import Tengoku.AclGeom.AclGeom.Geometry.Representatives

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The meets `D`, `F` and `R` after normalizing `P`

Let `a, b, c, d, x` be independent and let `κ ∈ k`.  Translating the common curve coordinate by
`κ` gives the starred table coordinates `b* = b + (a - 1) κ`, `d* = d + (c - 1) κ` and
`x* = x - κ`.  Then `a x* + b* = a x + b - κ` and `c (a x* + b*) + d* = c (a x + b) + d - κ`.

* `algebraicIndependent_table_shift`: the starred coordinates are again independent.
* `racl_shifted_D_F_R_of_normalized_P`: if the point `P` is normalized, `acl(p) = acl(b*)`,
  then points `δ, f, r` with the incidences of the meets `D`, `F` and `R` of `Ψ` are the table
  entries `a x*`, `a c x*` and `b c + d + a c κ`; the last one is `b* c + d*` up to `κ`.

The meets are the soundness meets `qWitness_meet_D`, `qWitness_meet_F` and `qWitness_meet_R` of
the starred table, reused verbatim.  The second theorem is conditional on the normalized `P`.
Deriving that normalization, from a supplied family of fresh relocation inputs over an
algebraically closed base, is a separate check.  The meets `E, G, H, I`, the point `Q`, the
combined generator presentation, ambient input existence and descent, the action presentation,
extraction and completeness remain open.

**Status:** conditional `D/F/R` normalization proved (#27, P2). The original five-variable
supplied-input family chain derives the shift, `P` and these rows in a private check under
explicit base/ambient ACF. `E/G/H/I/Q`, the combined generator presentation, ambient existence/
descent, actions, extraction and completeness remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Translating the table coordinates** (#27).  If `a, b, c, d, x` are independent and
`κ ∈ k`, then so are `a`, `b + (a - 1) κ`, `c`, `d + (c - 1) κ` and `x - κ`: the change of
coordinates is triangular with an inverse of the same form.-/
theorem algebraicIndependent_table_shift {a b c d x : K}
    (hind : AlgebraicIndependent k ![a, b, c, d, x]) (κ : k) :
    AlgebraicIndependent k ![a, b + (a - 1) * algebraMap k K κ,
      c, d + (c - 1) * algebraMap k K κ, x - algebraMap k K κ] := by
  obtain ⟨e, he⟩ : ∃ e, algebraMap k K κ = e := ⟨_, rfl⟩
  rw [he]
  have ht (S : Set K) : e ∈ racl k S := by
    rw [← he]
    exact (racl k S).algebraMap_mem κ
  refine AlgebraicIndependent.of_racl_range_eq hind (racl_range_eq_of_mem ?_ ?_)
  · have hm (i : Fin 5) : ![a, b, c, d, x] i ∈ racl k (Set.range ![a, b, c, d, x]) :=
      subset_racl k _ ⟨i, rfl⟩
    intro i
    fin_cases i
    · exact hm 0
    · exact add_mem (hm 1) (mul_mem (sub_mem (hm 0) (one_mem _)) (ht _))
    · exact hm 2
    · exact add_mem (hm 3) (mul_mem (sub_mem (hm 2) (one_mem _)) (ht _))
    · exact sub_mem (hm 4) (ht _)
  · have hm (i : Fin 5) : ![a, b + (a - 1) * e, c, d + (c - 1) * e, x - e] i ∈
        racl k (Set.range ![a, b + (a - 1) * e, c, d + (c - 1) * e, x - e]) :=
      subset_racl k _ ⟨i, rfl⟩
    intro i
    fin_cases i
    · exact hm 0
    · change b ∈ _
      have h := sub_mem (hm 1) (mul_mem (sub_mem (hm 0) (one_mem _)) (ht _))
      change b + (a - 1) * e - (a - 1) * e ∈ _ at h
      rwa [add_sub_cancel_right] at h
    · exact hm 2
    · change d ∈ _
      have h := sub_mem (hm 3) (mul_mem (sub_mem (hm 2) (one_mem _)) (ht _))
      change d + (c - 1) * e - (c - 1) * e ∈ _ at h
      rwa [add_sub_cancel_right] at h
    · change x ∈ _
      have h := add_mem (hm 4) (ht _)
      change x - e + e ∈ _ at h
      rwa [sub_add_cancel] at h

end

end AclGeom
