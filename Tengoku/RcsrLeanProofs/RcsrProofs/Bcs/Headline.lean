/-
Copyright (c) 2026 Steven Kotlarz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Kotlarz
-/

import Tengoku.RcsrLeanProofs.RcsrProofs.Bcs.Distance
import Tengoku.RcsrLeanProofs.RcsrProofs.Bcs.Assembly
import Tengoku.Seed.Data.Set.Card

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Headline theorem: `shellCard` counts the graph-distance spheres

`Assembly.lean` defines `shellCard n` as a finset cardinality (states in the
boxed slab `[-n,n]³ × Fin 8` with `D s = n`), and proves it splits as the sum
of the eight class-wise counts. This file identifies that finset count with
the actual graph-theoretic object of interest: the *sphere* of radius `n`
around `base` in the `Adj` graph, i.e. the set of states whose least `Adj`-walk
length from `base` is exactly `n`.

The bridge is `dist_is_least` (`D s` *is* the graph distance, as a witnessed
`IsLeast`) together with the box bound `dist_box`, which together show the
sphere coincides on the nose with the finset `shellCard` counts.
-/

namespace Bcs

open Finset

/-- The graph-distance sphere of radius `n`: states `s` whose least walk
length from `base` (i.e. graph distance) is exactly `n`.-/
def sphere (n : ℕ) : Set St := {s | IsLeast {k : ℕ | Walk k s} n}

/-- `s` lies on the sphere of radius `n` iff `(D s).toNat = n`: since
`dist_is_least` already witnesses `(D s).toNat` as *the* least walk length,
and `IsLeast` is unique, any other witnessed least value must agree with it.-/
theorem mem_sphere_iff (n : ℕ) (s : St) : s ∈ sphere n ↔ (D s).toNat = n := by
  constructor
  · intro h
    exact (h.unique (dist_is_least s)).symm
  · rintro rfl
    exact dist_is_least s

/-- The sphere of radius `n`, as a set, equals the coercion of the finset
`shellCard` is counting: the boxed `Fin 8 × box n` slab filtered to `D s = n`.-/
theorem sphere_eq_coe_filter (n : ℕ) :
    sphere n = (((univ : Finset (Fin 8)) ×ˢ box n).filter (fun s => D s = n) : Finset St) := by
  ext s
  simp only [mem_sphere_iff, Finset.coe_filter, Finset.mem_product,
    Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  obtain ⟨v, x, y, z⟩ := s
  constructor
  · intro h
    have hpos : 0 ≤ D (v, x, y, z) := d_nonneg _
    have hDn : D (v, x, y, z) = (n : Int) := by omega
    have hbox := dist_box v x y z n hDn
    refine ⟨?_, hDn⟩
    simp only [box, Finset.mem_product, Finset.mem_Icc]
    obtain ⟨hx, hy, hz⟩ := hbox
    exact ⟨by omega, by omega, by omega⟩
  · rintro ⟨-, hDn⟩
    have : 0 ≤ D (v, x, y, z) := d_nonneg _
    omega

/-- The sphere of radius `n` is finite.-/
theorem sphere_finite (n : ℕ) : (sphere n).Finite := by
  rw [sphere_eq_coe_filter]
  exact Finset.finite_toSet _

/-- **Headline theorem.** The number of states at graph distance exactly `n`
from `base` equals `shellCard n`, the finset count computed in
`Assembly.lean`.-/
theorem sphere_ncard_eq_shellCard (n : ℕ) : Set.ncard (sphere n) = shellCard n := by
  rw [sphere_eq_coe_filter, Set.ncard_coe_finset]
  rfl

/-- **Statement of record.** The number of states at graph distance exactly
`n` from `base` equals the sum of the eight class-wise level-set counts.-/
theorem sphere_ncard_eq_sum (n : ℕ) :
    Set.ncard (sphere n) = ∑ v : Fin 8, classCard v n := by
  rw [sphere_ncard_eq_shellCard, shellCard_eq_sum]

end Bcs
