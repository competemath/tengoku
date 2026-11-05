/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Closure.ClosedLattice
import Tengoku.Seed.FieldTheory.PurelyInseparable.PerfectClosure
import Tengoku.Seed.FieldTheory.IsPerfectClosure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Perfections and perfected subfields

Following blueprint §type-correct statement and §Foundation III:

* `Perfection K`: a chosen perfect closure of `K`, bundled as a perfect field
  `carrier` with a `p`-radical inclusion `incl : K →+* carrier` satisfying
  `IsPerfectClosure`, uniform in the characteristic exponent (`p = 1` in
  characteristic zero);
* `Perfection.perfSubfield M`: the perfected subfield `M^perf` of a subfield
  `M ≤ K`, with the public membership criterion
  `x ∈ M^perf ↔ ∃ n, ∃ m ∈ M, x ^ p ^ n = incl m`
  (`mem_perfSubfield_iff`), monotonicity, and the pullback computation
  `incl_mem_perfSubfield_iff`.

Perfection/Existence supplies a chosen bundle in every exponential characteristic.
The perfection order isomorphism between closed lattices (P2) and the
Frobenius action (P3) build on this in `AclGeom.Perfection.Lattice`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** the bundle and perfected-subfield interface are proved (M2, P1).
The constructor in every characteristic is supplied by Perfection/Existence.
-/

namespace AclGeom

noncomputable section

universe u

/-- A chosen perfection of a field `K` (blueprint §type-correct statement):
a perfect field together with a `p`-radical inclusion of `K` making it a
perfect closure, where `p` is the characteristic exponent — `p = 1` in
characteristic zero, in which case `incl` is an isomorphism. Working with
this bundle keeps every statement uniform in the characteristic.-/
structure Perfection (K : Type u) [Field K] : Type (u + 1) where
  /-- The underlying perfect field.-/
  carrier : Type u
  /-- The carrier is a field.-/
  [field : Field carrier]
  /-- The characteristic exponent of `K` (and of the perfection).-/
  p : ℕ
  /-- `p` is the characteristic exponent of the base.-/
  [expCharBase : ExpChar K p]
  /-- `p` is the characteristic exponent of the carrier.-/
  [expCharCarrier : ExpChar carrier p]
  /-- The inclusion of `K` into its perfection.-/
  incl : K →+* carrier
  /-- The carrier is perfect.-/
  [perfect : PerfectRing carrier p]
  /-- The inclusion exhibits the carrier as a perfect closure of `K`.-/
  [isPerfectClosure : IsPerfectClosure incl p]

namespace Perfection

attribute [instance] Perfection.field Perfection.expCharBase Perfection.expCharCarrier
  Perfection.perfect Perfection.isPerfectClosure

/-- In characteristic zero, `K` is its own perfection, with characteristic
exponent `1` and the identity inclusion.-/
def ofCharZero (K : Type u) [Field K] [CharZero K] : Perfection K where
  carrier := K
  p := 1
  incl := RingHom.id K
  isPerfectClosure :=
    { pow_mem' := fun x ↦ ⟨0, x, by simp⟩
      ker_le' := by
        rw [(RingHom.injective_iff_ker_eq_bot _).1 fun _ _ h ↦ h]
        exact bot_le }

variable {K : Type*} [Field K] (π : Perfection K)

theorem incl_injective : Function.Injective π.incl :=
  π.incl.injective

/-- Every element of the perfection has a `p`-power inside (the image of)
`K`.-/
theorem exists_pow_incl (x : π.carrier) :
    ∃ (n : ℕ) (y : K), π.incl y = x ^ π.p ^ n :=
  IsPRadical.pow_mem π.incl π.p x

/-- The perfected subfield `M^perf` of a subfield `M ≤ K`: elements of the
perfection some `p`-power of which lies in the image of `M`
(blueprint §Foundation III).-/
def perfSubfield (M : Subfield K) : Subfield π.carrier where
  carrier := {x | ∃ n : ℕ, ∃ m ∈ M, x ^ π.p ^ n = π.incl m}
  one_mem' := ⟨0, 1, one_mem M, by simp⟩
  zero_mem' := ⟨0, 0, zero_mem M, by simp⟩
  mul_mem' := by
    rintro a b ⟨na, ma, hma, ha⟩ ⟨nb, mb, hmb, hb⟩
    refine ⟨na + nb, ma ^ π.p ^ nb * mb ^ π.p ^ na,
      mul_mem (pow_mem hma _) (pow_mem hmb _), ?_⟩
    rw [map_mul, map_pow, map_pow, ← ha, ← hb, mul_pow, ← pow_mul, ← pow_mul,
      ← pow_add, ← pow_add, Nat.add_comm nb na]
  add_mem' := by
    rintro a b ⟨na, ma, hma, ha⟩ ⟨nb, mb, hmb, hb⟩
    refine ⟨na + nb, ma ^ π.p ^ nb + mb ^ π.p ^ na,
      add_mem (pow_mem hma _) (pow_mem hmb _), ?_⟩
    rw [map_add, map_pow, map_pow, ← ha, ← hb, add_pow_expChar_pow, ← pow_mul,
      ← pow_mul, ← pow_add, ← pow_add, Nat.add_comm nb na]
  neg_mem' := by
    rintro a ⟨n, m, hm, h⟩
    refine ⟨n, (-1) ^ π.p ^ n * m,
      mul_mem (pow_mem (neg_mem (one_mem M)) _) hm, ?_⟩
    rw [map_mul, map_pow, map_neg, map_one, ← h, neg_pow, mul_comm]
  inv_mem' := by
    rintro a ⟨n, m, hm, h⟩
    exact ⟨n, m⁻¹, inv_mem hm, by rw [inv_pow, h, map_inv₀]⟩

/-- The public membership criterion for the perfected subfield
(blueprint §Foundation III).-/
theorem mem_perfSubfield_iff {M : Subfield K} {x : π.carrier} :
    x ∈ π.perfSubfield M ↔ ∃ n : ℕ, ∃ m ∈ M, x ^ π.p ^ n = π.incl m :=
  Iff.rfl

theorem perfSubfield_mono {M N : Subfield K} (h : M ≤ N) :
    π.perfSubfield M ≤ π.perfSubfield N := by
  rintro x ⟨n, m, hm, hx⟩
  exact ⟨n, m, h hm, hx⟩

/-- Elements of `K` land in `M^perf` exactly when some `p`-power lands in
`M`; this computes the pullback of the perfected subfield along the
inclusion.-/
theorem incl_mem_perfSubfield_iff {M : Subfield K} {x : K} :
    π.incl x ∈ π.perfSubfield M ↔ ∃ n : ℕ, x ^ π.p ^ n ∈ M := by
  constructor
  · rintro ⟨n, m, hm, hx⟩
    rw [← map_pow] at hx
    exact ⟨n, by rw [π.incl_injective hx]; exact hm⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, x ^ π.p ^ n, hn, by rw [map_pow]⟩

/-- The image of `M` is contained in `M^perf`.-/
theorem incl_mem_perfSubfield {M : Subfield K} {x : K} (hx : x ∈ M) :
    π.incl x ∈ π.perfSubfield M :=
  π.incl_mem_perfSubfield_iff.2 ⟨0, by simpa using hx⟩

end Perfection

end

end AclGeom
