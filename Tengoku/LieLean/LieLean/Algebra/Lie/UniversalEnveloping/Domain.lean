/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.Algebra.Lie.UniversalEnveloping.Graded

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The universal enveloping algebra of a free Lie algebra over a domain is a domain

Let `L` be a Lie algebra over a commutative ring `R` without zero divisors, and assume that `L`
is free as an `R`-module. Then `U(L)` has no zero divisors, and it is a domain if `R` is.

## Main results

* `UniversalEnvelopingAlgebra.exists_toGr_ne_zero`: every nonzero `u ∈ U(L)` has a nonzero
  *symbol* `[u] ∈ Fₙ / Fₙ₋₁ ⊆ gr U(L)`, where `n` is the filtration degree of `u`.
* `UniversalEnvelopingAlgebra.instNoZeroDivisors`: `U(L)` has no zero divisors.
* `UniversalEnvelopingAlgebra.instIsDomain`: `U(L)` is a domain.

## Proof

By the graded PBW theorem (`UniversalEnvelopingAlgebra.symmetricAlgebraEquivAssociatedGraded`),
`gr U(L) ≅ Sym(L)`, which is a polynomial ring over `R` and hence has no zero divisors. If
`u, v ≠ 0` have filtration degrees `m, n`, their symbols `[u] ∈ Fₘ / Fₘ₋₁`,
`[v] ∈ Fₙ / Fₙ₋₁` are nonzero, so `[u] [v] = [u v] ∈ Fₘ₊ₙ / Fₘ₊ₙ₋₁` is nonzero, and `u v ≠ 0`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  §0.5, §4.1 and Theorem 4.2(a) (the statement for `U(𝔫⁻)`, used to show that homomorphisms
  of Verma modules are injective).
* J. Dixmier, *Enveloping algebras*, Cor. 2.3.9 (over a field).
-/

noncomputable section

namespace UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- Every nonzero element `u` of `U(L)` has a nonzero symbol in `gr U(L)`: the class of `u` in
`Fₙ / Fₙ₋₁`, for `n` the least integer with `u ∈ Fₙ`.
@isnad1 id=ex.1h3v.s11.117c5978e065 from=translated src=- shape=df889f19 vocab=18366231
-/
theorem exists_toGr_ne_zero {u : UniversalEnvelopingAlgebra R L} (hu : u ≠ 0) :
    ∃ n, ∃ hn : u ∈ filtration R L n, toGr R L n ⟨u, hn⟩ ≠ 0 := by
  classical
  obtain ⟨n, hn, hmin⟩ : ∃ n, u ∈ filtration R L n ∧ ∀ k < n, u ∉ filtration R L k :=
    ⟨Nat.find (exists_mem_filtration u), Nat.find_spec (exists_mem_filtration u),
      fun _ ↦ Nat.find_min (exists_mem_filtration u)⟩
  refine ⟨n, hn, ?_⟩
  cases n with
  | zero =>
    rw [ne_eq, toGr_zero_eq_zero_iff]
    exact fun h0 ↦ hu (congrArg Subtype.val h0)
  | succ k =>
    rw [ne_eq, toGr_succ_eq_zero_iff]
    exact hmin k (Nat.lt_succ_self k)

/-- If `L` is a free module over a ring `R` without zero divisors, then `U(L)` has no zero
divisors. This follows from the graded PBW theorem `gr U(L) ≅ Sym(L)`. See Humphreys,
*Representations of semisimple Lie algebras in the BGG category 𝒪*, §0.5, and Dixmier,
*Enveloping algebras*, Cor. 2.3.9 (both over a field).
@isnad1 id=nozerodi.0h2v.s6.b5b6ccc999cd from=translated src=- shape=872e7571 vocab=e211e540
-/
instance instNoZeroDivisors [NoZeroDivisors R] [Module.Free R L] :
    NoZeroDivisors (UniversalEnvelopingAlgebra R L) := by
  have : NoZeroDivisors (AssociatedGraded R L) :=
    (symmetricAlgebraEquivAssociatedGraded R L).symm.toMulEquiv.noZeroDivisors
  refine ⟨fun {u v} huv ↦ ?_⟩
  by_contra! h
  obtain ⟨m, hm, hum⟩ := exists_toGr_ne_zero h.1
  obtain ⟨n, hn, hvn⟩ := exists_toGr_ne_zero h.2
  have := mul_ne_zero hum hvn
  rw [toGr_mul] at this
  refine this ?_
  have h0 : (⟨u * v, mul_mem_filtration hm hn⟩ : filtration R L (m + n)) = 0 :=
    Subtype.ext huv
  rw [h0, map_zero]

/--
@isnad1 id=nontrivi.0h2v.s4.c7ddf8cdf676 from=translated src=- shape=f79b5090 vocab=ec7011f3
-/
instance instNontrivial [Nontrivial R] : Nontrivial (UniversalEnvelopingAlgebra R L) :=
  (lift R (0 : L →ₗ⁅R⁆ R)).toRingHom.domain_nontrivial

end UniversalEnvelopingAlgebra
