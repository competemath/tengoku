/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Tengoku.LanaBelyi.Belyi.CurveField.Riemann

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coordinate rings of affine curves

For a nonempty finite set `D` of places of a curve field `K`, the coordinate ring of the affine
curve `X ∖ D` is `𝒪(X ∖ D) = {f ∈ K | f ∈ 𝒪_P for all P ∉ D}` (`Belyi.CurveField.coordRing`).
It is the chart ring `A_t` (the integral closure of `ℚ[t]` in `K`) for any `t` whose poles are
exactly the places of `D` (such `t` exist by Riemann's theorem,
`Belyi.CurveField.exists_notMem_iff_mem`), hence a finitely generated `ℚ`-algebra; moreover any
finite set of regular functions on `X ∖ D` can be completed to a finite set of generators
(`Belyi.CurveField.exists_finset_adjoin_eq_coordRing`). Finite generating sets define the affine
integral models used for log-conductors ([GenEll], Definition 1.5 (iv)).
-/

namespace Belyi.CurveField

open Belyi.CurveField.Divisor

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

/-- The coordinate ring `𝒪(X ∖ D)` of the affine curve `X ∖ D`. -/
def coordRing (D : Finset (Place K)) : Subalgebra ℚ K where
  carrier := {f | ∀ P : Place K, P ∉ D → f ∈ P.1}
  mul_mem' hf hg P hP := mul_mem (hf P hP) (hg P hP)
  add_mem' hf hg P hP := add_mem (hf P hP) (hg P hP)
  algebraMap_mem' q P _ := P.algebraMap_mem q

theorem mem_coordRing {D : Finset (Place K)} {f : K} :
    f ∈ coordRing D ↔ ∀ P : Place K, P ∉ D → f ∈ P.1 := Iff.rfl

/-- The chart ring `A_t` consists of the functions regular at all places where `t` is. -/
theorem mem_chartRing_iff_forall {t : K} [Fact (Transcendental ℚ t)] (f : K) :
    f ∈ chartRing t ↔ ∀ P : Place K, t ∈ P.1 → f ∈ P.1 := by
  refine ⟨fun hf P hP => mem_of_mem_chartRing P.1 P.ratCast_mem hP hf, fun hf => ?_⟩
  set s : Set K := Set.range (algebraMap ℚ K) ∪ {t} with hs
  have hmem : f ∈ (⨅ V : {V : ValuationSubring K // s ⊆ V.toSubring}, V.1.toSubring) := by
    rw [Subring.mem_iInf]
    rintro ⟨V, hV⟩
    by_cases htop : V = ⊤
    · subst htop
      exact trivial
    · have hq : ∀ q : ℚ, (q : K) ∈ V := fun q => hV (Or.inl ⟨q, eq_ratCast _ q⟩)
      exact hf ⟨V, htop, hq⟩ (hV (Or.inr rfl))
  rw [iInf_valuationSubring_superset] at hmem
  have hint : IsIntegral (Subring.closure s) f := hmem
  have heq : (Algebra.adjoin ℚ {t}).toSubring = Subring.closure s := by
    rw [Algebra.adjoin_eq_ring_closure]
  let e : Subring.closure s →+* Algebra.adjoin ℚ {t} :=
    { toFun := fun a => ⟨a.1, by rw [← Subalgebra.mem_toSubring, heq]; exact a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact IsIntegral.map_of_comp_eq e (RingHom.id K) (by ext a; rfl) hint

/-- The coordinate ring of `X ∖ D` is the chart ring of a function with poles exactly `D`. -/
theorem coordRing_eq_chartRing {D : Finset (Place K)} {t : K} [Fact (Transcendental ℚ t)]
    (ht : ∀ P : Place K, t ∉ P.1 ↔ P ∈ D) (f : K) : f ∈ coordRing D ↔ f ∈ chartRing t := by
  rw [mem_coordRing, mem_chartRing_iff_forall]
  refine forall_congr' fun P => ?_
  rw [← ht]
  exact ⟨fun h htP => h (not_not.mpr htP), fun h hn => h (not_not.mp hn)⟩

end Belyi.CurveField
