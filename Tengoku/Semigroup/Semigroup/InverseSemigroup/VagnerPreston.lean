/-
Copyright (c) 2026 Timothy Harvey and James Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timothy Harvey
-/
import Tengoku.Seed.Logic.Equiv.PartialEquiv
import Tengoku.Semigroup.Semigroup.InverseSemigroup.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Vagner–Preston Representation Theorem

Every inverse semigroup `S` embeds into the symmetric inverse semigroup of partial
bijections of `S`: the map `a ↦ ρ_a`, where `ρ_a : S * a⁻¹ → S * a` is right
translation `x ↦ x * a`, is an injective homomorphism. Partial bijections are
modelled by Mathlib's `PartialEquiv S S`, with `PartialEquiv.trans` as the
(strictly associative) composition; the domain `S * a⁻¹` is implemented by its
fixed-point description `{x | x * (a * a⁻¹) = x}`.

## Main definitions

* `InverseSemigroup.vagnerMap`: right translation by `a` as a partial bijection of
  `S`, with source `{x | x * (a * a⁻¹) = x}` and target `{y | y * (a⁻¹ * a) = y}`.

## Main results

* `InverseSemigroup.vagnerMap_trans`: multiplicativity,
  `vagnerMap (a * b) = (vagnerMap a).trans (vagnerMap b)`.
* `InverseSemigroup.vagnerMap_injective`: the Vagner–Preston map is injective.
* `InverseSemigroup.vagner_preston`: the packaged embedding — the Vagner–Preston
  representation theorem.

## References

* [J. M. Howie, *Fundamentals of Semigroup Theory*][howie1995]

The proofs formalized in this module closely follow the structure and logic
from lecture notes:

* J. D. Mitchell, *MT5863 Semigroup Theory* (lecture notes,
  University of St Andrews, 2026).
-/
namespace Tengoku.Semigroup end Tengoku.Semigroup open Tengoku.Semigroup
namespace Tengoku.Semigroup.InverseSemigroup

variable {S : Type*} [InverseSemigroup S]

/-- The **Vagner–Preston map**: right translation by `a`, as a partial
bijection of `S` with source `S * a⁻¹ = {x | x * (a * a⁻¹) = x}` and target
`S * a = {y | y * (a⁻¹ * a) = y}`; the inverse map is right translation by
`a⁻¹`.-/
def vagnerMap (a : S) : PartialEquiv S S where
  toFun := (· * a)
  invFun := (· * a⁻¹)
  source := {x | x * (a * a⁻¹) = x}
  target := {y | y * (a⁻¹ * a) = y}
  map_source' := fun x _ => show x * a * (a⁻¹ * a) = x * a by
    rw [mul_assoc, ← mul_assoc a, mul_inv_mul]
  map_target' := fun y _ => show y * a⁻¹ * (a * a⁻¹) = y * a⁻¹ by
    rw [mul_assoc, ← mul_assoc a⁻¹, inv_mul_inv]
  left_inv' := fun x hx => by
    show x * a * a⁻¹ = x
    rw [mul_assoc]
    exact hx
  right_inv' := fun y hy => by
    show y * a⁻¹ * a = y
    rw [mul_assoc]
    exact hy

/-- `vagnerMap a` acts by right translation: `vagnerMap a x = x * a`.-/
@[simp] theorem vagnerMap_apply (a x : S) : vagnerMap a x = x * a := rfl

/-- The source of `vagnerMap a` is the set of fixed points of right
multiplication by the idempotent `a * a⁻¹`.-/
@[simp] theorem vagnerMap_source (a : S) :
    (vagnerMap a).source = {x | x * (a * a⁻¹) = x} := rfl

/-- The target of `vagnerMap a` is the set of fixed points of right
multiplication by the idempotent `a⁻¹ * a`.-/
@[simp] theorem vagnerMap_target (a : S) :
    (vagnerMap a).target = {y | y * (a⁻¹ * a) = y} := rfl

/-- The source of `vagnerMap a` is the principal left ideal `S¹ * a * a⁻¹`:
membership is equivalent to being a left multiple of `a * a⁻¹`.-/
theorem mem_vagnerMap_source_iff (a x : S) :
    x ∈ (vagnerMap a).source ↔ ∃ s : S, x = s * (a * a⁻¹) :=
  ⟨fun hx => ⟨x, hx.symm⟩, fun ⟨s, hs⟩ => by
    change x * (a * a⁻¹) = x
    have : IsIdempotentElem (a * a⁻¹) := isIdempotentElem_mul_inv a
    rw [hs, mul_assoc, this.eq]⟩

/-- **Multiplicativity** of the Vagner–Preston map: `ρ_(a*b) = ρ_a ∘ ρ_b`
(note `PartialEquiv.trans` composes left-to-right, matching
`x * (a * b) = (x * a) * b`).

The functions agree by associativity (and `mul_inv_rev` for the inverse
functions), so by `PartialEquiv.ext` it suffices to identify the sources.
`(ρ_a.trans ρ_b).source = {x | x(aa⁻¹) = x} ∩ (·*a) ⁻¹' {y | y(bb⁻¹) = y}`,
while `ρ_(ab)` has source `{x | x(ab)(b⁻¹a⁻¹) = x}`; using
`idempotent_mul_comm` to slide the idempotents `bb⁻¹` and `a⁻¹a` past each
other, each membership implies the other (Howie, Lemma 5.1.6).-/
theorem vagnerMap_trans (a b : S) :
    vagnerMap (a * b) = (vagnerMap a).trans (vagnerMap b) := by
  have hcomm : b * (b⁻¹ * (a⁻¹ * a)) = a⁻¹ * (a * (b * b⁻¹)) := by
    have h := idempotent_mul_comm (isIdempotentElem_mul_inv b) (isIdempotentElem_inv_mul a)
    simpa only [mul_assoc] using h
  have haa : ∀ z : S, a * (a⁻¹ * (a * z)) = a * z := fun z => by
    have h := congrArg (· * z) (mul_inv_mul a)
    simpa only [mul_assoc] using h
  refine PartialEquiv.ext (fun x => (mul_assoc x a b).symm) (fun x => ?_) ?_
  · -- the inverse functions agree: `x * (a * b)⁻¹ = (x * b⁻¹) * a⁻¹`
    change x * (a * b)⁻¹ = x * b⁻¹ * a⁻¹
    rw [mul_inv_rev, ← mul_assoc]
  · -- the sources agree
    rw [PartialEquiv.trans_source]
    ext x
    simp only [vagnerMap_source, vagnerMap_apply, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_ofPred_eq, mul_inv_rev]
    constructor
    · intro hx
      simp only [mul_assoc] at hx
      -- hx : x * (a * (b * (b⁻¹ * a⁻¹))) = x
      have h2 : x * a * (b * b⁻¹) = x * a := by
        have h := congrArg (· * a) hx
        simp only [mul_assoc] at h
        rw [hcomm, haa] at h
        simpa only [mul_assoc] using h
      refine ⟨?_, h2⟩
      have h := congrArg (· * a⁻¹) h2
      simp only [mul_assoc] at h
      -- h : x * (a * (b * (b⁻¹ * a⁻¹))) = x * (a * a⁻¹)
      exact h.symm.trans hx
    · rintro ⟨h1, h2⟩
      have h := congrArg (· * a⁻¹) h2
      simp only [mul_assoc] at h ⊢
      -- h : x * (a * (b * (b⁻¹ * a⁻¹))) = x * (a * a⁻¹)
      rw [h]
      exact h1

/-- **Injectivity** of the Vagner–Preston map: suppose `ρ_a = ρ_b`.  Equal
sources give that `a * a⁻¹` and `b * b⁻¹` are each fixed by right
multiplication by the other, so by commuting idempotents
`a * a⁻¹ = b * b⁻¹`; equal functions give `x * a = x * b` for every `x`,
whence `a = (a * a⁻¹) * a = (b * b⁻¹) * a = b * (b⁻¹ * b) = b`.-/
theorem vagnerMap_injective :
    Function.Injective (vagnerMap : S → PartialEquiv S S) := by
  intro a b h
  have happ : ∀ x : S, x * a = x * b := fun x =>
    congrArg (fun e : PartialEquiv S S => e x) h
  have hsrc : {x : S | x * (a * a⁻¹) = x} = {x : S | x * (b * b⁻¹) = x} :=
    congrArg PartialEquiv.source h
  have h1 : (a * a⁻¹) * (b * b⁻¹) = a * a⁻¹ := by
    have hmem : a * a⁻¹ ∈ {x : S | x * (a * a⁻¹) = x} := (isIdempotentElem_mul_inv a).eq
    rw [hsrc] at hmem
    exact hmem
  have h2 : (b * b⁻¹) * (a * a⁻¹) = b * b⁻¹ := by
    have hmem : b * b⁻¹ ∈ {x : S | x * (b * b⁻¹) = x} := (isIdempotentElem_mul_inv b).eq
    rw [← hsrc] at hmem
    exact hmem
  have hee : a * a⁻¹ = b * b⁻¹ :=
    calc a * a⁻¹ = (a * a⁻¹) * (b * b⁻¹) := h1.symm
      _ = (b * b⁻¹) * (a * a⁻¹) :=
          idempotent_mul_comm (isIdempotentElem_mul_inv a) (isIdempotentElem_mul_inv b)
      _ = b * b⁻¹ := h2
  calc a = a * a⁻¹ * a := (mul_inv_mul a).symm
    _ = b * b⁻¹ * a := by rw [hee]
    _ = b * (b⁻¹ * a) := mul_assoc b b⁻¹ a
    _ = b * (b⁻¹ * b) := by rw [happ b⁻¹]
    _ = b * b⁻¹ * b := (mul_assoc b b⁻¹ b).symm
    _ = b := mul_inv_mul b

/-- **The Vagner–Preston representation theorem**: every inverse semigroup
embeds in the symmetric inverse semigroup of partial bijections of its own
carrier.-/
theorem vagner_preston :
    ∃ θ : S → PartialEquiv S S,
      Function.Injective θ ∧ ∀ a b : S, θ (a * b) = (θ a).trans (θ b) :=
  ⟨vagnerMap, vagnerMap_injective, vagnerMap_trans⟩

end Tengoku.Semigroup.InverseSemigroup
-- Tengoku: root names of this library moved to Tengoku.Semigroup so they do not collide with other libraries (generated)
