/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Probability.Finite
import Tengoku

/-!
# Finite Shannon entropy

Entropy is measured in nats. For a finite `PMF`, the definition is the
finite sum of mathlib's `Real.negMulLog` over the real masses of the atoms.
This follows the same mathematical convention as Rocq `infotheo`: entropy is
first a function of a finite distribution, and random-variable entropy is then
defined by pushing a distribution forward along the random variable.
-/

namespace LeanInfoTheory
namespace Shannon

open scoped BigOperators

universe u v w

noncomputable section

/-- Shannon entropy, in nats, of a finite probability mass function. -/
def entropy {alpha : Type u} [Fintype alpha] (p : PMF alpha) : Real :=
  ∑ a, Real.negMulLog (p a).toReal

/-- The defining finite-sum formula for Shannon entropy. -/
theorem entropy_eq_sum {alpha : Type u} [Fintype alpha] (p : PMF alpha) :
    entropy p = ∑ a, Real.negMulLog (p a).toReal :=
  rfl

/-- Shannon entropy is nonnegative for finite PMFs. -/
theorem entropy_nonneg {alpha : Type u} [Fintype alpha] (p : PMF alpha) :
    0 <= entropy p := by
  classical
  rw [entropy_eq_sum]
  -- Each summand is nonnegative because every real PMF mass lies in `[0, 1]`.
  exact Finset.sum_nonneg fun a _ha =>
    Real.negMulLog_nonneg
      (PMF.toReal_nonneg p a)
      (PMF.toReal_le_one p a)

/--
Entropy is invariant under relabeling the alphabet by an equivalence.

This is one of the basic sanity checks for finite entropy: only the masses
matter, not the names of the atoms.
-/
theorem entropy_map_equiv {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] (p : PMF alpha) (e : alpha ≃ beta) :
    entropy (p.map e) = entropy p := by
  classical
  rw [entropy_eq_sum, entropy_eq_sum]
  exact
    (Fintype.sum_equiv e
      (fun a : alpha => Real.negMulLog (p a).toReal)
      (fun b : beta => Real.negMulLog (p.map e b).toReal)
      (fun a => by simp [PMF.map_apply_equiv p e a])).symm

/--
Entropy is invariant under injective relabeling into a larger finite alphabet.
Atoms outside the image of the relabeling have zero pushed-forward mass.
-/
theorem entropy_map_injective {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta]
    (p : PMF alpha) {f : alpha -> beta} (hf : Function.Injective f) :
    entropy (p.map f) = entropy p := by
  classical
  rw [entropy_eq_sum, entropy_eq_sum]
  let g : beta -> Real := fun b => Real.negMulLog (p.map f b).toReal
  calc
    (∑ b, Real.negMulLog (p.map f b).toReal) = (Finset.univ.image f).sum g := by
      symm
      apply Finset.sum_subset
      · intro b hb
        simp
      · intro b _hbuniv hbimage
        have hbrange : b ∉ Set.range f := by
          intro hbrange
          rcases hbrange with ⟨a, rfl⟩
          exact hbimage (by simp)
        simp [PMF.map_apply_eq_zero_of_notMem_range p hbrange]
    _ = ∑ a, g (f a) := by
      rw [Finset.sum_image]
      intro a _ha a' _ha' h
      exact hf h
    _ = ∑ a, Real.negMulLog (p a).toReal := by
      change
        (∑ a, Real.negMulLog (p.map f (f a)).toReal) =
          ∑ a, Real.negMulLog (p a).toReal
      apply Finset.sum_congr rfl
      intro a _ha
      rw [PMF.map_apply_of_injective p hf a]

/-- A deterministic finite PMF has entropy zero. -/
@[simp]
theorem entropy_pure {alpha : Type u} [Fintype alpha] (a : alpha) :
    entropy (PMF.pure a) = 0 := by
  classical
  rw [entropy_eq_sum]
  apply Finset.sum_eq_zero
  intro x _hx
  -- The selected atom has mass one and every other atom has mass zero.
  by_cases hx : x = a
  · simp [PMF.pure_apply, hx]
  · simp [PMF.pure_apply, hx]

private theorem negMulLog_eq_zero_iff_of_nonneg_of_le_one
    {x : Real} (hx0 : 0 <= x) (hx1 : x <= 1) :
    Real.negMulLog x = 0 ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro hx
    by_cases hzero : x = 0
    · exact Or.inl hzero
    · right
      have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hzero)
      by_contra hone
      have hxlt : x < 1 := lt_of_le_of_ne hx1 hone
      have hpos : 0 < Real.negMulLog x := by
        simpa only [Real.negMulLog_eq_neg, neg_pos] using Real.mul_log_neg hxpos hxlt
      exact hpos.ne' hx
  · rintro (rfl | rfl) <;> simp

/-- A finite PMF has entropy zero exactly when it is a pure law. -/
theorem entropy_eq_zero_iff {alpha : Type u} [Fintype alpha] (p : PMF alpha) :
    entropy p = 0 ↔ ∃ a, p = PMF.pure a := by
  classical
  constructor
  · intro hp
    have hterm : ∀ a, Real.negMulLog (p a).toReal = 0 := by
      have hnonneg :
          ∀ a : alpha, a ∈ (Finset.univ : Finset alpha) ->
            0 <= Real.negMulLog (p a).toReal := by
        intro a _ha
        exact Real.negMulLog_nonneg (PMF.toReal_nonneg p a) (PMF.toReal_le_one p a)
      have hsum : (∑ a : alpha, Real.negMulLog (p a).toReal) = 0 := by
        simpa only [entropy_eq_sum] using hp
      exact fun a =>
        (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum a (Finset.mem_univ a)
    obtain ⟨a, ha⟩ := p.support_nonempty
    have hreal_ne : (p a).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.2 ⟨ha, p.apply_ne_top a⟩
    have hreal_one : (p a).toReal = 1 := by
      rcases
          (negMulLog_eq_zero_iff_of_nonneg_of_le_one
            (PMF.toReal_nonneg p a) (PMF.toReal_le_one p a)).1 (hterm a) with
        hzero | hone
      · exact False.elim (hreal_ne hzero)
      · exact hone
    have hpa : p a = 1 := (ENNReal.toReal_eq_one_iff (p a)).1 hreal_one
    exact
      ⟨a, (PMF.eq_pure_iff_support_eq_singleton p a).2 ((p.apply_eq_one_iff a).1 hpa)⟩
  · rintro ⟨a, rfl⟩
    exact entropy_pure a

/-- Entropy of a finite-valued random variable under a discrete law. -/
def entropyOf {omega : Type u} {alpha : Type v} [Fintype alpha]
    (p : PMF omega) (X : omega -> alpha) : Real :=
  entropy (p.map X)

private theorem map_eq_pure_iff_eq_on_support
    {omega : Type u} {alpha : Type v} (p : PMF omega) (X : omega -> alpha) (a : alpha) :
    p.map X = PMF.pure a ↔ ∀ omega, omega ∈ p.support -> X omega = a := by
  constructor
  · intro hmap omega homega
    have hX : X omega ∈ (p.map X).support := by
      rw [PMF.support_map]
      exact ⟨omega, homega, rfl⟩
    rw [hmap, PMF.support_pure] at hX
    exact Set.mem_singleton_iff.1 hX
  · intro hX
    have hsupp : (p.map X).support = {a} := by
      rw [PMF.support_map]
      apply Set.Subset.antisymm
      · rintro _ ⟨omega, homega, rfl⟩
        exact Set.mem_singleton_iff.2 (hX omega homega)
      · intro x hx
        have hxa : x = a := Set.mem_singleton_iff.1 hx
        subst x
        obtain ⟨omega, homega⟩ := p.support_nonempty
        exact ⟨omega, homega, hX omega homega⟩
    exact (PMF.eq_pure_iff_support_eq_singleton (p.map X) a).2 hsupp

/--
The entropy of a finite-valued random variable is zero exactly when the
variable is constant on the support of the source PMF.
-/
theorem entropyOf_eq_zero_iff
    {omega : Type u} {alpha : Type v} [Fintype alpha]
    (p : PMF omega) (X : omega -> alpha) :
    entropyOf p X = 0 ↔
      ∃ a, ∀ omega, omega ∈ p.support -> X omega = a := by
  rw [entropyOf, entropy_eq_zero_iff]
  exact exists_congr fun a => map_eq_pure_iff_eq_on_support p X a

/-- Entropy of the identity random variable is the entropy of the original law. -/
@[simp]
theorem entropyOf_id {alpha : Type u} [Fintype alpha] (p : PMF alpha) :
    entropyOf p id = entropy p := by
  simp [entropyOf, PMF.map_id]

/-- Relabeling a finite-valued random variable by an equivalence preserves its entropy. -/
theorem entropyOf_comp_equiv
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (e : alpha ≃ beta) :
    entropyOf p (fun omega => e (X omega)) = entropyOf p X := by
  simpa [entropyOf, Function.comp_def, PMF.map_comp] using entropy_map_equiv (p := p.map X) e

/-- Applying an injective relabeling to a finite-valued random variable preserves its entropy. -/
theorem entropyOf_comp_injective
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) {f : alpha -> beta}
    (hf : Function.Injective f) :
    entropyOf p (fun omega => f (X omega)) = entropyOf p X := by
  simpa [entropyOf, Function.comp_def, PMF.map_comp] using
    entropy_map_injective (p := p.map X) hf

/-- Joint entropy is entropy of a joint finite distribution. -/
abbrev jointEntropy {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] (p : PMF (alpha × beta)) : Real :=
  entropy p

/-- Swapping the two coordinates of a joint law preserves entropy. -/
theorem entropy_map_swap {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] (p : PMF (alpha × beta)) :
    entropy (p.map Prod.swap) = entropy p := by
  simpa using entropy_map_equiv (p := p) (Equiv.prodComm alpha beta)

/--
Reassociating a left-associated triple alphabet preserves entropy.

This records that `H((A, B), C)` and `H(A, B, C)` are the same entropy after
the canonical product reassociation equivalence.
-/
theorem entropy_map_prodAssoc {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF ((alpha × beta) × gamma)) :
    entropy (p.map (Equiv.prodAssoc alpha beta gamma)) = entropy p := by
  exact entropy_map_equiv (p := p) (Equiv.prodAssoc alpha beta gamma)

/-- Reassociating a right-associated triple alphabet back to the left preserves entropy. -/
theorem entropy_map_prodAssoc_symm
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    entropy (p.map (Equiv.prodAssoc alpha beta gamma).symm) = entropy p := by
  exact entropy_map_equiv (p := p) (Equiv.prodAssoc alpha beta gamma).symm

/-- Swapping the two coordinates of a joint law preserves joint entropy. -/
theorem jointEntropy_map_swap {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] (p : PMF (alpha × beta)) :
    jointEntropy (p.map Prod.swap) = jointEntropy p :=
  entropy_map_swap p

/-- Joint entropy of two finite-valued random variables under a discrete law. -/
def jointEntropyOf {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) : Real :=
  entropyOf p fun omega => (X omega, Y omega)

/-- Joint entropy of two random variables is invariant under swapping their order. -/
theorem jointEntropyOf_swap
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    jointEntropyOf p Y X = jointEntropyOf p X Y := by
  simpa [jointEntropyOf, entropyOf, Function.comp_def, PMF.map_comp] using
    entropy_map_equiv
      (p := p.map fun omega => (X omega, Y omega))
      (Equiv.prodComm alpha beta)

/--
Entropy of three finite-valued random variables is invariant under reassociating
the product alphabet.
-/
theorem entropyOf_prodAssoc
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    entropyOf p (fun omega => (X omega, Y omega, Z omega)) =
      entropyOf p (fun omega => ((X omega, Y omega), Z omega)) := by
  unfold entropyOf
  have hmap :
      (p.map fun omega => (X omega, Y omega, Z omega)) =
        (p.map fun omega => ((X omega, Y omega), Z omega)).map
          (Equiv.prodAssoc alpha beta gamma) := by
    simpa [Function.comp_def] using
      (PMF.map_comp
        (p := p)
        (f := fun omega => ((X omega, Y omega), Z omega))
        (g := Equiv.prodAssoc alpha beta gamma)).symm
  rw [hmap]
  exact entropy_map_prodAssoc (p := p.map fun omega => ((X omega, Y omega), Z omega))

end

end Shannon
end LeanInfoTheory
