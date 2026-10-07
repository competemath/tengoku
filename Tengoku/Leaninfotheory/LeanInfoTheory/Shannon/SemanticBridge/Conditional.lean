/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.InfoMeasures
import Tengoku

/-!
# Finite conditional laws for the Shannon semantic bridge

This file introduces the first finite conditional-law API used by the semantic
bridge layer.

For a joint law `p : PMF (alpha × beta)`, the project convention is that
`condEntropy p` means `H(alpha | beta)`, the entropy of the first coordinate
conditioned on the second. The canonical finite conditional PMF
`P_{alpha | beta = b}` exists only when the conditioning atom has nonzero
marginal mass. We therefore require a proof of `sndMarginal p b ≠ 0` instead
of choosing an arbitrary default PMF on zero-mass conditioning atoms.
-/

namespace LeanInfoTheory
namespace Shannon

open scoped BigOperators ENNReal

noncomputable section

universe u v

-- Every PMF atom is finite as an `ENNReal`; conditional normalization divides
-- by a nonzero finite marginal mass.
private theorem pmf_apply_ne_top {alpha : Type u} (p : PMF alpha) (a : alpha) :
    p a ≠ ⊤ := by
  exact ne_of_lt ((PMF.coe_le_one (p := p) a).trans_lt ENNReal.one_lt_top)

/--
Conditional law of the first coordinate given a nonzero second-coordinate atom.

Mathematically, this is the finite PMF
`P_{A | B=b}(a) = P_{A,B}(a,b) / P_B(b)`. The proof argument
`hb : sndMarginal p b ≠ 0` is part of the API so that zero-probability
conditioning atoms do not receive a fake default distribution.
-/
def condFstGivenSnd {alpha : Type u} {beta : Type v} [Fintype alpha]
    (p : PMF (alpha × beta)) (b : beta) (hb : sndMarginal p b ≠ 0) : PMF alpha :=
  PMF.ofFintype (fun a => p (a, b) / sndMarginal p b) (by
    classical
    calc
      (∑ a : alpha, p (a, b) / sndMarginal p b)
          = ∑ a : alpha, p (a, b) * (sndMarginal p b)⁻¹ := by
            rfl
      _ = (∑ a : alpha, p (a, b)) * (sndMarginal p b)⁻¹ := by
            rw [Finset.sum_mul]
      _ = sndMarginal p b * (sndMarginal p b)⁻¹ := by
            rw [← sndMarginal_apply (p := p) (b := b)]
      _ = 1 := by
            exact ENNReal.mul_inv_cancel hb (pmf_apply_ne_top (sndMarginal p) b))

/--
Atom formula for the conditional law:
`P_{A | B=b}(a) = P_{A,B}(a,b) / P_B(b)`.
-/
@[simp]
theorem condFstGivenSnd_apply {alpha : Type u} {beta : Type v} [Fintype alpha]
    (p : PMF (alpha × beta)) (b : beta) (hb : sndMarginal p b ≠ 0) (a : alpha) :
    condFstGivenSnd p b hb a = p (a, b) / sndMarginal p b := by
  rfl

/--
The conditional PMF does not depend on which proof of nonzero marginal mass was
used to construct it.
-/
theorem condFstGivenSnd_proof_irrel {alpha : Type u} {beta : Type v} [Fintype alpha]
    (p : PMF (alpha × beta)) (b : beta)
    (hb hb' : sndMarginal p b ≠ 0) :
    condFstGivenSnd p b hb = condFstGivenSnd p b hb' := by
  ext a
  simp

/--
An atom has zero conditional mass exactly when the corresponding joint atom has
zero mass.
-/
@[simp]
theorem condFstGivenSnd_apply_eq_zero_iff {alpha : Type u} {beta : Type v}
    [Fintype alpha] (p : PMF (alpha × beta)) (b : beta)
    (hb : sndMarginal p b ≠ 0) (a : alpha) :
    condFstGivenSnd p b hb a = 0 ↔ p (a, b) = 0 := by
  have htop : sndMarginal p b ≠ ⊤ := pmf_apply_ne_top (sndMarginal p) b
  rw [condFstGivenSnd_apply, ENNReal.div_eq_zero_iff]
  constructor
  · intro h
    rcases h with h | h
    · exact h
    · exact False.elim (htop h)
  · intro h
    exact Or.inl h

/--
An atom has nonzero conditional mass exactly when the corresponding joint atom
has nonzero mass.
-/
@[simp]
theorem condFstGivenSnd_apply_ne_zero_iff {alpha : Type u} {beta : Type v}
    [Fintype alpha] (p : PMF (alpha × beta)) (b : beta)
    (hb : sndMarginal p b ≠ 0) (a : alpha) :
    condFstGivenSnd p b hb a ≠ 0 ↔ p (a, b) ≠ 0 := by
  rw [ne_eq, condFstGivenSnd_apply_eq_zero_iff]

/--
The support of `P_{A | B=b}` is the fiber of the joint support over `b`.
-/
@[simp]
theorem support_condFstGivenSnd {alpha : Type u} {beta : Type v}
    [Fintype alpha] (p : PMF (alpha × beta)) (b : beta)
    (hb : sndMarginal p b ≠ 0) :
    (condFstGivenSnd p b hb).support = {a | p (a, b) ≠ 0} := by
  ext a
  rw [PMF.mem_support_iff, Set.mem_ofPred_eq, condFstGivenSnd_apply_ne_zero_iff]

/--
Joint mass factors as conditional mass times the conditioning marginal:
`P_{A | B=b}(a) * P_B(b) = P_{A,B}(a,b)`.
-/
theorem condFstGivenSnd_mul_sndMarginal {alpha : Type u} {beta : Type v}
    [Fintype alpha] (p : PMF (alpha × beta)) (b : beta)
    (hb : sndMarginal p b ≠ 0) (a : alpha) :
    condFstGivenSnd p b hb a * sndMarginal p b = p (a, b) := by
  rw [condFstGivenSnd_apply]
  exact ENNReal.div_mul_cancel hb (pmf_apply_ne_top (sndMarginal p) b)

/--
Joint mass factors as the conditioning marginal times conditional mass:
`P_B(b) * P_{A | B=b}(a) = P_{A,B}(a,b)`.
-/
theorem sndMarginal_mul_condFstGivenSnd {alpha : Type u} {beta : Type v}
    [Fintype alpha] (p : PMF (alpha × beta)) (b : beta)
    (hb : sndMarginal p b ≠ 0) (a : alpha) :
    sndMarginal p b * condFstGivenSnd p b hb a = p (a, b) := by
  rw [mul_comm]
  exact condFstGivenSnd_mul_sndMarginal p b hb a

/--
Real-valued version of the joint factorization:
`P_B(b) * P_{A | B=b}(a) = P_{A,B}(a,b)` after converting masses to `Real`.
-/
theorem sndMarginal_toReal_mul_condFstGivenSnd_toReal
    {alpha : Type u} {beta : Type v} [Fintype alpha]
    (p : PMF (alpha × beta)) (b : beta) (hb : sndMarginal p b ≠ 0) (a : alpha) :
    (sndMarginal p b).toReal * (condFstGivenSnd p b hb a).toReal =
      (p (a, b)).toReal := by
  have h := congrArg ENNReal.toReal
    (sndMarginal_mul_condFstGivenSnd p b hb a)
  simpa [ENNReal.toReal_mul] using h

/--
Entropy of the conditional fiber, with explicit zero-mass branch.

This helper is intended for expected conditional entropy formulas. If
`P_B(b)=0`, the branch is the number `0`, not the entropy of an arbitrary
default conditional PMF.
-/
def condEntropyFstGivenSnd {alpha : Type u} {beta : Type v}
    [Fintype alpha] (p : PMF (alpha × beta)) (b : beta) : Real :=
  if hb : sndMarginal p b = 0 then
    0
  else
    entropy (condFstGivenSnd p b hb)

/-- Zero-marginal conditioning atoms contribute zero to conditional-fiber entropy. -/
@[simp]
theorem condEntropyFstGivenSnd_of_sndMarginal_eq_zero
    {alpha : Type u} {beta : Type v} [Fintype alpha]
    (p : PMF (alpha × beta)) {b : beta} (hb : sndMarginal p b = 0) :
    condEntropyFstGivenSnd p b = 0 := by
  rw [condEntropyFstGivenSnd, dite_eq_left hb]

/--
On nonzero conditioning atoms, `condEntropyFstGivenSnd` is the entropy of the
canonical conditional PMF `P_{A | B=b}`.
-/
theorem condEntropyFstGivenSnd_of_sndMarginal_ne_zero
    {alpha : Type u} {beta : Type v} [Fintype alpha]
    (p : PMF (alpha × beta)) {b : beta} (hb : sndMarginal p b ≠ 0) :
    condEntropyFstGivenSnd p b = entropy (condFstGivenSnd p b hb) := by
  rw [condEntropyFstGivenSnd, dite_eq_right hb]

/--
Per-fiber conditional entropy identity.

For each conditioning atom `b`,
`p_B(b) * H(P_{A | B=b}) = sum_a h(p(a,b)) - h(p_B(b))`, where
`h(x) = -x log x`. If `p_B(b)=0`, the left side uses the explicit zero branch
of `condEntropyFstGivenSnd`, and the right side is zero because every joint
atom over `b` has zero mass.
-/
theorem sndMarginal_toReal_mul_condEntropyFstGivenSnd
    {alpha : Type u} {beta : Type v} [Fintype alpha]
    (p : PMF (alpha × beta)) (b : beta) :
    (sndMarginal p b).toReal * condEntropyFstGivenSnd p b =
      (∑ a : alpha, Real.negMulLog (p (a, b)).toReal) -
        Real.negMulLog (sndMarginal p b).toReal := by
  classical
  by_cases hb : sndMarginal p b = 0
  · have hpzero : ∀ a : alpha, p (a, b) = 0 := fun a =>
      apply_eq_zero_of_sndMarginal_eq_zero p a hb
    have hsum_zero : (∑ a : alpha, Real.negMulLog (p (a, b)).toReal) = 0 := by
      apply Finset.sum_eq_zero
      intro a _ha
      rw [hpzero a]
      simp
    rw [condEntropyFstGivenSnd_of_sndMarginal_eq_zero p hb, hb, hsum_zero]
    simp
  · have hsum_cond :
        (∑ a : alpha, (condFstGivenSnd p b hb a).toReal) = 1 :=
      PMF.sum_toReal (condFstGivenSnd p b hb)
    have hpoint (a : alpha) :
        (sndMarginal p b).toReal *
            Real.negMulLog (condFstGivenSnd p b hb a).toReal =
          Real.negMulLog (p (a, b)).toReal -
            (condFstGivenSnd p b hb a).toReal *
              Real.negMulLog (sndMarginal p b).toReal := by
      have hfactor :
          (p (a, b)).toReal =
            (sndMarginal p b).toReal * (condFstGivenSnd p b hb a).toReal := by
        exact (sndMarginal_toReal_mul_condFstGivenSnd_toReal p b hb a).symm
      rw [hfactor, Real.negMulLog_mul]
      ring_nf
    rw [condEntropyFstGivenSnd_of_sndMarginal_ne_zero p hb]
    rw [entropy_eq_sum]
    calc
      (sndMarginal p b).toReal *
          (∑ a : alpha, Real.negMulLog (condFstGivenSnd p b hb a).toReal)
          = ∑ a : alpha,
              (sndMarginal p b).toReal *
                Real.negMulLog (condFstGivenSnd p b hb a).toReal := by
            rw [Finset.mul_sum]
      _ = ∑ a : alpha,
              (Real.negMulLog (p (a, b)).toReal -
                (condFstGivenSnd p b hb a).toReal *
                  Real.negMulLog (sndMarginal p b).toReal) := by
            apply Finset.sum_congr rfl
            intro a _ha
            exact hpoint a
      _ = (∑ a : alpha, Real.negMulLog (p (a, b)).toReal) -
            (∑ a : alpha, (condFstGivenSnd p b hb a).toReal) *
              Real.negMulLog (sndMarginal p b).toReal := by
            rw [Finset.sum_sub_distrib]
            congr 1
            rw [Finset.sum_mul]
      _ = (∑ a : alpha, Real.negMulLog (p (a, b)).toReal) -
            Real.negMulLog (sndMarginal p b).toReal := by
            rw [hsum_cond]
            simp

/--
Expected conditional entropy formula for the finite conditional-law API:

`H(A | B) = sum_b p_B(b) * H(P_{A | B=b})`.

The right-hand side is written using `condEntropyFstGivenSnd`, whose value is
`0` on zero-marginal conditioning atoms and the entropy of the canonical
conditional PMF on nonzero atoms.
-/
theorem condEntropy_eq_sum_sndMarginal_mul_condEntropyFstGivenSnd
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) :
    condEntropy p =
      ∑ b : beta, (sndMarginal p b).toReal * condEntropyFstGivenSnd p b := by
  classical
  have hjoint :
      entropy p = ∑ b : beta, ∑ a : alpha, Real.negMulLog (p (a, b)).toReal := by
    rw [entropy_eq_sum]
    calc
      (∑ x : alpha × beta, Real.negMulLog (p x).toReal)
          = ∑ a : alpha, ∑ b : beta, Real.negMulLog (p (a, b)).toReal := by
            rw [Fintype.sum_prod_type]
      _ = ∑ b : beta, ∑ a : alpha, Real.negMulLog (p (a, b)).toReal := by
            rw [Finset.sum_comm]
  calc
    condEntropy p = entropy p - entropy (sndMarginal p) := by
      rw [condEntropy_eq]
    _ = (∑ b : beta, ∑ a : alpha, Real.negMulLog (p (a, b)).toReal) -
          ∑ b : beta, Real.negMulLog (sndMarginal p b).toReal := by
          rw [hjoint, entropy_eq_sum]
    _ = ∑ b : beta,
          ((∑ a : alpha, Real.negMulLog (p (a, b)).toReal) -
            Real.negMulLog (sndMarginal p b).toReal) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ b : beta, (sndMarginal p b).toReal * condEntropyFstGivenSnd p b := by
          apply Finset.sum_congr rfl
          intro b _hb
          exact (sndMarginal_toReal_mul_condEntropyFstGivenSnd p b).symm

/-! ## Triple conditioning infrastructure -/

/--
The right-associated law `P_{A,B,C}` viewed as a law on `((A, B), C)`.

This is the law whose conditional fibers over `C=c` are joint laws on
`A × B`.
-/
abbrev pairThirdLaw {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta × gamma)) : PMF ((alpha × beta) × gamma) :=
  p.map (Equiv.prodAssoc alpha beta gamma).symm

/-- Atom formula for the reassociated law `((A,B),C)`. -/
@[simp]
theorem pairThirdLaw_apply {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta × gamma)) (a : alpha) (b : beta) (c : gamma) :
    pairThirdLaw p ((a, b), c) = p (a, b, c) := by
  simpa [pairThirdLaw] using
    PMF.map_apply_equiv (p := p) (e := (Equiv.prodAssoc alpha beta gamma).symm) (a, b, c)

private theorem map_pair_eq_pairThirdLaw
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta × gamma)) :
    p.map (fun z => ((z.1, z.2.1), z.2.2)) = pairThirdLaw p := by
  unfold pairThirdLaw
  apply congrArg (fun f => p.map f)
  funext z
  rcases z with ⟨a, b, c⟩
  rfl

/-- The second marginal of the reassociated law `((A,B),C)` is the law of `C`. -/
@[simp]
theorem sndMarginal_pairThirdLaw {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta × gamma)) :
    sndMarginal (pairThirdLaw p) = thirdMarginal p := by
  unfold pairThirdLaw sndMarginal thirdMarginal
  rw [PMF.map_comp]
  rfl

/-- Reassociating `(A,B,C)` as `((A,B),C)` preserves entropy. -/
theorem entropy_pairThirdLaw {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    entropy (pairThirdLaw p) = entropy p := by
  exact entropy_map_prodAssoc_symm p

/--
PMF form of the triple conditional-entropy chain rule:
`H(A,B|C) = H(B|C) + H(A|B,C)`.
-/
theorem condEntropy_pairThirdLaw_chain_rule
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condEntropy (pairThirdLaw p) =
      condEntropy (sndThirdMarginal p) + condEntropy p := by
  have hsnd : p.map (fun z => z.2) = sndThirdMarginal p := by
    apply congrArg (fun f => p.map f)
    funext z
    rfl
  have hid : p.map (fun z => z) = p := by
    change p.map id = p
    exact PMF.map_id p
  have h :=
    condEntropyOf_pair_chain_rule
      p (fun z => z.1) (fun z => z.2.1) (fun z => z.2.2)
  unfold condEntropyOf at h
  rw [map_pair_eq_pairThirdLaw, hsnd, hid] at h
  exact h

/--
Swapped PMF form of the triple conditional-entropy chain rule:
`H(A,B|C) = H(A|C) + H(B|A,C)`.
-/
theorem condEntropy_pairThirdLaw_chain_rule_swap
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condEntropy (pairThirdLaw p) =
      condEntropy (fstThirdMarginal p) +
        condEntropy (p.map fun z => (z.2.1, z.1, z.2.2)) := by
  have hfst : p.map (fun z => (z.1, z.2.2)) = fstThirdMarginal p := by
    rfl
  have h :=
    condEntropyOf_pair_chain_rule_swap
      p (fun z => z.1) (fun z => z.2.1) (fun z => z.2.2)
  unfold condEntropyOf at h
  rw [map_pair_eq_pairThirdLaw, hfst] at h
  exact h

/-! ## Conditional mutual information fibers -/

/--
Conditional joint law of the first two coordinates given a nonzero third
coordinate atom.

Mathematically, this is
`P_{A,B | C=c}(a,b) = P_{A,B,C}(a,b,c) / P_C(c)`.
-/
def condFstSndGivenThird {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta × gamma)) (c : gamma)
    (hc : thirdMarginal p c ≠ 0) : PMF (alpha × beta) :=
  PMF.ofFintype (fun x : alpha × beta => p (x.1, x.2, c) / thirdMarginal p c) (by
    classical
    calc
      (∑ x : alpha × beta, p (x.1, x.2, c) / thirdMarginal p c)
          = ∑ x : alpha × beta, p (x.1, x.2, c) * (thirdMarginal p c)⁻¹ := by
            rfl
      _ = (∑ x : alpha × beta, p (x.1, x.2, c)) * (thirdMarginal p c)⁻¹ := by
            rw [Finset.sum_mul]
      _ = (∑ a : alpha, ∑ b : beta, p (a, b, c)) * (thirdMarginal p c)⁻¹ := by
            rw [Fintype.sum_prod_type]
      _ = thirdMarginal p c * (thirdMarginal p c)⁻¹ := by
            rw [← thirdMarginal_apply (p := p) (c := c)]
      _ = 1 := by
            exact ENNReal.mul_inv_cancel hc (pmf_apply_ne_top (thirdMarginal p) c))

/-- Atom formula for `P_{A,B | C=c}`. -/
@[simp]
theorem condFstSndGivenThird_apply
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta × gamma)) (c : gamma)
    (hc : thirdMarginal p c ≠ 0) (a : alpha) (b : beta) :
    condFstSndGivenThird p c hc (a, b) = p (a, b, c) / thirdMarginal p c := by
  rfl

/--
Joint mass factors through the conditional joint law:
`P_C(c) * P_{A,B|C=c}(a,b) = P_{A,B,C}(a,b,c)`.
-/
theorem thirdMarginal_mul_condFstSndGivenThird
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta × gamma)) (c : gamma)
    (hc : thirdMarginal p c ≠ 0) (a : alpha) (b : beta) :
    thirdMarginal p c * condFstSndGivenThird p c hc (a, b) = p (a, b, c) := by
  rw [condFstSndGivenThird_apply, mul_comm]
  exact ENNReal.div_mul_cancel hc (pmf_apply_ne_top (thirdMarginal p) c)

/--
Real-valued joint factorization for the conditional joint law:
`P_C(c) * P_{A,B|C=c}(a,b) = P_{A,B,C}(a,b,c)`.
-/
theorem thirdMarginal_toReal_mul_condFstSndGivenThird_toReal
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta × gamma)) (c : gamma)
    (hc : thirdMarginal p c ≠ 0) (a : alpha) (b : beta) :
    (thirdMarginal p c).toReal *
        (condFstSndGivenThird p c hc (a, b)).toReal =
      (p (a, b, c)).toReal := by
  have h := congrArg ENNReal.toReal
    (thirdMarginal_mul_condFstSndGivenThird p c hc a b)
  simpa [ENNReal.toReal_mul] using h

/-- The second marginal of the `(A,C)` law is the law of `C`. -/
@[simp]
theorem sndMarginal_fstThirdMarginal
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Finite alpha] [Finite beta]
    (p : PMF (alpha × beta × gamma)) :
    sndMarginal (fstThirdMarginal p) = thirdMarginal p := by
  classical
  let := Fintype.ofFinite alpha
  let := Fintype.ofFinite beta
  ext c
  rw [sndMarginal_apply, thirdMarginal_apply]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [fstThirdMarginal_apply]

/-- The second marginal of the `(B,C)` law is the law of `C`. -/
@[simp]
theorem sndMarginal_sndThirdMarginal
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Finite alpha] [Finite beta]
    (p : PMF (alpha × beta × gamma)) :
    sndMarginal (sndThirdMarginal p) = thirdMarginal p := by
  classical
  let := Fintype.ofFinite alpha
  let := Fintype.ofFinite beta
  ext c
  rw [sndMarginal_apply, thirdMarginal_apply]
  calc
    (∑ b : beta, sndThirdMarginal p (b, c))
        = ∑ b : beta, ∑ a : alpha, p (a, b, c) := by
          apply Finset.sum_congr rfl
          intro b _hb
          rw [sndThirdMarginal_apply]
    _ = ∑ a : alpha, ∑ b : beta, p (a, b, c) := by
          rw [Finset.sum_comm]

/--
The first marginal of `P_{A,B|C=c}` is the conditional law `P_{A|C=c}`.
-/
theorem fstMarginal_condFstSndGivenThird
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta × gamma)) (c : gamma)
    (hc : thirdMarginal p c ≠ 0) :
    fstMarginal (condFstSndGivenThird p c hc) =
      condFstGivenSnd (fstThirdMarginal p) c
        (by simpa [sndMarginal_fstThirdMarginal (p := p)] using hc) := by
  classical
  ext a
  rw [fstMarginal_apply]
  rw [condFstGivenSnd_apply]
  rw [fstThirdMarginal_apply]
  rw [sndMarginal_fstThirdMarginal]
  calc
    (∑ b : beta, condFstSndGivenThird p c hc (a, b))
        = ∑ b : beta, p (a, b, c) / thirdMarginal p c := by
          apply Finset.sum_congr rfl
          intro b _hb
          rw [condFstSndGivenThird_apply]
    _ = ∑ b : beta, p (a, b, c) * (thirdMarginal p c)⁻¹ := by
          rfl
    _ = (∑ b : beta, p (a, b, c)) * (thirdMarginal p c)⁻¹ := by
          rw [Finset.sum_mul]
    _ = (∑ b : beta, p (a, b, c)) / thirdMarginal p c := by
          rfl

/--
The second marginal of `P_{A,B|C=c}` is the conditional law `P_{B|C=c}`.
-/
theorem sndMarginal_condFstSndGivenThird
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta × gamma)) (c : gamma)
    (hc : thirdMarginal p c ≠ 0) :
    sndMarginal (condFstSndGivenThird p c hc) =
      condFstGivenSnd (sndThirdMarginal p) c
        (by simpa [sndMarginal_sndThirdMarginal (p := p)] using hc) := by
  classical
  ext b
  rw [sndMarginal_apply]
  rw [condFstGivenSnd_apply]
  rw [sndThirdMarginal_apply]
  rw [sndMarginal_sndThirdMarginal]
  calc
    (∑ a : alpha, condFstSndGivenThird p c hc (a, b))
        = ∑ a : alpha, p (a, b, c) / thirdMarginal p c := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [condFstSndGivenThird_apply]
    _ = ∑ a : alpha, p (a, b, c) * (thirdMarginal p c)⁻¹ := by
          rfl
    _ = (∑ a : alpha, p (a, b, c)) * (thirdMarginal p c)⁻¹ := by
          rw [Finset.sum_mul]
    _ = (∑ a : alpha, p (a, b, c)) / thirdMarginal p c := by
          rfl

/--
The conditional law of `(A,B)` given `C=c`, obtained by conditioning the
reassociated law `((A,B),C)`, is the same as `condFstSndGivenThird`.
-/
theorem condFstGivenSnd_pairThirdLaw_eq_condFstSndGivenThird
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta × gamma)) (c : gamma)
    (hc : thirdMarginal p c ≠ 0) :
    condFstGivenSnd (pairThirdLaw p) c
        (by simpa [sndMarginal_pairThirdLaw (p := p)] using hc) =
      condFstSndGivenThird p c hc := by
  classical
  ext x
  rcases x with ⟨a, b⟩
  rw [condFstGivenSnd_apply, condFstSndGivenThird_apply]
  rw [pairThirdLaw_apply, sndMarginal_pairThirdLaw]

/--
Conditional mutual information of the fiber over `C=c`.

The value is zero when `P_C(c)=0`; otherwise it is the mutual information of
the conditional joint law `P_{A,B|C=c}`.
-/
def condMutualInfoFstSndGivenThird
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta × gamma)) (c : gamma) : Real :=
  if hc : thirdMarginal p c = 0 then
    0
  else
    mutualInfo (condFstSndGivenThird p c hc)

/-- Zero-marginal conditioning atoms contribute zero fiber mutual information. -/
@[simp]
theorem condMutualInfoFstSndGivenThird_of_thirdMarginal_eq_zero
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta × gamma)) {c : gamma}
    (hc : thirdMarginal p c = 0) :
    condMutualInfoFstSndGivenThird p c = 0 := by
  rw [condMutualInfoFstSndGivenThird, dite_eq_left hc]

/--
On nonzero third-coordinate atoms, the fiber CMI is the mutual information of
`P_{A,B|C=c}`.
-/
theorem condMutualInfoFstSndGivenThird_of_thirdMarginal_ne_zero
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta × gamma)) {c : gamma}
    (hc : thirdMarginal p c ≠ 0) :
    condMutualInfoFstSndGivenThird p c =
      mutualInfo (condFstSndGivenThird p c hc) := by
  rw [condMutualInfoFstSndGivenThird, dite_eq_right hc]

/--
Conditional mutual information can be rewritten as
`H(A|C) + H(B|C) - H(A,B|C)`.
-/
theorem condMutualInfo_eq_condEntropy_marginals
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condMutualInfo p =
      condEntropy (fstThirdMarginal p) + condEntropy (sndThirdMarginal p) -
        condEntropy (pairThirdLaw p) := by
  rw [condMutualInfo_eq, condEntropy_eq, condEntropy_eq, condEntropy_eq]
  rw [sndMarginal_fstThirdMarginal, sndMarginal_sndThirdMarginal,
    sndMarginal_pairThirdLaw, entropy_pairThirdLaw]
  ring

/--
On a nonzero third-coordinate atom, fiber CMI is the entropy identity for the
three conditional fibers:
`I(A;B | C=c) = H(A|C=c) + H(B|C=c) - H(A,B|C=c)`.
-/
theorem condMutualInfoFstSndGivenThird_eq_entropy_fibers_of_ne_zero
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta × gamma)) {c : gamma}
    (hc : thirdMarginal p c ≠ 0) :
    condMutualInfoFstSndGivenThird p c =
      condEntropyFstGivenSnd (fstThirdMarginal p) c +
        condEntropyFstGivenSnd (sndThirdMarginal p) c -
          condEntropyFstGivenSnd (pairThirdLaw p) c := by
  classical
  let hfst : sndMarginal (fstThirdMarginal p) c ≠ 0 := by
    simpa [sndMarginal_fstThirdMarginal (p := p)] using hc
  let hsnd : sndMarginal (sndThirdMarginal p) c ≠ 0 := by
    simpa [sndMarginal_sndThirdMarginal (p := p)] using hc
  let hpair : sndMarginal (pairThirdLaw p) c ≠ 0 := by
    simpa [sndMarginal_pairThirdLaw (p := p)] using hc
  rw [condMutualInfoFstSndGivenThird_of_thirdMarginal_ne_zero p hc]
  rw [mutualInfo_eq]
  rw [condEntropyFstGivenSnd_of_sndMarginal_ne_zero (fstThirdMarginal p) hfst]
  rw [condEntropyFstGivenSnd_of_sndMarginal_ne_zero (sndThirdMarginal p) hsnd]
  rw [condEntropyFstGivenSnd_of_sndMarginal_ne_zero (pairThirdLaw p) hpair]
  rw [← fstMarginal_condFstSndGivenThird p c hc]
  rw [← sndMarginal_condFstSndGivenThird p c hc]
  rw [condFstGivenSnd_pairThirdLaw_eq_condFstSndGivenThird p c hc]

/--
Weighted pointwise bridge between fiber CMI and the three conditional entropy
fibers. The zero-marginal case is killed by the factor `P_C(c)`.
-/
theorem thirdMarginal_toReal_mul_condMutualInfoFstSndGivenThird
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta × gamma)) (c : gamma) :
    (thirdMarginal p c).toReal * condMutualInfoFstSndGivenThird p c =
      (thirdMarginal p c).toReal *
        (condEntropyFstGivenSnd (fstThirdMarginal p) c +
          condEntropyFstGivenSnd (sndThirdMarginal p) c -
            condEntropyFstGivenSnd (pairThirdLaw p) c) := by
  by_cases hc : thirdMarginal p c = 0
  · rw [condMutualInfoFstSndGivenThird_of_thirdMarginal_eq_zero p hc, hc]
    simp
  · rw [condMutualInfoFstSndGivenThird_eq_entropy_fibers_of_ne_zero p hc]

/--
Expected conditional mutual information formula:

`I(A;B | C) = sum_c P_C(c) I(A;B | C=c)`.

The fiber term is zero on zero-marginal `c` and otherwise the mutual
information of `P_{A,B|C=c}`.
-/
theorem condMutualInfo_eq_sum_thirdMarginal_mul_condMutualInfoFstSndGivenThird
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condMutualInfo p =
      ∑ c : gamma,
        (thirdMarginal p c).toReal * condMutualInfoFstSndGivenThird p c := by
  classical
  rw [condMutualInfo_eq_condEntropy_marginals]
  rw [condEntropy_eq_sum_sndMarginal_mul_condEntropyFstGivenSnd (fstThirdMarginal p)]
  rw [condEntropy_eq_sum_sndMarginal_mul_condEntropyFstGivenSnd (sndThirdMarginal p)]
  rw [condEntropy_eq_sum_sndMarginal_mul_condEntropyFstGivenSnd (pairThirdLaw p)]
  rw [sndMarginal_fstThirdMarginal, sndMarginal_sndThirdMarginal,
    sndMarginal_pairThirdLaw]
  calc
    (∑ c : gamma, (thirdMarginal p c).toReal *
          condEntropyFstGivenSnd (fstThirdMarginal p) c) +
        (∑ c : gamma, (thirdMarginal p c).toReal *
          condEntropyFstGivenSnd (sndThirdMarginal p) c) -
        (∑ c : gamma, (thirdMarginal p c).toReal *
          condEntropyFstGivenSnd (pairThirdLaw p) c)
        =
        ∑ c : gamma, (thirdMarginal p c).toReal *
          (condEntropyFstGivenSnd (fstThirdMarginal p) c +
            condEntropyFstGivenSnd (sndThirdMarginal p) c -
              condEntropyFstGivenSnd (pairThirdLaw p) c) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro c _hc
          ring
    _ = ∑ c : gamma,
        (thirdMarginal p c).toReal * condMutualInfoFstSndGivenThird p c := by
          apply Finset.sum_congr rfl
          intro c _hc
          exact (thirdMarginal_toReal_mul_condMutualInfoFstSndGivenThird p c).symm

end

end Shannon
end LeanInfoTheory
