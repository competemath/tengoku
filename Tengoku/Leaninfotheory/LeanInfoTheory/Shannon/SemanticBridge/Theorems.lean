/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.SemanticBridge.KL

/-!
# First semantic theorem API for finite Shannon information measures

This file collects the first user-facing semantic consequences of the bridge
layer.  The theorems here are stated in the finite-PMF vocabulary of
`LeanInfoTheory.Shannon`, while their proofs reuse the KL and conditional-law
bridges from the lower semantic bridge files.

The main results are:

* `mutualInfo_nonneg`: `0 <= I(A;B)`;
* `condEntropy_nonneg`: `0 <= H(A|B)`;
* `condMutualInfo_nonneg`: `0 <= I(A;B|C)`;
* `entropy_map_le`: deterministic processing cannot increase entropy;
* `condEntropyOf_comp_le`: deterministic processing cannot increase conditional entropy;
* `mutualInfoOf_comp_le`: deterministic processing cannot increase mutual information;
* `mutualInfo_le_entropy_fstMarginal`: mutual information is bounded by marginal entropy;
* `entropy_le_entropy_fstMarginal_add_entropy_sndMarginal`: joint entropy is subadditive;
* `mutualInfo_chain_rule_fst`: `I(A;B,C) = I(A;C) + I(A;B|C)`;
* `condMutualInfo_eq_condEntropy_fstThirdMarginal_sub_condEntropy`:
  `I(A;B|C) = H(A|C) - H(A|B,C)`;
* `condMutualInfoOf_le_condEntropyOf_left`: `I(X;Y|Z) <= H(X|Z)`;
* `condEntropyOf_pair_le_condEntropyOf_add_condEntropyOf`:
  `H(X,Y|Z) <= H(X|Z) + H(Y|Z)`;
* `condEntropy_le_condEntropy_fstThirdMarginal`: `H(A|B,C) <= H(A|C)`.
-/

namespace LeanInfoTheory
namespace Shannon

open scoped BigOperators

noncomputable section

universe u v w

/-! ## Nonnegativity -/

/--
Mutual information is nonnegative:

`0 <= I(A;B)`.

The proof passes through the semantic bridge
`I(A;B) = D(P_AB || P_A x P_B)` and then uses nonnegativity of the real
coercion of an `ENNReal` KL divergence.
-/
theorem mutualInfo_nonneg {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] (p : PMF (alpha × beta)) :
    0 <= mutualInfo p := by
  let : MeasurableSpace (alpha × beta) := ⊤
  have : MeasurableSingletonClass (alpha × beta) := ⟨fun _ => trivial⟩
  rw [mutualInfo_eq_toReal_klDiv_joint_indepProd (p := p)]
  exact ENNReal.toReal_nonneg

/--
Fiber conditional entropy is nonnegative:

`0 <= H(A | B=b)`.

On zero-mass fibers this is `0 <= 0`; on nonzero fibers it reduces to entropy
nonnegativity for the conditional law `P_{A|B=b}`.
-/
theorem condEntropyFstGivenSnd_nonneg
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] (p : PMF (alpha × beta)) (b : beta) :
    0 <= condEntropyFstGivenSnd p b := by
  by_cases hb : sndMarginal p b = 0
  · rw [condEntropyFstGivenSnd_of_sndMarginal_eq_zero p hb]
  · rw [condEntropyFstGivenSnd_of_sndMarginal_ne_zero p hb]
    exact entropy_nonneg (condFstGivenSnd p b hb)

/--
On a nonzero conditioning fiber, conditional entropy is zero exactly when the
canonical conditional PMF is pure.
-/
theorem condEntropyFstGivenSnd_eq_zero_iff_of_sndMarginal_ne_zero
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] (p : PMF (alpha × beta)) {b : beta}
    (hb : sndMarginal p b ≠ 0) :
    condEntropyFstGivenSnd p b = 0 ↔
      ∃ a, condFstGivenSnd p b hb = PMF.pure a := by
  rw [condEntropyFstGivenSnd_of_sndMarginal_ne_zero p hb]
  exact entropy_eq_zero_iff (condFstGivenSnd p b hb)

/--
Conditional entropy is nonnegative:

`0 <= H(A | B)`.

The proof uses the finite semantic bridge

`H(A | B) = sum_b P_B(b) * H(P_{A|B=b})`,

then every summand is nonnegative.
-/
theorem condEntropy_nonneg {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] (p : PMF (alpha × beta)) :
    0 <= condEntropy p := by
  rw [condEntropy_eq_sum_sndMarginal_mul_condEntropyFstGivenSnd]
  exact Finset.sum_nonneg fun b _hb =>
    mul_nonneg (PMF.toReal_nonneg (sndMarginal p) b)
      (condEntropyFstGivenSnd_nonneg p b)

/-- Conditional entropy of finite-valued random variables is nonnegative. -/
theorem condEntropyOf_nonneg
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    0 <= condEntropyOf p X Y :=
  condEntropy_nonneg (p.map fun omega => (X omega, Y omega))

/-! ## Zero conditional entropy and functional dependence -/

/--
Conditional entropy is zero exactly when the first coordinate is a function of
the second coordinate on the support of the joint PMF.
-/
theorem condEntropy_eq_zero_iff_exists_function
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) :
    condEntropy p = 0 ↔
      ∃ f : beta -> alpha, ∀ z, z ∈ p.support -> z.1 = f z.2 := by
  classical
  constructor
  · intro hzero
    have hsum :
        (∑ b : beta,
          (sndMarginal p b).toReal * condEntropyFstGivenSnd p b) = 0 := by
      simpa only [condEntropy_eq_sum_sndMarginal_mul_condEntropyFstGivenSnd] using hzero
    have hproduct_zero (b : beta) :
        (sndMarginal p b).toReal * condEntropyFstGivenSnd p b = 0 := by
      have hnonneg :
          ∀ b : beta, b ∈ (Finset.univ : Finset beta) ->
            0 <= (sndMarginal p b).toReal * condEntropyFstGivenSnd p b := by
        intro b _hb
        exact mul_nonneg (PMF.toReal_nonneg (sndMarginal p) b)
          (condEntropyFstGivenSnd_nonneg p b)
      exact
        (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum b (Finset.mem_univ b)
    have hpure (b : beta) (hb : sndMarginal p b ≠ 0) :
        ∃ a, condFstGivenSnd p b hb = PMF.pure a := by
      have hweight_ne : (sndMarginal p b).toReal ≠ 0 :=
        ne_of_gt (ENNReal.toReal_pos hb ((sndMarginal p).apply_ne_top b))
      have hfiber_zero : condEntropyFstGivenSnd p b = 0 :=
        (mul_eq_zero.1 (hproduct_zero b)).resolve_left hweight_ne
      exact
        (condEntropyFstGivenSnd_eq_zero_iff_of_sndMarginal_ne_zero p hb).1
          hfiber_zero
    obtain ⟨z0, _hz0⟩ := p.support_nonempty
    let a0 : alpha := z0.1
    let f : beta -> alpha := fun b =>
      if hb : sndMarginal p b = 0 then a0 else Classical.choose (hpure b hb)
    refine ⟨f, ?_⟩
    intro z hz
    rcases z with ⟨a, b⟩
    have hpab : p (a, b) ≠ 0 := hz
    have hb : sndMarginal p b ≠ 0 := sndMarginal_ne_zero_of_apply_ne_zero p hpab
    have hpure_eq :
        condFstGivenSnd p b hb = PMF.pure (Classical.choose (hpure b hb)) :=
      Classical.choose_spec (hpure b hb)
    have hcond_ne : condFstGivenSnd p b hb a ≠ 0 :=
      (condFstGivenSnd_apply_ne_zero_iff p b hb a).2 hpab
    have hpure_ne : PMF.pure (Classical.choose (hpure b hb)) a ≠ 0 := by
      rw [← hpure_eq]
      exact hcond_ne
    have ha : a = Classical.choose (hpure b hb) := by
      exact
        (PMF.mem_support_pure_iff (Classical.choose (hpure b hb)) a).1
          ((PMF.mem_support_iff (PMF.pure (Classical.choose (hpure b hb))) a).2 hpure_ne)
    have hfb : f b = Classical.choose (hpure b hb) := by
      dsimp only [f]
      rw [dite_eq_right hb]
    exact ha.trans hfb.symm
  · rintro ⟨f, hf⟩
    rw [condEntropy_eq_sum_sndMarginal_mul_condEntropyFstGivenSnd]
    apply Finset.sum_eq_zero
    intro b _hbmem
    by_cases hb : sndMarginal p b = 0
    · rw [condEntropyFstGivenSnd_of_sndMarginal_eq_zero p hb, mul_zero]
    · have hsubset :
          (condFstGivenSnd p b hb).support ⊆ ({f b} : Set alpha) := by
        intro a ha
        have hcond_ne : condFstGivenSnd p b hb a ≠ 0 :=
          (PMF.mem_support_iff (condFstGivenSnd p b hb) a).1 ha
        have hpab : p (a, b) ≠ 0 :=
          (condFstGivenSnd_apply_ne_zero_iff p b hb a).1 hcond_ne
        exact Set.mem_singleton_iff.2 (hf (a, b) ((p.mem_support_iff (a, b)).2 hpab))
      have hsupp : (condFstGivenSnd p b hb).support = ({f b} : Set alpha) := by
        apply Set.Subset.antisymm hsubset
        intro x hx
        have hx_eq : x = f b := Set.mem_singleton_iff.1 hx
        subst x
        obtain ⟨a, ha⟩ := (condFstGivenSnd p b hb).support_nonempty
        have ha_eq : a = f b := Set.mem_singleton_iff.1 (hsubset ha)
        rw [ha_eq] at ha
        exact ha
      have hpure_eq : condFstGivenSnd p b hb = PMF.pure (f b) :=
        (PMF.eq_pure_iff_support_eq_singleton (condFstGivenSnd p b hb) (f b)).2 hsupp
      have hfiber_zero : condEntropyFstGivenSnd p b = 0 :=
        (condEntropyFstGivenSnd_eq_zero_iff_of_sndMarginal_ne_zero p hb).2
          ⟨f b, hpure_eq⟩
      rw [hfiber_zero, mul_zero]

/--
Conditional entropy of finite-valued random variables is zero exactly when the
first variable is a function of the second on the source PMF support.
-/
theorem condEntropyOf_eq_zero_iff_exists_function
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    condEntropyOf p X Y = 0 ↔
      ∃ f : beta -> alpha,
        ∀ omega, omega ∈ p.support -> X omega = f (Y omega) := by
  change condEntropy (p.map fun omega => (X omega, Y omega)) = 0 ↔ _
  constructor
  · intro hzero
    obtain ⟨f, hf⟩ :=
      (condEntropy_eq_zero_iff_exists_function
        (p.map fun omega => (X omega, Y omega))).1 hzero
    refine ⟨f, ?_⟩
    intro omega homega
    apply hf (X omega, Y omega)
    rw [PMF.support_map]
    exact ⟨omega, homega, rfl⟩
  · rintro ⟨f, hf⟩
    apply
      (condEntropy_eq_zero_iff_exists_function
        (p.map fun omega => (X omega, Y omega))).2
    refine ⟨f, ?_⟩
    intro z hz
    rw [PMF.support_map] at hz
    obtain ⟨omega, homega, rfl⟩ := hz
    exact hf omega homega

/-- A deterministic function of `Y` has zero conditional entropy given `Y`. -/
theorem condEntropyOf_comp_eq_zero
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (Y : omega -> beta) (f : beta -> alpha) :
    condEntropyOf p (fun omega => f (Y omega)) Y = 0 := by
  exact
    (condEntropyOf_eq_zero_iff_exists_function p
      (fun omega => f (Y omega)) Y).2 ⟨f, fun _ _ => rfl⟩

/-- A finite-valued random variable has zero conditional entropy given itself. -/
theorem condEntropyOf_self_eq_zero
    {omega : Type u} {alpha : Type v} [Fintype alpha]
    (p : PMF omega) (X : omega -> alpha) :
    condEntropyOf p X X = 0 := by
  exact
    (condEntropyOf_eq_zero_iff_exists_function p X X).2
      ⟨id, fun _ _ => rfl⟩

/--
Joint entropy equals the entropy of the second marginal exactly when the first
coordinate is a function of the second on the joint support.
-/
theorem entropy_eq_entropy_sndMarginal_iff_exists_function
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) :
    entropy p = entropy (sndMarginal p) ↔
      ∃ f : beta -> alpha, ∀ z, z ∈ p.support -> z.1 = f z.2 := by
  constructor
  · intro h
    have hadd : entropy (sndMarginal p) + condEntropy p = entropy (sndMarginal p) :=
      (entropy_eq_entropy_sndMarginal_add_condEntropy p).symm.trans h
    have hzero : condEntropy p = 0 := by
      have hadd0 :
          entropy (sndMarginal p) + condEntropy p = entropy (sndMarginal p) + 0 := by
        simpa using hadd
      exact add_left_cancel hadd0
    exact (condEntropy_eq_zero_iff_exists_function p).1 hzero
  · intro h
    have hzero := (condEntropy_eq_zero_iff_exists_function p).2 h
    calc
      entropy p = entropy (sndMarginal p) + condEntropy p :=
        entropy_eq_entropy_sndMarginal_add_condEntropy p
      _ = entropy (sndMarginal p) := by rw [hzero, add_zero]

/--
`H(X,Y) = H(Y)` exactly when `X` is a function of `Y` on the source PMF
support.
-/
theorem jointEntropyOf_eq_entropyOf_iff_exists_function
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    jointEntropyOf p X Y = entropyOf p Y ↔
      ∃ f : beta -> alpha,
        ∀ omega, omega ∈ p.support -> X omega = f (Y omega) := by
  constructor
  · intro h
    have hadd : entropyOf p Y + condEntropyOf p X Y = entropyOf p Y :=
      (jointEntropyOf_eq_entropyOf_add_condEntropyOf p X Y).symm.trans h
    have hzero : condEntropyOf p X Y = 0 := by
      have hadd0 :
          entropyOf p Y + condEntropyOf p X Y = entropyOf p Y + 0 := by
        simpa using hadd
      exact add_left_cancel hadd0
    exact (condEntropyOf_eq_zero_iff_exists_function p X Y).1 hzero
  · intro h
    have hzero := (condEntropyOf_eq_zero_iff_exists_function p X Y).2 h
    calc
      jointEntropyOf p X Y = entropyOf p Y + condEntropyOf p X Y :=
        jointEntropyOf_eq_entropyOf_add_condEntropyOf p X Y
      _ = entropyOf p Y := by rw [hzero, add_zero]

/-! ## Deterministic entropy processing -/

private theorem entropy_eq_entropy_map_add_condEntropyOf_id
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta]
    (p : PMF alpha) (f : alpha -> beta) :
    entropy p = entropy (p.map f) + condEntropyOf p id f := by
  have hjoint : jointEntropyOf p f id = entropyOf p id :=
    (jointEntropyOf_eq_entropyOf_iff_exists_function p f id).2
      ⟨f, fun _ _ => rfl⟩
  calc
    entropy p = entropyOf p id := (entropyOf_id p).symm
    _ = jointEntropyOf p f id := hjoint.symm
    _ = entropyOf p f + condEntropyOf p id f :=
      jointEntropyOf_eq_entropyOf_add_condEntropyOf_swap p f id
    _ = entropy (p.map f) + condEntropyOf p id f := rfl

/-- Applying a deterministic map to a finite PMF cannot increase entropy. -/
theorem entropy_map_le
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta]
    (p : PMF alpha) (f : alpha -> beta) :
    entropy (p.map f) <= entropy p := by
  have hdecomp := entropy_eq_entropy_map_add_condEntropyOf_id p f
  have hnonneg := condEntropyOf_nonneg p id f
  linarith

/--
Applying a deterministic map preserves entropy exactly when it is injective on
the support of the source PMF.
-/
theorem entropy_map_eq_iff_injOn_support
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta]
    (p : PMF alpha) (f : alpha -> beta) :
    entropy (p.map f) = entropy p ↔ Set.InjOn f p.support := by
  have hdecomp := entropy_eq_entropy_map_add_condEntropyOf_id p f
  constructor
  · intro heq
    have hzero : condEntropyOf p id f = 0 := by
      linarith
    obtain ⟨g, hg⟩ :=
      (condEntropyOf_eq_zero_iff_exists_function p id f).1 hzero
    intro a ha a' ha' hfa
    calc
      a = g (f a) := hg a ha
      _ = g (f a') := congrArg g hfa
      _ = a' := (hg a' ha').symm
  · intro hinj
    obtain ⟨a0, _ha0⟩ := p.support_nonempty
    let : Nonempty alpha := ⟨a0⟩
    have hzero : condEntropyOf p id f = 0 :=
      (condEntropyOf_eq_zero_iff_exists_function p id f).2
        ⟨Function.invFunOn f p.support,
          fun a ha => (hinj.leftInvOn_invFunOn ha).symm⟩
    linarith

/-- Deterministic post-processing of a finite-valued variable cannot increase entropy. -/
theorem entropyOf_comp_le
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (f : alpha -> beta) :
    entropyOf p (fun omega => f (X omega)) <= entropyOf p X := by
  simpa [entropyOf, Function.comp_def, PMF.map_comp] using
    entropy_map_le (p.map X) f

/--
Deterministic post-processing preserves random-variable entropy exactly when
the map is injective on the support of the law of the original variable.
-/
theorem entropyOf_comp_eq_iff_injOn_support
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (f : alpha -> beta) :
    entropyOf p (fun omega => f (X omega)) = entropyOf p X ↔
      Set.InjOn f (p.map X).support := by
  simpa [entropyOf, Function.comp_def, PMF.map_comp] using
    entropy_map_eq_iff_injOn_support (p.map X) f

/--
Conditional deterministic chain rule:
`H(X|Z) = H(f(X)|Z) + H(X|f(X),Z)`.
-/
theorem condEntropyOf_deterministic_chain_rule
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Z : omega -> gamma)
    (f : alpha -> beta) :
    condEntropyOf p X Z =
      condEntropyOf p (fun omega => f (X omega)) Z +
        condEntropyOf p X (fun omega => (f (X omega), Z omega)) := by
  have hzero :
      condEntropyOf p (fun omega => f (X omega))
        (fun omega => (X omega, Z omega)) = 0 := by
    simpa using
      condEntropyOf_comp_eq_zero p (fun omega => (X omega, Z omega))
        (fun z => f z.1)
  have hjoint :
      condEntropyOf p (fun omega => (X omega, f (X omega))) Z =
        condEntropyOf p X Z := by
    calc
      condEntropyOf p (fun omega => (X omega, f (X omega))) Z =
          condEntropyOf p X Z +
            condEntropyOf p (fun omega => f (X omega))
              (fun omega => (X omega, Z omega)) :=
        condEntropyOf_pair_chain_rule_swap p X (fun omega => f (X omega)) Z
      _ = condEntropyOf p X Z := by rw [hzero, add_zero]
  calc
    condEntropyOf p X Z =
        condEntropyOf p (fun omega => (X omega, f (X omega))) Z := hjoint.symm
    _ = condEntropyOf p (fun omega => f (X omega)) Z +
          condEntropyOf p X (fun omega => (f (X omega), Z omega)) :=
      condEntropyOf_pair_chain_rule p X (fun omega => f (X omega)) Z

/-- Deterministic post-processing cannot increase conditional entropy. -/
theorem condEntropyOf_comp_le
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Z : omega -> gamma)
    (f : alpha -> beta) :
    condEntropyOf p (fun omega => f (X omega)) Z <= condEntropyOf p X Z := by
  have hdecomp := condEntropyOf_deterministic_chain_rule p X Z f
  have hnonneg :=
    condEntropyOf_nonneg p X (fun omega => (f (X omega), Z omega))
  linarith

/--
Deterministic post-processing preserves conditional entropy exactly when `X`
is recoverable from `(f(X), Z)` on the source PMF support.
-/
theorem condEntropyOf_comp_eq_iff_exists_recovery
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Z : omega -> gamma)
    (f : alpha -> beta) :
    condEntropyOf p (fun omega => f (X omega)) Z = condEntropyOf p X Z ↔
      ∃ g : beta × gamma -> alpha,
        ∀ omega, omega ∈ p.support -> X omega = g (f (X omega), Z omega) := by
  have hdecomp := condEntropyOf_deterministic_chain_rule p X Z f
  constructor
  · intro heq
    have hzero :
        condEntropyOf p X (fun omega => (f (X omega), Z omega)) = 0 := by
      linarith
    exact
      (condEntropyOf_eq_zero_iff_exists_function p X
        (fun omega => (f (X omega), Z omega))).1 hzero
  · intro hrecover
    have hzero :
        condEntropyOf p X (fun omega => (f (X omega), Z omega)) = 0 :=
      (condEntropyOf_eq_zero_iff_exists_function p X
        (fun omega => (f (X omega), Z omega))).2 hrecover
    linarith

/-- Applying a deterministic map to the first coordinate cannot increase `H(A|C)`. -/
theorem condEntropy_map_fst_le
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × gamma)) (f : alpha -> beta) :
    condEntropy (p.map fun z => (f z.1, z.2)) <= condEntropy p := by
  have hid : p.map (fun z : alpha × gamma => (z.1, z.2)) = p := by
    calc
      p.map (fun z : alpha × gamma => (z.1, z.2)) = p.map id := by
        exact congrArg (fun h => p.map h) (by
          funext z
          exact Prod.eta z)
      _ = p := PMF.map_id p
  simpa only [condEntropyOf, hid] using
    condEntropyOf_comp_le p Prod.fst Prod.snd f

/--
The first-coordinate map preserves `H(A|C)` exactly when `A` is recoverable
from `(f(A), C)` on the joint support.
-/
theorem condEntropy_map_fst_eq_iff_exists_recovery
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × gamma)) (f : alpha -> beta) :
    condEntropy (p.map fun z => (f z.1, z.2)) = condEntropy p ↔
      ∃ g : beta × gamma -> alpha,
        ∀ z, z ∈ p.support -> z.1 = g (f z.1, z.2) := by
  have hid : p.map (fun z : alpha × gamma => (z.1, z.2)) = p := by
    calc
      p.map (fun z : alpha × gamma => (z.1, z.2)) = p.map id := by
        exact congrArg (fun h => p.map h) (by
          funext z
          exact Prod.eta z)
      _ = p := PMF.map_id p
  simpa only [condEntropyOf, hid] using
    condEntropyOf_comp_eq_iff_exists_recovery p Prod.fst Prod.snd f

/-! ## Pair-level entropy and mutual-information inequalities -/

/-- Conditioning reduces entropy: `H(A|B) <= H(A)`. -/
theorem condEntropy_le_entropy_fstMarginal
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) :
    condEntropy p <= entropy (fstMarginal p) := by
  have hnonneg := mutualInfo_nonneg p
  rw [mutualInfo_eq_entropy_fstMarginal_sub_condEntropy] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- Mutual information is at most the entropy of the first marginal. -/
theorem mutualInfo_le_entropy_fstMarginal
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) :
    mutualInfo p <= entropy (fstMarginal p) := by
  calc
    mutualInfo p = entropy (fstMarginal p) - condEntropy p :=
      mutualInfo_eq_entropy_fstMarginal_sub_condEntropy p
    _ <= entropy (fstMarginal p) :=
      sub_le_self _ (condEntropy_nonneg p)

/-- Mutual information is at most the entropy of the second marginal. -/
theorem mutualInfo_le_entropy_sndMarginal
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) :
    mutualInfo p <= entropy (sndMarginal p) := by
  calc
    mutualInfo p =
        entropy (sndMarginal p) - condEntropy (p.map Prod.swap) :=
      mutualInfo_eq_entropy_sndMarginal_sub_condEntropy_swap p
    _ <= entropy (sndMarginal p) :=
      sub_le_self _ (condEntropy_nonneg (p.map Prod.swap))

/-- The entropy of the first marginal is at most the joint entropy. -/
theorem entropy_fstMarginal_le_entropy
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) :
    entropy (fstMarginal p) <= entropy p := by
  calc
    entropy (fstMarginal p) <=
        entropy (fstMarginal p) + condEntropy (p.map Prod.swap) :=
      le_add_of_nonneg_right (condEntropy_nonneg (p.map Prod.swap))
    _ = entropy p :=
      (entropy_eq_entropy_fstMarginal_add_condEntropy_swap p).symm

/-- The entropy of the second marginal is at most the joint entropy. -/
theorem entropy_sndMarginal_le_entropy
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) :
    entropy (sndMarginal p) <= entropy p := by
  calc
    entropy (sndMarginal p) <= entropy (sndMarginal p) + condEntropy p :=
      le_add_of_nonneg_right (condEntropy_nonneg p)
    _ = entropy p :=
      (entropy_eq_entropy_sndMarginal_add_condEntropy p).symm

/-- Joint entropy is subadditive: `H(A,B) <= H(A) + H(B)`. -/
theorem entropy_le_entropy_fstMarginal_add_entropy_sndMarginal
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) :
    entropy p <= entropy (fstMarginal p) + entropy (sndMarginal p) := by
  have hnonneg := mutualInfo_nonneg p
  rw [mutualInfo_eq] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- Random-variable conditioning reduces entropy: `H(X|Y) <= H(X)`. -/
theorem condEntropyOf_le_entropyOf
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    condEntropyOf p X Y <= entropyOf p X := by
  simpa [condEntropyOf, entropyOf] using
    condEntropy_le_entropy_fstMarginal
      (p.map fun omega => (X omega, Y omega))

/-- Random-variable mutual information is at most `H(X)`. -/
theorem mutualInfoOf_le_entropyOf_left
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    mutualInfoOf p X Y <= entropyOf p X := by
  simpa [mutualInfoOf, entropyOf] using
    mutualInfo_le_entropy_fstMarginal
      (p.map fun omega => (X omega, Y omega))

/-- Random-variable mutual information is at most `H(Y)`. -/
theorem mutualInfoOf_le_entropyOf_right
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    mutualInfoOf p X Y <= entropyOf p Y := by
  simpa [mutualInfoOf, entropyOf] using
    mutualInfo_le_entropy_sndMarginal
      (p.map fun omega => (X omega, Y omega))

/-- The entropy of `X` is at most the joint entropy `H(X,Y)`. -/
theorem entropyOf_le_jointEntropyOf
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    entropyOf p X <= jointEntropyOf p X Y := by
  simpa [entropyOf, jointEntropyOf] using
    entropy_fstMarginal_le_entropy
      (p.map fun omega => (X omega, Y omega))

/-- The entropy of `Y` is at most the joint entropy `H(X,Y)`. -/
theorem entropyOf_le_jointEntropyOf_swap
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    entropyOf p Y <= jointEntropyOf p X Y := by
  simpa [entropyOf, jointEntropyOf] using
    entropy_sndMarginal_le_entropy
      (p.map fun omega => (X omega, Y omega))

/-- Random-variable joint entropy is subadditive: `H(X,Y) <= H(X) + H(Y)`. -/
theorem jointEntropyOf_le_entropyOf_add_entropyOf
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    jointEntropyOf p X Y <= entropyOf p X + entropyOf p Y := by
  simpa [entropyOf, jointEntropyOf] using
    entropy_le_entropy_fstMarginal_add_entropy_sndMarginal
      (p.map fun omega => (X omega, Y omega))

/-! ## Textbook-Facing Pair-Inequality Aliases -/

/-- Textbook-facing PMF alias for `H(A|B) <= H(A)`. -/
theorem condEntropy_le_entropy_left
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) :
    condEntropy p <= entropy (fstMarginal p) :=
  condEntropy_le_entropy_fstMarginal p

/-- Textbook-facing PMF alias for `I(A;B) <= H(A)`. -/
theorem mutualInfo_le_entropy_left
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) :
    mutualInfo p <= entropy (fstMarginal p) :=
  mutualInfo_le_entropy_fstMarginal p

/-- Textbook-facing PMF alias for `I(A;B) <= H(B)`. -/
theorem mutualInfo_le_entropy_right
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) :
    mutualInfo p <= entropy (sndMarginal p) :=
  mutualInfo_le_entropy_sndMarginal p

/-- Textbook-facing PMF alias for `H(A) <= H(A,B)`. -/
theorem entropy_left_le_jointEntropy
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) :
    entropy (fstMarginal p) <= entropy p :=
  entropy_fstMarginal_le_entropy p

/-- Textbook-facing PMF alias for `H(B) <= H(A,B)`. -/
theorem entropy_right_le_jointEntropy
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) :
    entropy (sndMarginal p) <= entropy p :=
  entropy_sndMarginal_le_entropy p

/-- Textbook-facing PMF alias for joint-entropy subadditivity. -/
theorem jointEntropy_le_add_marginalEntropy
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) :
    entropy p <= entropy (fstMarginal p) + entropy (sndMarginal p) :=
  entropy_le_entropy_fstMarginal_add_entropy_sndMarginal p

/-- Left-oriented alias for `H(X) <= H(X,Y)`. -/
theorem entropyOf_left_le_jointEntropyOf
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    entropyOf p X <= jointEntropyOf p X Y :=
  entropyOf_le_jointEntropyOf p X Y

/-- Right-oriented alias for `H(Y) <= H(X,Y)`. -/
theorem entropyOf_right_le_jointEntropyOf
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    entropyOf p Y <= jointEntropyOf p X Y :=
  entropyOf_le_jointEntropyOf_swap p X Y

/-- Short random-variable alias for joint-entropy subadditivity. -/
theorem jointEntropyOf_le_add_entropyOf
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    jointEntropyOf p X Y <= entropyOf p X + entropyOf p Y :=
  jointEntropyOf_le_entropyOf_add_entropyOf p X Y

/-! ## Conditional mutual information nonnegativity -/

/--
Fiber conditional mutual information is nonnegative:

`0 <= I(A;B | C=c)`.

On zero-mass fibers this is `0 <= 0`; on nonzero fibers it reduces to
`mutualInfo_nonneg` applied to the conditional joint law `P_{A,B|C=c}`.
-/
theorem condMutualInfoFstSndGivenThird_nonneg
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta × gamma)) (c : gamma) :
    0 <= condMutualInfoFstSndGivenThird p c := by
  by_cases hc : thirdMarginal p c = 0
  · rw [condMutualInfoFstSndGivenThird_of_thirdMarginal_eq_zero p hc]
  · rw [condMutualInfoFstSndGivenThird_of_thirdMarginal_ne_zero p hc]
    exact mutualInfo_nonneg (condFstSndGivenThird p c hc)

/--
Conditional mutual information is nonnegative:

`0 <= I(A;B | C)`.

We use the finite semantic bridge

`I(A;B | C) = sum_c P_C(c) * I(A;B | C=c)`,

then each summand is nonnegative because both `P_C(c)` and the fiber mutual
information are nonnegative.
-/
theorem condMutualInfo_nonneg
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    0 <= condMutualInfo p := by
  rw [condMutualInfo_eq_sum_thirdMarginal_mul_condMutualInfoFstSndGivenThird]
  exact Finset.sum_nonneg fun c _hc =>
    mul_nonneg (PMF.toReal_nonneg (thirdMarginal p) c)
      (condMutualInfoFstSndGivenThird_nonneg p c)

/-- Conditional mutual information of finite-valued random variables is nonnegative. -/
theorem condMutualInfoOf_nonneg
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    0 <= condMutualInfoOf p X Y Z := by
  exact condMutualInfo_nonneg (p.map fun omega => (X omega, Y omega, Z omega))

/-! ## Marginal reassociation lemmas -/

/--
Taking the first marginal after projecting `(A,B,C)` to `(A,C)` recovers the
first marginal of the original law:

`(P_AC)_A = P_A`.
-/
@[simp]
theorem fstMarginal_fstThirdMarginal
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta × gamma)) :
    fstMarginal (fstThirdMarginal p) = fstMarginal p := by
  simp [fstMarginal, fstThirdMarginal]

/--
Viewing a triple law as a joint law of `A` and `(B,C)`, the second marginal is
the same law as the explicit `(B,C)` marginal:

`P_{B,C} = sndMarginal P_{A,(B,C)}`.
-/
@[simp]
theorem sndMarginal_eq_sndThirdMarginal
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta × gamma)) :
    sndMarginal p = sndThirdMarginal p := by
  simp [sndMarginal, sndThirdMarginal]

/-! ## Chain rules -/

/--
First mutual-information chain rule:

`I(A;B,C) = I(A;C) + I(A;B | C)`.

In Lean's right-associated product convention, a PMF
`p : PMF (alpha × beta × gamma)` is also a joint law of `A` and `(B,C)`, so
`mutualInfo p` denotes `I(A;B,C)`.
-/
theorem mutualInfo_chain_rule_fst
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    mutualInfo p = mutualInfo (fstThirdMarginal p) + condMutualInfo p := by
  rw [mutualInfo_eq, mutualInfo_eq, condMutualInfo_eq]
  rw [fstMarginal_fstThirdMarginal, sndMarginal_fstThirdMarginal,
    sndMarginal_eq_sndThirdMarginal]
  ring

/--
Second mutual-information chain-rule variant:

`I(A;B,C) = I(A;B) + I(A;C | B)`.
-/
theorem mutualInfo_chain_rule_snd
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    mutualInfo p =
      mutualInfo (fstSndMarginal p) +
        condMutualInfo (p.map fun x => (x.1, x.2.2, x.2.1)) := by
  let q : PMF (alpha × gamma × beta) := p.map fun x => (x.1, x.2.2, x.2.1)
  change mutualInfo p = mutualInfo (fstSndMarginal p) + condMutualInfo q
  have hfst : fstMarginal (fstSndMarginal p) = fstMarginal p := by
    simp [fstMarginal, fstSndMarginal]
  have hthird : thirdMarginal q = sndMarginal (fstSndMarginal p) := by
    simp [q, thirdMarginal, sndMarginal, fstSndMarginal]
  have hfstthird : fstThirdMarginal q = fstSndMarginal p := by
    simp [q, fstThirdMarginal, fstSndMarginal]
  have hsndthird_entropy : entropy (sndThirdMarginal q) = entropy (sndMarginal p) := by
    have hsndthird : sndThirdMarginal q = (sndMarginal p).map Prod.swap := by
      unfold q sndThirdMarginal sndMarginal
      rw [PMF.map_comp, PMF.map_comp]
      rfl
    rw [hsndthird, entropy_map_swap]
  have hq_entropy : entropy q = entropy p := by
    have hswap :
        Function.Injective (fun x : alpha × beta × gamma => (x.1, x.2.2, x.2.1)) := by
      intro x y h
      exact
        Prod.ext
          (congrArg (fun z : alpha × gamma × beta => z.1) h)
          (Prod.ext
            (congrArg (fun z : alpha × gamma × beta => z.2.2) h)
            (congrArg (fun z : alpha × gamma × beta => z.2.1) h))
    exact entropy_map_injective (p := p) hswap
  rw [mutualInfo_eq, mutualInfo_eq, condMutualInfo_eq]
  rw [hfst, hfstthird, hthird, hsndthird_entropy, hq_entropy]
  ring

/--
Random-variable form of `mutualInfo_chain_rule_fst`:

`I(X;Y,Z) = I(X;Z) + I(X;Y | Z)`.
-/
theorem mutualInfoOf_chain_rule_fst
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    mutualInfoOf p X (fun omega => (Y omega, Z omega)) =
      mutualInfoOf p X Z + condMutualInfoOf p X Y Z := by
  simpa [mutualInfoOf, condMutualInfoOf] using
    mutualInfo_chain_rule_fst (p := p.map fun omega => (X omega, Y omega, Z omega))

/--
Random-variable form of `mutualInfo_chain_rule_snd`:

`I(X;Y,Z) = I(X;Y) + I(X;Z | Y)`.
-/
theorem mutualInfoOf_chain_rule_snd
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    mutualInfoOf p X (fun omega => (Y omega, Z omega)) =
      mutualInfoOf p X Y + condMutualInfoOf p X Z Y := by
  have hmap :
      (p.map fun omega => (X omega, Z omega, Y omega)) =
        (p.map fun omega => (X omega, Y omega, Z omega)).map
          (fun x : alpha × beta × gamma => (x.1, x.2.2, x.2.1)) := by
    simpa [Function.comp_def] using
      (PMF.map_comp
        (p := p)
        (f := fun omega => (X omega, Y omega, Z omega))
        (g := fun x : alpha × beta × gamma => (x.1, x.2.2, x.2.1))).symm
  simpa [mutualInfoOf, condMutualInfoOf, hmap] using
    mutualInfo_chain_rule_snd (p := p.map fun omega => (X omega, Y omega, Z omega))

/-! ## Deterministic mutual-information processing -/

private theorem mutualInfoOf_augment_right
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta)
    (f : beta -> gamma) :
    mutualInfoOf p X (fun omega => (f (Y omega), Y omega)) =
      mutualInfoOf p X Y := by
  have hY :
      entropyOf p (fun omega => (f (Y omega), Y omega)) = entropyOf p Y := by
    unfold entropyOf
    have hmap :
        p.map (fun omega => (f (Y omega), Y omega)) =
          (p.map Y).map (fun b => (f b, b)) := by
      simpa [Function.comp_def] using
        (PMF.map_comp (p := p) (f := Y) (g := fun b => (f b, b))).symm
    rw [hmap]
    exact entropy_map_injective (p := p.map Y) fun a b h => congrArg Prod.snd h
  have hXY :
      jointEntropyOf p X (fun omega => (f (Y omega), Y omega)) =
        jointEntropyOf p X Y := by
    unfold jointEntropyOf entropyOf
    have hmap :
        p.map (fun omega => (X omega, (f (Y omega), Y omega))) =
          (p.map fun omega => (X omega, Y omega)).map
            (fun z => (z.1, (f z.2, z.2))) := by
      simpa [Function.comp_def] using
        (PMF.map_comp
          (p := p)
          (f := fun omega => (X omega, Y omega))
          (g := fun z => (z.1, (f z.2, z.2)))).symm
    rw [hmap]
    exact entropy_map_injective (p := p.map fun omega => (X omega, Y omega)) fun a b h =>
      Prod.ext
        (congrArg (fun z : alpha × (gamma × beta) => z.1) h)
        (congrArg (fun z : alpha × (gamma × beta) => z.2.2) h)
  rw [mutualInfoOf_eq, mutualInfoOf_eq, hY, hXY]

/--
Deterministic mutual-information chain rule:
`I(X;Y) = I(f(X);Y) + I(X;Y | f(X))`.
-/
theorem mutualInfoOf_deterministic_chain_rule_left
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta)
    (f : alpha -> gamma) :
    mutualInfoOf p X Y =
      mutualInfoOf p (fun omega => f (X omega)) Y +
        condMutualInfoOf p X Y (fun omega => f (X omega)) := by
  calc
    mutualInfoOf p X Y = mutualInfoOf p Y X :=
      (mutualInfoOf_swap p X Y).symm
    _ = mutualInfoOf p Y (fun omega => (f (X omega), X omega)) :=
      (mutualInfoOf_augment_right p Y X f).symm
    _ = mutualInfoOf p Y (fun omega => f (X omega)) +
          condMutualInfoOf p Y X (fun omega => f (X omega)) :=
      mutualInfoOf_chain_rule_snd p Y (fun omega => f (X omega)) X
    _ = mutualInfoOf p (fun omega => f (X omega)) Y +
          condMutualInfoOf p X Y (fun omega => f (X omega)) := by
      rw [mutualInfoOf_swap, condMutualInfoOf_swap]

/-- Deterministic post-processing of the left variable cannot increase mutual information. -/
theorem mutualInfoOf_comp_left_le
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta)
    (f : alpha -> gamma) :
    mutualInfoOf p (fun omega => f (X omega)) Y <= mutualInfoOf p X Y := by
  rw [mutualInfoOf_deterministic_chain_rule_left p X Y f]
  exact le_add_of_nonneg_right
    (condMutualInfoOf_nonneg p X Y fun omega => f (X omega))

/-- Deterministic post-processing of the right variable cannot increase mutual information. -/
theorem mutualInfoOf_comp_right_le
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta)
    (f : beta -> gamma) :
    mutualInfoOf p X (fun omega => f (Y omega)) <= mutualInfoOf p X Y := by
  calc
    mutualInfoOf p X (fun omega => f (Y omega)) =
        mutualInfoOf p (fun omega => f (Y omega)) X :=
      (mutualInfoOf_swap p X (fun omega => f (Y omega))).symm
    _ <= mutualInfoOf p Y X := mutualInfoOf_comp_left_le p Y X f
    _ = mutualInfoOf p X Y := mutualInfoOf_swap p X Y

/-- Deterministic post-processing of both variables cannot increase mutual information. -/
theorem mutualInfoOf_comp_le
    {omega : Type u} {alpha : Type v} {beta : Type w}
      {gamma : Type x} {delta : Type y}
    [Fintype alpha] [Fintype beta] [Fintype gamma] [Fintype delta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta)
    (f : alpha -> gamma) (g : beta -> delta) :
    mutualInfoOf p (fun omega => f (X omega)) (fun omega => g (Y omega)) <=
      mutualInfoOf p X Y := by
  calc
    mutualInfoOf p (fun omega => f (X omega)) (fun omega => g (Y omega)) <=
        mutualInfoOf p (fun omega => f (X omega)) Y :=
      mutualInfoOf_comp_right_le p (fun omega => f (X omega)) Y g
    _ <= mutualInfoOf p X Y := mutualInfoOf_comp_left_le p X Y f

/-- Mapping the first coordinate of a joint PMF cannot increase mutual information. -/
theorem mutualInfo_map_fst_le
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta)) (f : alpha -> gamma) :
    mutualInfo (p.map fun z => (f z.1, z.2)) <= mutualInfo p := by
  have hid : p.map (fun z : alpha × beta => (z.1, z.2)) = p := by
    calc
      p.map (fun z : alpha × beta => (z.1, z.2)) = p.map id := by
        exact congrArg (fun h => p.map h) (by
          funext z
          exact Prod.eta z)
      _ = p := PMF.map_id p
  simpa only [mutualInfoOf, hid] using
    mutualInfoOf_comp_left_le p Prod.fst Prod.snd f

/-- Mapping the second coordinate of a joint PMF cannot increase mutual information. -/
theorem mutualInfo_map_snd_le
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta)) (f : beta -> gamma) :
    mutualInfo (p.map fun z => (z.1, f z.2)) <= mutualInfo p := by
  have hid : p.map (fun z : alpha × beta => (z.1, z.2)) = p := by
    calc
      p.map (fun z : alpha × beta => (z.1, z.2)) = p.map id := by
        exact congrArg (fun h => p.map h) (by
          funext z
          exact Prod.eta z)
      _ = p := PMF.map_id p
  simpa only [mutualInfoOf, hid] using
    mutualInfoOf_comp_right_le p Prod.fst Prod.snd f

/-- Mapping both coordinates of a joint PMF cannot increase mutual information. -/
theorem mutualInfo_map_prod_le
    {alpha : Type u} {beta : Type v} {gamma : Type w} {delta : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma] [Fintype delta]
    (p : PMF (alpha × beta)) (f : alpha -> gamma) (g : beta -> delta) :
    mutualInfo (p.map fun z => (f z.1, g z.2)) <= mutualInfo p := by
  have hid : p.map (fun z : alpha × beta => (z.1, z.2)) = p := by
    calc
      p.map (fun z : alpha × beta => (z.1, z.2)) = p.map id := by
        exact congrArg (fun h => p.map h) (by
          funext z
          exact Prod.eta z)
      _ = p := PMF.map_id p
  simpa only [mutualInfoOf, hid] using
    mutualInfoOf_comp_le p Prod.fst Prod.snd f g

/-! ## Textbook-Facing Deterministic-Processing Aliases -/

/-- Explicitly two-sided alias for deterministic mutual-information processing. -/
theorem mutualInfoOf_comp_both_le
    {omega : Type u} {alpha : Type v} {beta : Type w}
      {gamma : Type x} {delta : Type y}
    [Fintype alpha] [Fintype beta] [Fintype gamma] [Fintype delta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta)
    (f : alpha -> gamma) (g : beta -> delta) :
    mutualInfoOf p (fun omega => f (X omega)) (fun omega => g (Y omega)) <=
      mutualInfoOf p X Y :=
  mutualInfoOf_comp_le p X Y f g

/-- Left-coordinate alias for deterministic processing of a joint PMF. -/
theorem mutualInfo_map_left_le
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta)) (f : alpha -> gamma) :
    mutualInfo (p.map fun z => (f z.1, z.2)) <= mutualInfo p :=
  mutualInfo_map_fst_le p f

/-- Right-coordinate alias for deterministic processing of a joint PMF. -/
theorem mutualInfo_map_right_le
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta)) (f : beta -> gamma) :
    mutualInfo (p.map fun z => (z.1, f z.2)) <= mutualInfo p :=
  mutualInfo_map_snd_le p f

/-- Both-coordinate alias for deterministic processing of a joint PMF. -/
theorem mutualInfo_map_both_le
    {alpha : Type u} {beta : Type v} {gamma : Type w} {delta : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma] [Fintype delta]
    (p : PMF (alpha × beta)) (f : alpha -> gamma) (g : beta -> delta) :
    mutualInfo (p.map fun z => (f z.1, g z.2)) <= mutualInfo p :=
  mutualInfo_map_prod_le p f g

/-! ## Conditioning reduces entropy -/

/--
Conditional mutual information as a difference of conditional entropies:

`I(A;B | C) = H(A | C) - H(A | B,C)`.
-/
theorem condMutualInfo_eq_condEntropy_fstThirdMarginal_sub_condEntropy
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condMutualInfo p = condEntropy (fstThirdMarginal p) - condEntropy p := by
  rw [condMutualInfo_eq, condEntropy_eq, condEntropy_eq]
  rw [sndMarginal_fstThirdMarginal, sndMarginal_eq_sndThirdMarginal]
  ring

/--
Symmetric conditional-entropy difference form:
`I(A;B | C) = H(B | C) - H(B | A,C)`.
-/
theorem condMutualInfo_eq_condEntropy_sndThirdMarginal_sub_condEntropy_swap12
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condMutualInfo p =
      condEntropy (sndThirdMarginal p) -
        condEntropy (p.map fun z => (z.2.1, z.1, z.2.2)) := by
  rw [condMutualInfo_eq_condEntropy_marginals,
    condEntropy_pairThirdLaw_chain_rule_swap]
  ring

/--
Conditioning reduces entropy:

`H(A | B,C) <= H(A | C)`.

The proof rewrites the difference as `I(A;B | C)` and uses conditional mutual
information nonnegativity.
-/
theorem condEntropy_le_condEntropy_fstThirdMarginal
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condEntropy p <= condEntropy (fstThirdMarginal p) := by
  have hnonneg := condMutualInfo_nonneg p
  rw [condMutualInfo_eq_condEntropy_fstThirdMarginal_sub_condEntropy] at hnonneg
  exact sub_nonneg.mp hnonneg

/--
Random-variable conditioning-reduces-entropy theorem:

`H(X | Y,Z) <= H(X | Z)`.
-/
theorem condEntropyOf_pair_le_condEntropyOf
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    condEntropyOf p X (fun omega => (Y omega, Z omega)) <= condEntropyOf p X Z := by
  simpa [condEntropyOf] using
    condEntropy_le_condEntropy_fstThirdMarginal
      (p := p.map fun omega => (X omega, Y omega, Z omega))

/-! ## Triple-level conditional entropy and mutual-information inequalities -/

/-- Conditional mutual information is at most `H(A|C)`. -/
theorem condMutualInfo_le_condEntropy_fstThirdMarginal
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condMutualInfo p <= condEntropy (fstThirdMarginal p) := by
  calc
    condMutualInfo p = condEntropy (fstThirdMarginal p) - condEntropy p :=
      condMutualInfo_eq_condEntropy_fstThirdMarginal_sub_condEntropy p
    _ <= condEntropy (fstThirdMarginal p) :=
      sub_le_self _ (condEntropy_nonneg p)

/-- Conditional mutual information is at most `H(B|C)`. -/
theorem condMutualInfo_le_condEntropy_sndThirdMarginal
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condMutualInfo p <= condEntropy (sndThirdMarginal p) := by
  calc
    condMutualInfo p =
        condEntropy (sndThirdMarginal p) -
          condEntropy (p.map fun z => (z.2.1, z.1, z.2.2)) :=
      condMutualInfo_eq_condEntropy_sndThirdMarginal_sub_condEntropy_swap12 p
    _ <= condEntropy (sndThirdMarginal p) :=
      sub_le_self _
        (condEntropy_nonneg
          (p.map fun z : alpha × beta × gamma => (z.2.1, z.1, z.2.2)))

/-- `H(A|C)` is at most the conditional joint entropy `H(A,B|C)`. -/
theorem condEntropy_fstThirdMarginal_le_condEntropy_pairThirdLaw
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condEntropy (fstThirdMarginal p) <= condEntropy (pairThirdLaw p) := by
  calc
    condEntropy (fstThirdMarginal p) <=
        condEntropy (fstThirdMarginal p) +
          condEntropy (p.map fun z => (z.2.1, z.1, z.2.2)) :=
      le_add_of_nonneg_right
        (condEntropy_nonneg
          (p.map fun z : alpha × beta × gamma => (z.2.1, z.1, z.2.2)))
    _ = condEntropy (pairThirdLaw p) :=
      (condEntropy_pairThirdLaw_chain_rule_swap p).symm

/-- `H(B|C)` is at most the conditional joint entropy `H(A,B|C)`. -/
theorem condEntropy_sndThirdMarginal_le_condEntropy_pairThirdLaw
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condEntropy (sndThirdMarginal p) <= condEntropy (pairThirdLaw p) := by
  calc
    condEntropy (sndThirdMarginal p) <=
        condEntropy (sndThirdMarginal p) + condEntropy p :=
      le_add_of_nonneg_right (condEntropy_nonneg p)
    _ = condEntropy (pairThirdLaw p) :=
      (condEntropy_pairThirdLaw_chain_rule p).symm

/-- Conditional joint entropy is subadditive: `H(A,B|C) <= H(A|C) + H(B|C)`. -/
theorem condEntropy_pairThirdLaw_le_condEntropy_fstThirdMarginal_add_condEntropy_sndThirdMarginal
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condEntropy (pairThirdLaw p) <=
      condEntropy (fstThirdMarginal p) + condEntropy (sndThirdMarginal p) := by
  have hnonneg := condMutualInfo_nonneg p
  rw [condMutualInfo_eq_condEntropy_marginals] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- Random-variable conditional mutual information is at most `H(X|Z)`. -/
theorem condMutualInfoOf_le_condEntropyOf_left
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    condMutualInfoOf p X Y Z <= condEntropyOf p X Z := by
  calc
    condMutualInfoOf p X Y Z =
        condEntropyOf p X Z -
          condEntropyOf p X (fun omega => (Y omega, Z omega)) :=
      condMutualInfoOf_eq_condEntropyOf_sub_condEntropyOf p X Y Z
    _ <= condEntropyOf p X Z :=
      sub_le_self _
        (condEntropyOf_nonneg p X fun omega => (Y omega, Z omega))

/-- Random-variable conditional mutual information is at most `H(Y|Z)`. -/
theorem condMutualInfoOf_le_condEntropyOf_right
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    condMutualInfoOf p X Y Z <= condEntropyOf p Y Z := by
  calc
    condMutualInfoOf p X Y Z =
        condEntropyOf p Y Z -
          condEntropyOf p Y (fun omega => (X omega, Z omega)) :=
      condMutualInfoOf_eq_condEntropyOf_sub_condEntropyOf_swap p X Y Z
    _ <= condEntropyOf p Y Z :=
      sub_le_self _
        (condEntropyOf_nonneg p Y fun omega => (X omega, Z omega))

/-- `H(X|Z)` is at most the conditional joint entropy `H(X,Y|Z)`. -/
theorem condEntropyOf_le_condEntropyOf_pair
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    condEntropyOf p X Z <=
      condEntropyOf p (fun omega => (X omega, Y omega)) Z := by
  calc
    condEntropyOf p X Z <=
        condEntropyOf p X Z +
          condEntropyOf p Y (fun omega => (X omega, Z omega)) :=
      le_add_of_nonneg_right
        (condEntropyOf_nonneg p Y fun omega => (X omega, Z omega))
    _ = condEntropyOf p (fun omega => (X omega, Y omega)) Z :=
      (condEntropyOf_pair_chain_rule_swap p X Y Z).symm

/-- `H(Y|Z)` is at most the conditional joint entropy `H(X,Y|Z)`. -/
theorem condEntropyOf_le_condEntropyOf_pair_swap
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    condEntropyOf p Y Z <=
      condEntropyOf p (fun omega => (X omega, Y omega)) Z := by
  calc
    condEntropyOf p Y Z <=
        condEntropyOf p Y Z +
          condEntropyOf p X (fun omega => (Y omega, Z omega)) :=
      le_add_of_nonneg_right
        (condEntropyOf_nonneg p X fun omega => (Y omega, Z omega))
    _ = condEntropyOf p (fun omega => (X omega, Y omega)) Z :=
      (condEntropyOf_pair_chain_rule p X Y Z).symm

/-- Random-variable conditional joint entropy is subadditive. -/
theorem condEntropyOf_pair_le_condEntropyOf_add_condEntropyOf
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    condEntropyOf p (fun omega => (X omega, Y omega)) Z <=
      condEntropyOf p X Z + condEntropyOf p Y Z := by
  have hnonneg := condMutualInfoOf_nonneg p X Y Z
  rw [condMutualInfoOf_eq_condEntropyOf_add_condEntropyOf_sub_condEntropyOf_pair]
    at hnonneg
  exact sub_nonneg.mp hnonneg

/-! ## Textbook-Facing Conditional-Inequality Aliases -/

/-- Textbook-facing PMF alias for `I(A;B|C) <= H(A|C)`. -/
theorem condMutualInfo_le_condEntropy_left
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condMutualInfo p <= condEntropy (fstThirdMarginal p) :=
  condMutualInfo_le_condEntropy_fstThirdMarginal p

/-- Textbook-facing PMF alias for `I(A;B|C) <= H(B|C)`. -/
theorem condMutualInfo_le_condEntropy_right
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condMutualInfo p <= condEntropy (sndThirdMarginal p) :=
  condMutualInfo_le_condEntropy_sndThirdMarginal p

/-- Left-oriented PMF alias for `H(A|C) <= H(A,B|C)`. -/
theorem condEntropy_left_le_condEntropy_pair
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condEntropy (fstThirdMarginal p) <= condEntropy (pairThirdLaw p) :=
  condEntropy_fstThirdMarginal_le_condEntropy_pairThirdLaw p

/-- Right-oriented PMF alias for `H(B|C) <= H(A,B|C)`. -/
theorem condEntropy_right_le_condEntropy_pair
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condEntropy (sndThirdMarginal p) <= condEntropy (pairThirdLaw p) :=
  condEntropy_sndThirdMarginal_le_condEntropy_pairThirdLaw p

/-- Short PMF alias for conditional joint-entropy subadditivity. -/
theorem condEntropy_pair_le_add_condEntropy
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condEntropy (pairThirdLaw p) <=
      condEntropy (fstThirdMarginal p) + condEntropy (sndThirdMarginal p) :=
  condEntropy_pairThirdLaw_le_condEntropy_fstThirdMarginal_add_condEntropy_sndThirdMarginal
    p

/-- Left-oriented random-variable alias for `H(X|Z) <= H(X,Y|Z)`. -/
theorem condEntropyOf_left_le_condEntropyOf_pair
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    condEntropyOf p X Z <=
      condEntropyOf p (fun omega => (X omega, Y omega)) Z :=
  condEntropyOf_le_condEntropyOf_pair p X Y Z

/-- Right-oriented random-variable alias for `H(Y|Z) <= H(X,Y|Z)`. -/
theorem condEntropyOf_right_le_condEntropyOf_pair
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    condEntropyOf p Y Z <=
      condEntropyOf p (fun omega => (X omega, Y omega)) Z :=
  condEntropyOf_le_condEntropyOf_pair_swap p X Y Z

/-- Short random-variable alias for conditional joint-entropy subadditivity. -/
theorem condEntropyOf_pair_le_add_condEntropyOf
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    condEntropyOf p (fun omega => (X omega, Y omega)) Z <=
      condEntropyOf p X Z + condEntropyOf p Y Z :=
  condEntropyOf_pair_le_condEntropyOf_add_condEntropyOf p X Y Z

end

end Shannon
end LeanInfoTheory
