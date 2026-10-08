/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.SemanticBridge.Theorems
import Tengoku

/-!
# Independence for finite Shannon information measures

This file introduces PMF-first independence predicates for the finite Shannon
API. A joint law is independent when it equals the independent product of its
marginals; random-variable independence applies that predicate to the mapped
joint law. Deterministic processing of either variable preserves independence,
with the right-processing theorem and existing symmetry covering both sides.
The file characterizes zero finite mutual information by these
predicates, closes the pair-level entropy equality cases governed by
independence, and develops conditional independence through a proof-independent
cross-product definition, its positive-fiber characterization, and the
equivalence between conditional independence and zero conditional mutual
information, together with the resulting conditional-entropy equality cases.

The definitions themselves do not choose measurable-space structures. The
bridge to mathlib's measure-theoretic independence predicate also lives in this
separately importable semantic layer and states its measurability assumptions
explicitly.
-/

namespace LeanInfoTheory
namespace Shannon

noncomputable section

universe u v w x

/-- A joint PMF is independent when it is the product of its marginals. -/
def IsIndependent {alpha : Type u} {beta : Type v}
    (p : PMF (alpha × beta)) : Prop :=
  p = indepProd (fstMarginal p) (sndMarginal p)

/-- Two random variables are independent when their joint law is independent. -/
def IsIndependentOf {omega : Type u} {alpha : Type v} {beta : Type w}
    (p : PMF omega) (X : omega → alpha) (Y : omega → beta) : Prop :=
  IsIndependent (p.map fun omega => (X omega, Y omega))

/--
The first two coordinates of a triple PMF are conditionally independent given
the third when every atom satisfies the cross-product factorization

`p(a,b,c) * p_C(c) = p_AC(a,c) * p_BC(b,c)`.

This definition is meaningful on null fibers and does not require choosing a
conditional PMF from a proof that `p_C(c) ≠ 0`.
-/
def IsCondIndependent {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta × gamma)) : Prop :=
  ∀ a b c,
    p (a, b, c) * thirdMarginal p c =
      fstThirdMarginal p (a, c) * sndThirdMarginal p (b, c)

/--
Two random variables are conditionally independent given a third when their
mapped triple law is conditionally independent.
-/
def IsCondIndependentOf
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    (p : PMF omega) (X : omega → alpha) (Y : omega → beta)
    (Z : omega → gamma) : Prop :=
  IsCondIndependent (p.map fun omega => (X omega, Y omega, Z omega))

/-- Swapping the first two coordinates of a triple law preserves conditional independence. -/
@[simp]
theorem isCondIndependent_map_swap12
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta × gamma)) :
    IsCondIndependent (p.map fun x => (x.2.1, x.1, x.2.2)) ↔
      IsCondIndependent p := by
  let swap12 : alpha × beta × gamma → beta × alpha × gamma :=
    fun x => (x.2.1, x.1, x.2.2)
  have hswap12 : Function.Injective swap12 := by
    intro x y hxy
    apply Prod.ext
    · exact congrArg (fun z => z.2.1) hxy
    · apply Prod.ext
      · exact congrArg (fun z => z.1) hxy
      · exact congrArg (fun z => z.2.2) hxy
  have hmass (a : alpha) (b : beta) (c : gamma) :
      (p.map swap12) (b, a, c) = p (a, b, c) := by
    simpa [swap12] using
      PMF.map_apply_of_injective p hswap12 (a, b, c)
  have hfst :
      fstThirdMarginal (p.map swap12) = sndThirdMarginal p := by
    change fstThirdMarginal (p.map fun x => (x.2.1, x.1, x.2.2)) =
      sndThirdMarginal p
    exact fstThirdMarginal_map_swap12 p
  have hsnd :
      sndThirdMarginal (p.map swap12) = fstThirdMarginal p := by
    change sndThirdMarginal (p.map fun x => (x.2.1, x.1, x.2.2)) =
      fstThirdMarginal p
    exact sndThirdMarginal_map_swap12 p
  have hthird :
      thirdMarginal (p.map swap12) = thirdMarginal p := by
    change thirdMarginal (p.map fun x => (x.2.1, x.1, x.2.2)) =
      thirdMarginal p
    exact thirdMarginal_map_swap12 p
  change IsCondIndependent (p.map swap12) ↔ IsCondIndependent p
  unfold IsCondIndependent
  constructor
  · intro hp a b c
    have h := hp b a c
    rw [hmass a b c, hthird, hfst, hsnd] at h
    simpa [mul_comm] using h
  · intro hp b a c
    have h := hp a b c
    rw [hmass a b c, hthird, hfst, hsnd]
    simpa [mul_comm] using h

/-- Conditional independence of random variables is symmetric in its first two variables. -/
theorem isCondIndependentOf_swap
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    (p : PMF omega) (X : omega → alpha) (Y : omega → beta)
    (Z : omega → gamma) :
    IsCondIndependentOf p Y X Z ↔ IsCondIndependentOf p X Y Z := by
  have hmap :
      p.map (fun omega => (Y omega, X omega, Z omega)) =
        (p.map fun omega => (X omega, Y omega, Z omega)).map
          (fun x => (x.2.1, x.1, x.2.2)) := by
    rw [PMF.map_comp]
    rfl
  unfold IsCondIndependentOf
  rw [hmap, isCondIndependent_map_swap12]

/-- Independence is equivalent to pointwise factorization into marginal masses. -/
theorem isIndependent_iff_apply_eq_mul_marginals
    {alpha : Type u} {beta : Type v} (p : PMF (alpha × beta)) :
    IsIndependent p ↔
      ∀ a b, p (a, b) = fstMarginal p a * sndMarginal p b := by
  constructor
  · intro hp a b
    rw [IsIndependent] at hp
    calc
      p (a, b) = indepProd (fstMarginal p) (sndMarginal p) (a, b) :=
        congrArg (fun q : PMF (alpha × beta) => q (a, b)) hp
      _ = fstMarginal p a * sndMarginal p b := indepProd_apply _ _ _ _
  · intro hp
    rw [IsIndependent]
    apply PMF.ext
    rintro ⟨a, b⟩
    simpa using hp a b

/-- The independent product of two PMFs is independent. -/
@[simp]
theorem isIndependent_indepProd {alpha : Type u} {beta : Type v}
    (p : PMF alpha) (q : PMF beta) :
    IsIndependent (indepProd p q) := by
  simp [IsIndependent]

/-- Swapping the coordinates of a joint law preserves independence. -/
@[simp]
theorem isIndependent_map_swap {alpha : Type u} {beta : Type v}
    (p : PMF (alpha × beta)) :
    IsIndependent (p.map Prod.swap) ↔ IsIndependent p := by
  constructor
  · intro hp
    rw [IsIndependent] at hp ⊢
    have hp' := congrArg
      (fun q : PMF (beta × alpha) => q.map (Prod.swap : beta × alpha → alpha × beta)) hp
    have hswap :
        (p.map (Prod.swap : alpha × beta → beta × alpha)).map
            (Prod.swap : beta × alpha → alpha × beta) = p := by
      rw [PMF.map_comp]
      have hfun :
          (Prod.swap : beta × alpha → alpha × beta) ∘
              (Prod.swap : alpha × beta → beta × alpha) = id := by
        funext x
        rcases x with ⟨a, b⟩
        rfl
      rw [hfun, PMF.map_id]
    rw [hswap, indepProd_map_swap, fstMarginal_map_swap,
      sndMarginal_map_swap] at hp'
    exact hp'
  · intro hp
    rw [IsIndependent] at hp ⊢
    calc
      p.map Prod.swap =
          (indepProd (fstMarginal p) (sndMarginal p)).map Prod.swap :=
        congrArg (fun q : PMF (alpha × beta) => q.map Prod.swap) hp
      _ = indepProd (sndMarginal p) (fstMarginal p) :=
        indepProd_map_swap _ _
      _ = indepProd (fstMarginal (p.map Prod.swap))
          (sndMarginal (p.map Prod.swap)) := by
        rw [fstMarginal_map_swap, sndMarginal_map_swap]

/--
Random-variable independence is equality of the joint law with the independent
product of the two individual laws.
-/
theorem isIndependentOf_iff_map_eq_indepProd
    {omega : Type u} {alpha : Type v} {beta : Type w}
    (p : PMF omega) (X : omega → alpha) (Y : omega → beta) :
    IsIndependentOf p X Y ↔
      p.map (fun omega => (X omega, Y omega)) =
        indepProd (p.map X) (p.map Y) := by
  simp [IsIndependentOf, IsIndependent]

/--
Deterministic processing of the right variable preserves independence.

The source and observed types are arbitrary: the PMF mapped-law proof needs no
finiteness, measurable-space, or injectivity assumptions on the processing map.
-/
theorem isIndependentOf_comp_right
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    (p : PMF omega) (X : omega → alpha) (Y : omega → beta)
    (f : beta → gamma) (hXY : IsIndependentOf p X Y) :
    IsIndependentOf p X (fun omega => f (Y omega)) := by
  rw [isIndependentOf_iff_map_eq_indepProd] at hXY ⊢
  simpa only [indepProd, PMF.map_bind, PMF.map_comp, Function.comp_def] using
    congrArg
      (fun q : PMF (alpha × beta) => q.map (fun z => (z.1, f z.2)))
      hXY

/--
The PMF mapped-law definition of random-variable independence agrees with
mathlib's measure-theoretic `ProbabilityTheory.IndepFun` predicate.

Measurability and measurable-singleton assumptions are explicit here because
they belong to the semantic bridge, not to the PMF-first definition
`IsIndependentOf`.
-/
theorem isIndependentOf_iff_indepFun
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [MeasurableSpace omega] [MeasurableSpace alpha] [MeasurableSpace beta]
    [MeasurableSingletonClass alpha] [MeasurableSingletonClass beta]
    (p : PMF omega) (X : omega → alpha) (Y : omega → beta)
    (hX : Measurable X) (hY : Measurable Y) :
    IsIndependentOf p X Y ↔
      ProbabilityTheory.IndepFun X Y p.toMeasure := by
  rw [isIndependentOf_iff_map_eq_indepProd]
  rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    hX.aemeasurable hY.aemeasurable]
  rw [PMF.toMeasure_map (fun omega => (X omega, Y omega)) p (hX.prodMk hY),
    PMF.toMeasure_map X p hX, PMF.toMeasure_map Y p hY,
    ← indepProd_toMeasure]
  exact PMF.toMeasure_inj.symm

/-- Independence of random variables is symmetric. -/
theorem isIndependentOf_swap
    {omega : Type u} {alpha : Type v} {beta : Type w}
    (p : PMF omega) (X : omega → alpha) (Y : omega → beta) :
    IsIndependentOf p Y X ↔ IsIndependentOf p X Y := by
  have hmap :
      p.map (fun omega => (Y omega, X omega)) =
        (p.map fun omega => (X omega, Y omega)).map Prod.swap := by
    rw [PMF.map_comp]
    rfl
  unfold IsIndependentOf
  rw [hmap, isIndependent_map_swap]

/-! ## Mutual information equality -/

/--
Finite mutual information is zero exactly when the joint PMF is independent.

The proof chooses the discrete measurable structure only locally, uses the KL
representation of mutual information, and discharges the necessary real-KL
finiteness guard through support inclusion.
-/
theorem mutualInfo_eq_zero_iff_isIndependent
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] (p : PMF (alpha × beta)) :
    mutualInfo p = 0 ↔ IsIndependent p := by
  let : MeasurableSpace (alpha × beta) := ⊤
  have : MeasurableSingletonClass (alpha × beta) := ⟨fun _ => trivial⟩
  have hsupport :
      p.support ⊆
        (indepProd (fstMarginal p) (sndMarginal p)).support :=
    (toMeasure_absolutelyContinuous_iff_support_subset p
      (indepProd (fstMarginal p) (sndMarginal p))).1
      (joint_toMeasure_absolutelyContinuous_indepProd_marginals (p := p))
  rw [mutualInfo_eq_toReal_klDiv_joint_indepProd,
    toReal_klDiv_pmf_eq_zero_iff p
      (indepProd (fstMarginal p) (sndMarginal p)) hsupport,
    IsIndependent]

/--
Finite-valued random variables have zero mutual information exactly when their
mapped joint law is independent.
-/
theorem mutualInfoOf_eq_zero_iff_isIndependentOf
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega → alpha) (Y : omega → beta) :
    mutualInfoOf p X Y = 0 ↔ IsIndependentOf p X Y := by
  simpa [mutualInfoOf, IsIndependentOf] using
    mutualInfo_eq_zero_iff_isIndependent
      (p.map fun omega => (X omega, Y omega))

/-! ## Pair entropy equality cases -/

/--
Conditioning preserves the entropy of the left coordinate exactly when the two
coordinates are independent.
-/
theorem condEntropy_eq_entropy_left_iff_isIndependent
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] (p : PMF (alpha × beta)) :
    condEntropy p = entropy (fstMarginal p) ↔ IsIndependent p := by
  rw [← mutualInfo_eq_zero_iff_isIndependent]
  constructor
  · intro h
    rw [mutualInfo_eq_entropy_fstMarginal_sub_condEntropy, h, sub_self]
  · intro h
    rw [mutualInfo_eq_entropy_fstMarginal_sub_condEntropy] at h
    linarith

/--
Conditioning preserves `H(X)` exactly when the finite-valued random variables
`X` and `Y` are independent.
-/
theorem condEntropyOf_eq_entropyOf_iff_isIndependentOf
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega → alpha) (Y : omega → beta) :
    condEntropyOf p X Y = entropyOf p X ↔ IsIndependentOf p X Y := by
  simpa [condEntropyOf, entropyOf, IsIndependentOf] using
    condEntropy_eq_entropy_left_iff_isIndependent
      (p.map fun omega => (X omega, Y omega))

/-- Joint entropy is additive exactly when the two coordinates are independent. -/
theorem jointEntropy_eq_add_marginalEntropy_iff_isIndependent
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] (p : PMF (alpha × beta)) :
    entropy p = entropy (fstMarginal p) + entropy (sndMarginal p) ↔
      IsIndependent p := by
  rw [← mutualInfo_eq_zero_iff_isIndependent]
  constructor
  · intro h
    rw [mutualInfo_eq, h, sub_self]
  · intro h
    rw [mutualInfo_eq] at h
    linarith

/--
Joint entropy is additive exactly when the finite-valued random variables are
independent.
-/
theorem jointEntropyOf_eq_add_entropyOf_iff_isIndependentOf
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega → alpha) (Y : omega → beta) :
    jointEntropyOf p X Y = entropyOf p X + entropyOf p Y ↔
      IsIndependentOf p X Y := by
  simpa [jointEntropyOf, entropyOf, IsIndependentOf] using
    jointEntropy_eq_add_marginalEntropy_iff_isIndependent
      (p.map fun omega => (X omega, Y omega))

/-! ## Textbook-facing pair equality aliases -/

/-- Short PMF alias for additivity of joint entropy under independence. -/
theorem jointEntropy_additive_iff_isIndependent
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] (p : PMF (alpha × beta)) :
    entropy p = entropy (fstMarginal p) + entropy (sndMarginal p) ↔
      IsIndependent p :=
  jointEntropy_eq_add_marginalEntropy_iff_isIndependent p

/-- Short random-variable alias for additivity of joint entropy under independence. -/
theorem jointEntropyOf_additive_iff_isIndependentOf
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    jointEntropyOf p X Y = entropyOf p X + entropyOf p Y ↔
      IsIndependentOf p X Y :=
  jointEntropyOf_eq_add_entropyOf_iff_isIndependentOf p X Y

/-! ## Conditional mutual information fibers -/

/--
Finite conditional mutual information is zero exactly when every positive-mass
conditional fiber has zero mutual information.

The forward direction uses nonnegativity to extract zero from each term in the
averaged conditional-mutual-information formula. The marginal guard lets us
cancel the positive real fiber weight. In the reverse direction, null fibers
have zero weight and every positive-mass fiber is zero by hypothesis.
-/
theorem condMutualInfo_eq_zero_iff_condMutualInfoFstSndGivenThird_eq_zero
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condMutualInfo p = 0 ↔
      ∀ c, thirdMarginal p c ≠ 0 →
        condMutualInfoFstSndGivenThird p c = 0 := by
  rw [condMutualInfo_eq_sum_thirdMarginal_mul_condMutualInfoFstSndGivenThird]
  constructor
  · intro hzero c hc
    have hnonneg :
        ∀ c : gamma, c ∈ (Finset.univ : Finset gamma) →
          0 ≤ (thirdMarginal p c).toReal *
            condMutualInfoFstSndGivenThird p c := by
      intro c _hc
      exact mul_nonneg (PMF.toReal_nonneg (thirdMarginal p) c)
        (condMutualInfoFstSndGivenThird_nonneg p c)
    have hproduct_zero :
        (thirdMarginal p c).toReal *
          condMutualInfoFstSndGivenThird p c = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hzero c
        (Finset.mem_univ c)
    have hweight_ne : (thirdMarginal p c).toReal ≠ 0 :=
      ne_of_gt (ENNReal.toReal_pos hc ((thirdMarginal p).apply_ne_top c))
    exact (mul_eq_zero.1 hproduct_zero).resolve_left hweight_ne
  · intro hfiber
    apply Finset.sum_eq_zero
    intro c _hc
    by_cases hc : thirdMarginal p c = 0
    · simp [hc]
    · simp [hfiber c hc]

/-! ## Conditional independence -/

/--
The cross-product definition of conditional independence is equivalent to
ordinary independence of the conditional joint law on every positive-mass
fiber.

No condition is needed on null fibers: the cross-product identity holds there
because the corresponding first-third marginal has zero mass. The right-hand
side is independent of the particular proof of nonzero marginal mass.
-/
theorem isCondIndependent_iff_isIndependent_condFstSndGivenThird
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta × gamma)) :
    IsCondIndependent p ↔
      ∀ c (hc : thirdMarginal p c ≠ 0),
        IsIndependent (condFstSndGivenThird p c hc) := by
  have hleft (c : gamma) (hc : thirdMarginal p c ≠ 0) (a : alpha) :
      thirdMarginal p c *
          fstMarginal (condFstSndGivenThird p c hc) a =
        fstThirdMarginal p (a, c) := by
    have hfst : sndMarginal (fstThirdMarginal p) c ≠ 0 := by
      simpa using hc
    rw [fstMarginal_condFstSndGivenThird]
    simpa using
      (sndMarginal_mul_condFstGivenSnd (fstThirdMarginal p) c hfst a)
  have hright (c : gamma) (hc : thirdMarginal p c ≠ 0) (b : beta) :
      thirdMarginal p c *
          sndMarginal (condFstSndGivenThird p c hc) b =
        sndThirdMarginal p (b, c) := by
    have hsnd : sndMarginal (sndThirdMarginal p) c ≠ 0 := by
      simpa using hc
    rw [sndMarginal_condFstSndGivenThird]
    simpa using
      (sndMarginal_mul_condFstGivenSnd (sndThirdMarginal p) c hsnd b)
  constructor
  · intro hp c hc
    rw [isIndependent_iff_apply_eq_mul_marginals]
    intro a b
    have htop : thirdMarginal p c ≠ ⊤ := (thirdMarginal p).apply_ne_top c
    have hjoint :
        thirdMarginal p c * condFstSndGivenThird p c hc (a, b) =
          p (a, b, c) :=
      thirdMarginal_mul_condFstSndGivenThird p c hc a b
    apply (ENNReal.mul_right_inj hc htop).mp
    calc
      thirdMarginal p c * condFstSndGivenThird p c hc (a, b) =
          p (a, b, c) := hjoint
      _ = thirdMarginal p c *
          (fstMarginal (condFstSndGivenThird p c hc) a *
            sndMarginal (condFstSndGivenThird p c hc) b) := by
        apply (ENNReal.mul_right_inj hc htop).mp
        calc
          thirdMarginal p c * p (a, b, c) =
              p (a, b, c) * thirdMarginal p c := mul_comm _ _
          _ = fstThirdMarginal p (a, c) * sndThirdMarginal p (b, c) :=
            hp a b c
          _ =
              (thirdMarginal p c *
                  fstMarginal (condFstSndGivenThird p c hc) a) *
                (thirdMarginal p c *
                  sndMarginal (condFstSndGivenThird p c hc) b) := by
            rw [hleft c hc a, hright c hc b]
          _ = thirdMarginal p c *
              (thirdMarginal p c *
                (fstMarginal (condFstSndGivenThird p c hc) a *
                  sndMarginal (condFstSndGivenThird p c hc) b)) := by
            ac_rfl
  · intro hfiber a b c
    by_cases hc : thirdMarginal p c = 0
    · have hfstzero : fstThirdMarginal p (a, c) = 0 :=
        apply_eq_zero_of_sndMarginal_eq_zero (fstThirdMarginal p) a (by
          simpa using hc)
      simp [hc, hfstzero]
    · have hindependent :=
        (isIndependent_iff_apply_eq_mul_marginals
          (condFstSndGivenThird p c hc)).1 (hfiber c hc) a b
      have hjoint :
          thirdMarginal p c * condFstSndGivenThird p c hc (a, b) =
            p (a, b, c) :=
        thirdMarginal_mul_condFstSndGivenThird p c hc a b
      calc
        p (a, b, c) * thirdMarginal p c =
            (thirdMarginal p c *
                condFstSndGivenThird p c hc (a, b)) *
              thirdMarginal p c := by rw [hjoint]
        _ = (thirdMarginal p c *
              (fstMarginal (condFstSndGivenThird p c hc) a *
                sndMarginal (condFstSndGivenThird p c hc) b)) *
            thirdMarginal p c := by rw [hindependent]
        _ =
            (thirdMarginal p c *
                fstMarginal (condFstSndGivenThird p c hc) a) *
              (thirdMarginal p c *
                sndMarginal (condFstSndGivenThird p c hc) b) := by
          ac_rfl
        _ = fstThirdMarginal p (a, c) * sndThirdMarginal p (b, c) := by
          rw [hleft c hc a, hright c hc b]

/-! ## Conditional mutual information equality -/

/--
Finite conditional mutual information is zero exactly when the first two
coordinates are conditionally independent given the third.

No conditional law needs to be chosen on null fibers. `IsCondIndependent`
uses the cross-product identity on the original PMF, where those fibers satisfy
the identity directly; conditional PMFs appear only for positive-mass fibers
inside the proof.
-/
theorem condMutualInfo_eq_zero_iff_isCondIndependent
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condMutualInfo p = 0 ↔ IsCondIndependent p := by
  rw [condMutualInfo_eq_zero_iff_condMutualInfoFstSndGivenThird_eq_zero,
    isCondIndependent_iff_isIndependent_condFstSndGivenThird]
  constructor
  · intro hfiber c hc
    apply (mutualInfo_eq_zero_iff_isIndependent
      (condFstSndGivenThird p c hc)).1
    simpa only [condMutualInfoFstSndGivenThird_of_thirdMarginal_ne_zero p hc] using
      hfiber c hc
  · intro hfiber c hc
    rw [condMutualInfoFstSndGivenThird_of_thirdMarginal_ne_zero p hc]
    exact (mutualInfo_eq_zero_iff_isIndependent
      (condFstSndGivenThird p c hc)).2 (hfiber c hc)

/--
Finite-valued random variables have zero conditional mutual information exactly
when they are conditionally independent under their mapped triple law.
-/
theorem condMutualInfoOf_eq_zero_iff_isCondIndependentOf
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega → alpha) (Y : omega → beta)
    (Z : omega → gamma) :
    condMutualInfoOf p X Y Z = 0 ↔ IsCondIndependentOf p X Y Z := by
  simpa [condMutualInfoOf, IsCondIndependentOf] using
    condMutualInfo_eq_zero_iff_isCondIndependent
      (p.map fun omega => (X omega, Y omega, Z omega))

/-! ## Conditional entropy equality cases -/

/--
Conditioning the first coordinate on the second preserves its entropy given the
third coordinate exactly under conditional independence.
-/
theorem condEntropy_eq_condEntropy_fstThirdMarginal_iff_isCondIndependent
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condEntropy p = condEntropy (fstThirdMarginal p) ↔
      IsCondIndependent p := by
  rw [← condMutualInfo_eq_zero_iff_isCondIndependent]
  constructor
  · intro h
    rw [condMutualInfo_eq_condEntropy_fstThirdMarginal_sub_condEntropy,
      h, sub_self]
  · intro h
    rw [condMutualInfo_eq_condEntropy_fstThirdMarginal_sub_condEntropy] at h
    linarith

/--
Conditioning `X` on `Y` preserves its entropy given `Z` exactly when `X` and
`Y` are conditionally independent given `Z`.
-/
theorem condEntropyOf_eq_condEntropyOf_iff_isCondIndependentOf
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega → alpha) (Y : omega → beta)
    (Z : omega → gamma) :
    condEntropyOf p X (fun omega => (Y omega, Z omega)) =
        condEntropyOf p X Z ↔
      IsCondIndependentOf p X Y Z := by
  rw [← condMutualInfoOf_eq_zero_iff_isCondIndependentOf]
  constructor
  · intro h
    rw [condMutualInfoOf_eq_condEntropyOf_sub_condEntropyOf, h, sub_self]
  · intro h
    rw [condMutualInfoOf_eq_condEntropyOf_sub_condEntropyOf] at h
    linarith

/--
Conditional joint entropy is additive exactly when the first two coordinates
are conditionally independent given the third.
-/
theorem condEntropy_pair_eq_add_condEntropy_iff_isCondIndependent
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condEntropy (pairThirdLaw p) =
        condEntropy (fstThirdMarginal p) + condEntropy (sndThirdMarginal p) ↔
      IsCondIndependent p := by
  rw [← condMutualInfo_eq_zero_iff_isCondIndependent]
  constructor
  · intro h
    rw [condMutualInfo_eq_condEntropy_marginals, h, sub_self]
  · intro h
    rw [condMutualInfo_eq_condEntropy_marginals] at h
    linarith

/--
Conditional joint entropy of finite-valued random variables is additive exactly
under conditional independence.
-/
theorem condEntropyOf_pair_eq_add_condEntropyOf_iff_isCondIndependentOf
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega → alpha) (Y : omega → beta)
    (Z : omega → gamma) :
    condEntropyOf p (fun omega => (X omega, Y omega)) Z =
        condEntropyOf p X Z + condEntropyOf p Y Z ↔
      IsCondIndependentOf p X Y Z := by
  rw [← condMutualInfoOf_eq_zero_iff_isCondIndependentOf]
  constructor
  · intro h
    rw [condMutualInfoOf_eq_condEntropyOf_add_condEntropyOf_sub_condEntropyOf_pair,
      h, sub_self]
  · intro h
    rw [condMutualInfoOf_eq_condEntropyOf_add_condEntropyOf_sub_condEntropyOf_pair] at h
    linarith

/-! ## Textbook-facing conditional equality aliases -/

/-- Short PMF alias for conditional joint-entropy additivity. -/
theorem condEntropy_pair_additive_iff_isCondIndependent
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condEntropy (pairThirdLaw p) =
        condEntropy (fstThirdMarginal p) + condEntropy (sndThirdMarginal p) ↔
      IsCondIndependent p :=
  condEntropy_pair_eq_add_condEntropy_iff_isCondIndependent p

/-- Short random-variable alias for conditional joint-entropy additivity. -/
theorem condEntropyOf_pair_additive_iff_isCondIndependentOf
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta)
    (Z : omega -> gamma) :
    condEntropyOf p (fun omega => (X omega, Y omega)) Z =
        condEntropyOf p X Z + condEntropyOf p Y Z ↔
      IsCondIndependentOf p X Y Z :=
  condEntropyOf_pair_eq_add_condEntropyOf_iff_isCondIndependentOf p X Y Z

end

end Shannon
end LeanInfoTheory
