/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.SemanticBridge.Markov

/-!
# Finite sufficient statistics

This module introduces the lightweight core for finite sufficient statistics.
A statistic `T(X)` is sufficient for a parameter `Theta` under a source law
`p` when the reverse chain `Theta -> T(X) -> X` is Markov. The associated
triple law records `(Theta, T(X), X)` in exactly that order for recovery and
channel factorization. At family level, one recovery channel must reconstruct
the complete output-input joint law for every model parameter. That common
recovery yields reverse Markov structure and exact information preservation
under every parameter prior. Conversely, one full-support prior suffices to
recover the common family channel, yielding the standard all-priors
characterization on finite nonempty parameter alphabets. For deterministic
statistics, finite Fisher-Neyman factorization is equivalent to this common-
recovery notion.

The definitions require no finite-alphabet or measurable-space assumptions.
Their elementary characterizations belong in this module as they are
developed. Kernel and KL equality results remain in the downstream
`Shannon.SemanticBridge.Sufficiency.KL` layer.
-/

namespace LeanInfoTheory
namespace Shannon

noncomputable section

/--
The induced law of `(Theta, T(X), X)`. The
`(parameter, statistic, observation)` coordinate order is intentional: it puts
the statistic beside the parameter before the observation is reconstructed by
a channel from statistic values, matching the recovery and channel
factorization statements below.
-/
def statisticTripleLawOf
    {omega : Type u} {theta : Type v} {alpha : Type w} {beta : Type x}
    (p : PMF omega) (Theta : omega → theta) (X : omega → alpha)
    (T : alpha → beta) : PMF (theta × beta × alpha) :=
  p.map fun omega => (Theta omega, T (X omega), X omega)

/--
Under the fixed source law `p`, `T` is sufficient for `Theta` based on `X` when
the reverse chain `Theta -> T(X) -> X` is Markov; equivalently, `Theta` and `X`
are conditionally independent given `T(X)`. This is a fixed-law (or fixed-prior)
predicate. The family-level `IsSufficientStatistic` below instead asks for one
recovery channel that works for every model parameter, independently of a
chosen prior.
-/
def IsSufficientStatisticOf
    {omega : Type u} {theta : Type v} {alpha : Type w} {beta : Type x}
    (p : PMF omega) (Theta : omega → theta) (X : omega → alpha)
    (T : alpha → beta) : Prop :=
  IsMarkovChainOf p Theta (fun omega => T (X omega)) X

/-! ## Fixed-prior characterizations

The following theorem band presents four equivalent views of sufficiency under
one fixed source law: the reverse Markov chain
`Theta -> T(X) -> X`, zero conditional mutual information
`I(Theta;X | T(X)) = 0`, preservation of mutual information
`I(Theta;T(X)) = I(Theta;X)`, and preservation of parameter uncertainty
`H(Theta | X) = H(Theta | T(X))`. The Markov view is assumption-free; the
information-measure views use the finite value types required by the existing
finite Shannon API.
-/

/-- Fixed-prior sufficiency is exactly the reverse Markov condition. -/
theorem isSufficientStatisticOf_iff_isMarkovChainOf
    {omega : Type u} {theta : Type v} {alpha : Type w} {beta : Type x}
    (p : PMF omega) (Theta : omega → theta) (X : omega → alpha)
    (T : alpha → beta) :
    IsSufficientStatisticOf p Theta X T ↔
      IsMarkovChainOf p Theta (fun omega => T (X omega)) X :=
  Iff.rfl

/--
A finite-valued statistic is sufficient exactly when the parameter and the
observation have zero conditional mutual information given the statistic.
-/
theorem isSufficientStatisticOf_iff_condMutualInfoOf_eq_zero
    {omega : Type u} {theta : Type v} {alpha : Type w} {beta : Type x}
    [Fintype theta] [Fintype alpha] [Fintype beta]
    (p : PMF omega) (Theta : omega → theta) (X : omega → alpha)
    (T : alpha → beta) :
    IsSufficientStatisticOf p Theta X T ↔
      condMutualInfoOf p Theta X (fun omega => T (X omega)) = 0 := by
  simpa [IsSufficientStatisticOf] using
    (condMutualInfoOf_eq_zero_iff_isMarkovChainOf p Theta
      (fun omega => T (X omega)) X).symm

/--
A finite-valued statistic is sufficient exactly when it preserves the mutual
information between the parameter and the observation under the fixed law.
-/
theorem isSufficientStatisticOf_iff_mutualInfoOf_eq
    {omega : Type u} {theta : Type v} {alpha : Type w} {beta : Type x}
    [Fintype theta] [Fintype alpha] [Fintype beta]
    (p : PMF omega) (Theta : omega → theta) (X : omega → alpha)
    (T : alpha → beta) :
    IsSufficientStatisticOf p Theta X T ↔
      mutualInfoOf p Theta (fun omega => T (X omega)) =
        mutualInfoOf p Theta X := by
  have hforward :
      IsMarkovChainOf p Theta X (fun omega => T (X omega)) :=
    isMarkovChainOf_comp p Theta X T
  simpa [IsSufficientStatisticOf] using
    (mutualInfoOf_dataProcessing_eq_iff p Theta X
      (fun omega => T (X omega)) hforward).symm

/--
A finite-valued statistic is sufficient exactly when conditioning on it leaves
the same parameter uncertainty as conditioning on the full observation.
-/
theorem isSufficientStatisticOf_iff_condEntropyOf_eq
    {omega : Type u} {theta : Type v} {alpha : Type w} {beta : Type x}
    [Fintype theta] [Fintype alpha] [Fintype beta]
    (p : PMF omega) (Theta : omega → theta) (X : omega → alpha)
    (T : alpha → beta) :
    IsSufficientStatisticOf p Theta X T ↔
      condEntropyOf p Theta X =
        condEntropyOf p Theta (fun omega => T (X omega)) := by
  have hforward :
      IsMarkovChainOf p Theta X (fun omega => T (X omega)) :=
    isMarkovChainOf_comp p Theta X T
  simpa [IsSufficientStatisticOf] using
    (condEntropyOf_dataProcessing_eq_iff p Theta X
      (fun omega => T (X omega)) hforward).symm

/-! ## Fixed-prior recovery

Write `S = T(X)`. Fixed-prior sufficiency is equivalent to a channel
factorization of the complete law

`P_(Theta,S,X) = P_(Theta,S) R`,

or atomwise `P(theta,s,x) = P(theta,s) * R s x`. One channel
`R : beta -> PMF alpha` is shared across all parameter values and cannot inspect
`theta`, although it may depend on the fixed joint law. Its rows on null
statistic fibers are unconstrained. Reconstructing the complete law preserves
the parameter-observation coupling and is strictly stronger than the one-way
marginal consequence `P_X = P_S R`; the converse of that consequence is false.
-/

private theorem isMarkovChain_statisticTripleLawOf_iff
    {omega : Type u} {theta : Type v} {alpha : Type w} {beta : Type x}
    (p : PMF omega) (Theta : omega → theta) (X : omega → alpha)
    (T : alpha → beta) :
    IsMarkovChain (statisticTripleLawOf p Theta X T) ↔
      IsSufficientStatisticOf p Theta X T := by
  unfold IsMarkovChain statisticTripleLawOf IsSufficientStatisticOf
    IsMarkovChainOf IsCondIndependentOf
  rw [PMF.map_comp]
  rfl

private theorem fstSndMarginal_statisticTripleLawOf
    {omega : Type u} {theta : Type v} {alpha : Type w} {beta : Type x}
    (p : PMF omega) (Theta : omega → theta) (X : omega → alpha)
    (T : alpha → beta) :
    fstSndMarginal (statisticTripleLawOf p Theta X T) =
      p.map fun omega => (Theta omega, T (X omega)) := by
  unfold fstSndMarginal statisticTripleLawOf
  rw [PMF.map_comp]
  rfl

/--
A fixed-prior statistic is sufficient exactly when one channel from statistic
values back to observations reconstructs the complete
`(parameter, statistic, observation)` law. The same channel is used for every
parameter value, and its behavior on a null statistic fiber is irrelevant.
-/
theorem isSufficientStatisticOf_iff_exists_recovery
    {omega : Type u} {theta : Type v} {alpha : Type w} {beta : Type x}
    [Finite alpha]
    (p : PMF omega) (Theta : omega → theta) (X : omega → alpha)
    (T : alpha → beta) :
    IsSufficientStatisticOf p Theta X T ↔
      ∃ R : beta → PMF alpha,
        statisticTripleLawOf p Theta X T =
          PMF.channelExtension
            (p.map fun omega => (Theta omega, T (X omega))) R := by
  let q := statisticTripleLawOf p Theta X T
  have hmarkov :
      IsMarkovChain q ↔ IsSufficientStatisticOf p Theta X T := by
    simpa only [q] using isMarkovChain_statisticTripleLawOf_iff p Theta X T
  have hinput :
      fstSndMarginal q = p.map fun omega => (Theta omega, T (X omega)) := by
    simpa only [q] using fstSndMarginal_statisticTripleLawOf p Theta X T
  constructor
  · intro h
    obtain ⟨R, hR⟩ :=
      (isMarkovChain_iff_exists_channelExtension q).mp (hmarkov.mpr h)
    exact ⟨R, by simpa only [q, hinput] using hR⟩
  · rintro ⟨R, hR⟩
    apply hmarkov.mp
    apply (isMarkovChain_iff_exists_channelExtension q).mpr
    exact ⟨R, by simpa only [q, hinput] using hR⟩

/--
Sufficiency implies that the observation marginal can be recovered from the
statistic marginal. This is only a one-way consequence: marginal recovery by
itself does not characterize sufficiency.
-/
theorem exists_marginal_recovery_of_isSufficientStatisticOf
    {omega : Type u} {theta : Type v} {alpha : Type w} {beta : Type x}
    [Finite alpha]
    (p : PMF omega) (Theta : omega → theta) (X : omega → alpha)
    (T : alpha → beta)
    (h : IsSufficientStatisticOf p Theta X T) :
    ∃ R : beta → PMF alpha,
      p.map X = (p.map fun omega => T (X omega)).bind R := by
  obtain ⟨R, hR⟩ :=
    (isSufficientStatisticOf_iff_exists_recovery p Theta X T).mp h
  refine ⟨R, ?_⟩
  have hmap := congrArg (fun q : PMF (theta × beta × alpha) =>
    q.map fun z => z.2.2) hR
  rw [statisticTripleLawOf, PMF.map_comp,
    PMF.channelExtension_map_output] at hmap
  have hX :
      (fun z : theta × beta × alpha => z.2.2) ∘
          (fun omega => (Theta omega, T (X omega), X omega)) = X := by
    funext omega
    rfl
  have hT :
      Prod.snd ∘ (fun omega => (Theta omega, T (X omega))) =
        (fun omega => T (X omega)) := by
    funext omega
    rfl
  rw [PMF.map_comp] at hmap
  rw [hX, hT] at hmap
  exact hmap

/-! ## Family-level sufficiency

Write `P_t = model t`. A family channel `W` is sufficient when the quantifiers
have the order `exists R, forall t` and the shared recovery channel satisfies

`((P_t.bind W) b) * R b a = P_t a * W a b`.

Thus one `R` reconstructs the complete input-output coupling for the whole
family, rather than merely recovering each input marginal or choosing a
separate witness for each `t`. This prior-free notion differs from the
fixed-law predicate `IsSufficientStatisticOf`. If an output is null for one
model, that model imposes no condition on the corresponding recovery row;
another model supporting the same output may still determine it. A row null
for every model is wholly unconstrained. `IsSufficientStatistic` is exactly
the deterministic-channel specialization of `IsSufficientChannel`, not a
second notion of family sufficiency.
-/

/--
A channel is sufficient for a model family when one recovery channel, shared
by every parameter value, reconstructs each complete output-input joint law.
-/
def IsSufficientChannel
    {theta : Type u} {alpha : Type v} {beta : Type w}
    (model : theta → PMF alpha) (W : alpha → PMF beta) : Prop :=
  ∃ R : beta → PMF alpha, ∀ t,
    PMF.channelJoint ((model t).bind W) R =
      (PMF.channelJoint (model t) W).map Prod.swap

/--
A deterministic statistic is sufficient for a model family when its induced
deterministic channel is sufficient for that family.
-/
def IsSufficientStatistic
    {theta : Type u} {alpha : Type v} {beta : Type w}
    (model : theta → PMF alpha) (T : alpha → beta) : Prop :=
  IsSufficientChannel model (PMF.deterministicChannel T)

/-- The identity statistic is sufficient for every model family. -/
theorem isSufficientStatistic_id
    {theta : Type u} {alpha : Type v}
    (model : theta → PMF alpha) :
    IsSufficientStatistic model id := by
  refine ⟨PMF.deterministicChannel id, ?_⟩
  intro t
  rw [PMF.bind_deterministicChannel, PMF.map_id]
  rw [PMF.channelJoint_deterministicChannel, PMF.map_comp]
  rfl

/-! ## Every-prior consequences

The generated law
`PMF.channelExtension (PMF.channelJoint prior model) W` has coordinate order
`(parameter, input, output)`: `z.1` is the parameter, `z.2.1` the input, and
`z.2.2` the output. Its reverse-chain conclusion therefore reads
`parameter -> output -> input`.
-/

private theorem swapLastTwo_injective
    {alpha : Type u} {beta : Type v} {gamma : Type w} :
    Function.Injective
      (fun z : alpha × beta × gamma => (z.1, z.2.2, z.2.1)) := by
  intro x y hxy
  apply Prod.ext
  · exact congrArg (fun z => z.1) hxy
  · apply Prod.ext
    · exact congrArg (fun z => z.2.2) hxy
    · exact congrArg (fun z => z.2.1) hxy

private theorem modelChannel_reverse_eq_channelExtension
    {theta : Type u} {alpha : Type v} {beta : Type w}
    (prior : PMF theta) (model : theta → PMF alpha)
    (W : alpha → PMF beta) (R : beta → PMF alpha)
    (hR : ∀ t,
      PMF.channelJoint ((model t).bind W) R =
        (PMF.channelJoint (model t) W).map Prod.swap) :
    (PMF.channelExtension (PMF.channelJoint prior model) W).map
        (fun z => (z.1, z.2.2, z.2.1)) =
      PMF.channelExtension
        (PMF.channelJoint prior (PMF.channelComp model W)) R := by
  let swap23 : theta × alpha × beta → theta × beta × alpha :=
    fun z => (z.1, z.2.2, z.2.1)
  have hswap23 : Function.Injective swap23 := by
    simpa only [swap23] using
      (swapLastTwo_injective (alpha := theta) (beta := alpha) (gamma := beta))
  apply PMF.ext
  rintro ⟨t, b, a⟩
  have hmap :
      ((PMF.channelExtension (PMF.channelJoint prior model) W).map swap23)
          (t, b, a) =
        PMF.channelExtension (PMF.channelJoint prior model) W (t, a, b) := by
    simpa [swap23] using
      PMF.map_apply_of_injective
        (PMF.channelExtension (PMF.channelJoint prior model) W)
        hswap23 (t, a, b)
  have hrecovery :=
    congrArg (fun p : PMF (beta × alpha) => p (b, a)) (hR t)
  change
    PMF.channelJoint ((model t).bind W) R (b, a) =
      ((PMF.channelJoint (model t) W).map Prod.swap) (b, a) at hrecovery
  rw [PMF.channelJoint_apply] at hrecovery
  have hswapmass :
      ((PMF.channelJoint (model t) W).map Prod.swap) (b, a) =
        PMF.channelJoint (model t) W (a, b) := by
    simpa using
      PMF.map_apply_equiv
        (PMF.channelJoint (model t) W) (Equiv.prodComm alpha beta) (a, b)
  rw [hswapmass, PMF.channelJoint_apply] at hrecovery
  rw [hmap, PMF.channelExtension_apply, PMF.channelJoint_apply,
    PMF.channelExtension_apply, PMF.channelJoint_apply]
  change prior t * model t a * W a b =
    prior t * ((model t).bind W) b * R b a
  calc
    prior t * model t a * W a b =
        prior t * (model t a * W a b) := by ac_rfl
    _ = prior t * (((model t).bind W) b * R b a) := by rw [hrecovery]
    _ = prior t * ((model t).bind W) b * R b a := by ac_rfl

/--
For every parameter prior, a sufficient family channel gives the reverse
Markov chain `parameter -> output -> input` in the generated experiment law.
-/
theorem isMarkovChainOf_of_isSufficientChannel
    {theta : Type u} {alpha : Type v} {beta : Type w}
    (prior : PMF theta) (model : theta → PMF alpha)
    (W : alpha → PMF beta) (h : IsSufficientChannel model W) :
    IsMarkovChainOf
      (PMF.channelExtension (PMF.channelJoint prior model) W)
      (fun z => z.1) (fun z => z.2.2) (fun z => z.2.1) := by
  obtain ⟨R, hR⟩ := h
  let q := PMF.channelExtension (PMF.channelJoint prior model) W
  let qrev := q.map fun z => (z.1, z.2.2, z.2.1)
  have hqrev :
      qrev = PMF.channelExtension
        (PMF.channelJoint prior (PMF.channelComp model W)) R := by
    simpa only [q, qrev] using
      modelChannel_reverse_eq_channelExtension prior model W R hR
  have hmarkov : IsMarkovChain qrev := by
    rw [hqrev]
    exact isMarkovChain_channelExtension _ _
  simpa [q, qrev, IsMarkovChain, IsMarkovChainOf, IsCondIndependentOf,
    PMF.map_comp, Function.comp_def] using hmarkov

/--
For every finite parameter prior, sufficiency makes the parameter and input
conditionally independent given the channel output.
-/
theorem condMutualInfo_eq_zero_of_isSufficientChannel
    {theta : Type u} {alpha : Type v} {beta : Type w}
    [Fintype theta] [Fintype alpha] [Fintype beta]
    (prior : PMF theta) (model : theta → PMF alpha)
    (W : alpha → PMF beta) (h : IsSufficientChannel model W) :
    condMutualInfo (PMF.channelExtension (PMF.channelJoint prior model) W) = 0 := by
  let q := PMF.channelExtension (PMF.channelJoint prior model) W
  have hmarkov :
      IsMarkovChainOf q (fun z => z.1) (fun z => z.2.2) (fun z => z.2.1) := by
    simpa only [q] using
      isMarkovChainOf_of_isSufficientChannel prior model W h
  have hcond : IsCondIndependent q := by
    unfold IsMarkovChainOf IsCondIndependentOf at hmarkov
    have hid : q.map (fun z => (z.1, z.2.1, z.2.2)) = q := by
      have hfun :
          (fun z : theta × alpha × beta => (z.1, z.2.1, z.2.2)) = id := by
        funext z
        rcases z with ⟨t, a, b⟩
        rfl
      rw [hfun, PMF.map_id]
    rw [hid] at hmarkov
    exact hmarkov
  exact (condMutualInfo_eq_zero_iff_isCondIndependent q).2 hcond

/--
For every finite parameter prior, a sufficient family channel preserves the
mutual information between the parameter and the model observation.
-/
theorem mutualInfo_eq_of_isSufficientChannel
    {theta : Type u} {alpha : Type v} {beta : Type w}
    [Fintype theta] [Fintype alpha] [Fintype beta]
    (prior : PMF theta) (model : theta → PMF alpha)
    (W : alpha → PMF beta) (h : IsSufficientChannel model W) :
    mutualInfo (PMF.channelJoint prior (PMF.channelComp model W)) =
      mutualInfo (PMF.channelJoint prior model) := by
  let q := PMF.channelExtension (PMF.channelJoint prior model) W
  have hforward : IsMarkovChain q := by
    simpa only [q] using
      isMarkovChain_channelExtension (PMF.channelJoint prior model) W
  have hreverse :
      IsMarkovChainOf q (fun z => z.1) (fun z => z.2.2) (fun z => z.2.1) := by
    simpa only [q] using
      isMarkovChainOf_of_isSufficientChannel prior model W h
  have heq := (mutualInfo_dataProcessing_eq_iff q hforward).2 hreverse
  simpa only [q, PMF.channelExtension_map_endpoints,
    PMF.channelExtension_map_input] using heq

/--
For every finite parameter prior, conditioning the parameter on a sufficient
channel output leaves the same uncertainty as conditioning on the model input.
-/
theorem condEntropy_eq_of_isSufficientChannel
    {theta : Type u} {alpha : Type v} {beta : Type w}
    [Fintype theta] [Fintype alpha] [Fintype beta]
    (prior : PMF theta) (model : theta → PMF alpha)
    (W : alpha → PMF beta) (h : IsSufficientChannel model W) :
    condEntropy (PMF.channelJoint prior model) =
      condEntropy (PMF.channelJoint prior (PMF.channelComp model W)) := by
  let q := PMF.channelExtension (PMF.channelJoint prior model) W
  have hforward : IsMarkovChain q := by
    simpa only [q] using
      isMarkovChain_channelExtension (PMF.channelJoint prior model) W
  have hreverse :
      IsMarkovChainOf q (fun z => z.1) (fun z => z.2.2) (fun z => z.2.1) := by
    simpa only [q] using
      isMarkovChainOf_of_isSufficientChannel prior model W h
  have heq := (condEntropy_dataProcessing_eq_iff q hforward).2 hreverse
  simpa only [q, PMF.channelExtension_map_input,
    PMF.channelExtension_map_endpoints] using heq

/-! ## Full-support and all-prior characterizations

Under a full-support prior, reverse-Markov factorization gives the atomwise
identity

`prior t * (P_t a * W a b) = prior t * (Q_t b * R b a)`.

Since `prior t != 0`, cancellation yields one recovery equation for every
parameter value. Full support is substantive: a zero-prior parameter is
invisible to the generated joint law and cannot be constrained by its Markov
property. On a finite nonempty parameter alphabet, the all-priors converse
uses only the canonical uniform prior from the universal hypothesis.
-/

/--
For a prior supported on every parameter value, family sufficiency is
equivalent to the reverse Markov condition in the generated experiment law.
Only the model-input alphabet must be finite.
-/
theorem isSufficientChannel_iff_isMarkovChainOf_of_support_eq_univ
    {theta : Type u} {alpha : Type v} {beta : Type w}
    [Finite alpha]
    (prior : PMF theta) (hprior : prior.support = Set.univ)
    (model : theta → PMF alpha) (W : alpha → PMF beta) :
    IsSufficientChannel model W ↔
      IsMarkovChainOf
        (PMF.channelExtension (PMF.channelJoint prior model) W)
        (fun z => z.1) (fun z => z.2.2) (fun z => z.2.1) := by
  constructor
  · exact isMarkovChainOf_of_isSufficientChannel prior model W
  · intro hmarkov
    let q := PMF.channelExtension (PMF.channelJoint prior model) W
    let swap23 : theta × alpha × beta → theta × beta × alpha :=
      fun z => (z.1, z.2.2, z.2.1)
    let qrev := q.map swap23
    have hswap23 : Function.Injective swap23 := by
      simpa only [swap23] using
        (swapLastTwo_injective (alpha := theta) (beta := alpha) (gamma := beta))
    have hqrev : IsMarkovChain qrev := by
      simpa [q, qrev, swap23, IsMarkovChain, IsMarkovChainOf,
        IsCondIndependentOf, PMF.map_comp, Function.comp_def] using hmarkov
    obtain ⟨R, hR⟩ :=
      (isMarkovChain_iff_exists_channelExtension qrev).mp hqrev
    have hinput :
        fstSndMarginal qrev =
          PMF.channelJoint prior (PMF.channelComp model W) := by
      unfold fstSndMarginal
      simp only [qrev]
      rw [PMF.map_comp]
      have hfun :
          (fun x : theta × beta × alpha => (x.1, x.2.1)) ∘ swap23 =
            (fun z : theta × alpha × beta => (z.1, z.2.2)) := by
        funext z
        rfl
      rw [hfun]
      simp only [q]
      exact PMF.channelExtension_map_endpoints prior model W
    have hfactor :
        qrev = PMF.channelExtension
          (PMF.channelJoint prior (PMF.channelComp model W)) R := by
      simpa only [hinput] using hR
    refine ⟨R, ?_⟩
    intro t
    apply PMF.ext
    rintro ⟨b, a⟩
    have hfactorMass :=
      congrArg (fun p : PMF (theta × beta × alpha) => p (t, b, a)) hfactor
    change qrev (t, b, a) =
      PMF.channelExtension
        (PMF.channelJoint prior (PMF.channelComp model W)) R (t, b, a)
      at hfactorMass
    have hmap : qrev (t, b, a) = q (t, a, b) := by
      simpa only [qrev, swap23] using
        PMF.map_apply_of_injective q hswap23 (t, a, b)
    rw [hmap, PMF.channelExtension_apply, PMF.channelJoint_apply,
      PMF.channelExtension_apply, PMF.channelJoint_apply] at hfactorMass
    change
      prior t * model t a * W a b =
        prior t * ((model t).bind W) b * R b a at hfactorMass
    have htmem : t ∈ prior.support := by
      rw [hprior]
      exact Set.mem_univ t
    have htne : prior t ≠ 0 := (prior.mem_support_iff t).1 htmem
    have hcancel :=
      congrArg (fun x : ENNReal => (prior t)⁻¹ * x) hfactorMass
    have hmass :
        model t a * W a b = ((model t).bind W) b * R b a := by
      simpa only [mul_assoc,
        ENNReal.inv_mul_cancel_left htne (prior.apply_ne_top t)] using hcancel
    rw [PMF.channelJoint_apply]
    have hswapMass :
        ((PMF.channelJoint (model t) W).map Prod.swap) (b, a) =
          PMF.channelJoint (model t) W (a, b) := by
      simpa using
        PMF.map_apply_equiv
          (PMF.channelJoint (model t) W) (Equiv.prodComm alpha beta) (a, b)
    rw [hswapMass, PMF.channelJoint_apply]
    exact hmass.symm

/--
On a finite nonempty parameter alphabet, a family channel is sufficient exactly
when it gives the reverse Markov chain for every parameter prior.
-/
theorem isSufficientChannel_iff_forall_isMarkovChainOf
    {theta : Type u} {alpha : Type v} {beta : Type w}
    [Finite theta] [Nonempty theta] [Finite alpha]
    (model : theta → PMF alpha) (W : alpha → PMF beta) :
    IsSufficientChannel model W ↔
      ∀ prior : PMF theta,
        IsMarkovChainOf
          (PMF.channelExtension (PMF.channelJoint prior model) W)
          (fun z => z.1) (fun z => z.2.2) (fun z => z.2.1) := by
  classical
  let := Fintype.ofFinite theta
  constructor
  · intro h prior
    exact isMarkovChainOf_of_isSufficientChannel prior model W h
  · intro h
    let prior := PMF.uniformOfFintype theta
    exact (isSufficientChannel_iff_isMarkovChainOf_of_support_eq_univ
      prior (by simpa only [prior, Set.top_eq_univ] using
        PMF.support_uniformOfFintype theta)
      model W).2 (h prior)

private theorem isSufficientStatisticOf_channelJoint_iff
    {theta : Type u} {alpha : Type v} {beta : Type w}
    (prior : PMF theta) (model : theta → PMF alpha) (T : alpha → beta) :
    IsSufficientStatisticOf (PMF.channelJoint prior model)
        (fun z => z.1) (fun z => z.2) T ↔
      IsMarkovChainOf
        (PMF.channelExtension (PMF.channelJoint prior model)
          (PMF.deterministicChannel T))
        (fun z => z.1) (fun z => z.2.2) (fun z => z.2.1) := by
  rw [PMF.channelExtension_deterministicChannel]
  unfold IsSufficientStatisticOf IsMarkovChainOf IsCondIndependentOf
  rw [PMF.map_comp]
  rfl

/--
For a prior supported on every parameter value, family sufficiency of a
deterministic statistic is equivalent to its fixed-prior sufficiency.
-/
theorem isSufficientStatistic_iff_isSufficientStatisticOf_of_support_eq_univ
    {theta : Type u} {alpha : Type v} {beta : Type w}
    [Finite alpha]
    (prior : PMF theta) (hprior : prior.support = Set.univ)
    (model : theta → PMF alpha) (T : alpha → beta) :
    IsSufficientStatistic model T ↔
      IsSufficientStatisticOf (PMF.channelJoint prior model)
        (fun z => z.1) (fun z => z.2) T := by
  rw [IsSufficientStatistic,
    isSufficientChannel_iff_isMarkovChainOf_of_support_eq_univ prior hprior]
  exact (isSufficientStatisticOf_channelJoint_iff prior model T).symm

/--
On a finite nonempty parameter alphabet, a deterministic statistic is
sufficient for a model family exactly when it is sufficient under every prior.
-/
theorem isSufficientStatistic_iff_forall_isSufficientStatisticOf
    {theta : Type u} {alpha : Type v} {beta : Type w}
    [Finite theta] [Nonempty theta] [Finite alpha]
    (model : theta → PMF alpha) (T : alpha → beta) :
    IsSufficientStatistic model T ↔
      ∀ prior : PMF theta,
        IsSufficientStatisticOf (PMF.channelJoint prior model)
          (fun z => z.1) (fun z => z.2) T := by
  classical
  rw [IsSufficientStatistic,
    isSufficientChannel_iff_forall_isMarkovChainOf]
  constructor
  · intro h prior
    exact (isSufficientStatisticOf_channelJoint_iff prior model T).2
      (h prior)
  · intro h prior
    exact (isSufficientStatisticOf_channelJoint_iff prior model T).1
      (h prior)

/-! ## Fisher-Neyman factorization -/

-- The converse normalizes the parameter-independent factor separately on
-- each statistic fiber. Zero-mass fibers use an irrelevant pure fallback.
private def fisherNeymanFiberWeight
    {alpha : Type u} {beta : Type v}
    (T : alpha → beta) (h : alpha → ENNReal) (b : beta) (a : alpha) : ENNReal := by
  classical
  exact if b = T a then h a else 0

private def fisherNeymanFiberMass
    {alpha : Type u} {beta : Type v}
    (T : alpha → beta) (h : alpha → ENNReal) (b : beta) : ENNReal :=
  ∑' a, fisherNeymanFiberWeight T h b a

private theorem fisherNeymanFiberMass_ne_top
    {alpha : Type u} {beta : Type v} [Finite alpha]
    (T : alpha → beta) (h : alpha → ENNReal)
    (hh : ∀ a, h a ≠ ⊤) (b : beta) :
    fisherNeymanFiberMass T h b ≠ ⊤ := by
  classical
  let := Fintype.ofFinite alpha
  rw [fisherNeymanFiberMass, tsum_fintype]
  apply ENNReal.sum_ne_top.2
  intro a _ha
  by_cases hab : b = T a
  · simpa [fisherNeymanFiberWeight, hab] using hh a
  · simp [fisherNeymanFiberWeight, hab]

private def fisherNeymanRecovery
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Nonempty alpha]
    (T : alpha → beta) (h : alpha → ENNReal)
    (hh : ∀ a, h a ≠ ⊤) : beta → PMF alpha :=
  fun b =>
    if hb : fisherNeymanFiberMass T h b = 0 then
      PMF.pure (Classical.choice (inferInstance : Nonempty alpha))
    else
      PMF.normalize (fisherNeymanFiberWeight T h b) hb
        (fisherNeymanFiberMass_ne_top T h hh b)

private theorem fisherNeymanRecovery_apply_of_fiberMass_ne_zero
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Nonempty alpha]
    (T : alpha → beta) (h : alpha → ENNReal)
    (hh : ∀ a, h a ≠ ⊤) {b : beta}
    (hb : fisherNeymanFiberMass T h b ≠ 0) (a : alpha) :
    fisherNeymanRecovery T h hh b a =
      fisherNeymanFiberWeight T h b a *
        (fisherNeymanFiberMass T h b)⁻¹ := by
  rw [fisherNeymanRecovery, dite_eq_right hb]
  change
    fisherNeymanFiberWeight T h b a *
        (∑' x, fisherNeymanFiberWeight T h b x)⁻¹ =
      fisherNeymanFiberWeight T h b a *
        (fisherNeymanFiberMass T h b)⁻¹
  rfl

private theorem map_statistic_eq_factor_mul_fiberMass
    {theta : Type u} {alpha : Type v} {beta : Type w}
    (model : theta → PMF alpha) (T : alpha → beta)
    (g : theta → beta → ENNReal) (h : alpha → ENNReal)
    (hfactor : ∀ t a, model t a = g t (T a) * h a)
    (t : theta) (b : beta) :
    (model t).map T b = g t b * fisherNeymanFiberMass T h b := by
  rw [PMF.map_apply, fisherNeymanFiberMass, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro a
  by_cases hab : b = T a
  · rw [ite_eq_left hab, fisherNeymanFiberWeight, ite_eq_left hab, hfactor, ← hab]
  · rw [ite_eq_right hab, fisherNeymanFiberWeight, ite_eq_right hab, mul_zero]

/--
Finite Fisher-Neyman factorization theorem for deterministic statistics.
A statistic is sufficient for a model family exactly when every model mass
factors through the statistic into a parameter-dependent factor `g` and one
parameter-independent factor `h`. Pointwise finiteness of `h` makes each finite
fiber mass `sum_{a : T a = b} h a` finite and permits normalization on a
positive fiber. Pointwise finiteness of `g` separately excludes pathological
top-valued witnesses and matches the canonical forward witness
`g t b = (model t).map T b`; it is not the hypothesis used to normalize the
recovery row.
-/
theorem isSufficientStatistic_iff_exists_fisherNeymanFactorization
    {theta : Type u} {alpha : Type v} {beta : Type w}
    [Finite alpha] [Nonempty alpha]
    (model : theta → PMF alpha) (T : alpha → beta) :
    IsSufficientStatistic model T ↔
      ∃ g : theta → beta → ENNReal, ∃ h : alpha → ENNReal,
        (∀ t b, g t b ≠ ⊤) ∧
          (∀ a, h a ≠ ⊤) ∧
            ∀ t a, model t a = g t (T a) * h a := by
  classical
  let := Fintype.ofFinite alpha
  constructor
  · intro hsuff
    rw [IsSufficientStatistic, IsSufficientChannel] at hsuff
    rcases hsuff with ⟨R, hR⟩
    let g : theta → beta → ENNReal := fun t b => (model t).map T b
    let h : alpha → ENNReal := fun a => R (T a) a
    refine ⟨g, h, ?_, ?_, ?_⟩
    · intro t b
      exact ((model t).map T).apply_ne_top b
    · intro a
      exact (R (T a)).apply_ne_top a
    · intro t a
      have hmass :=
        congrArg (fun q : PMF (beta × alpha) => q (T a, a)) (hR t)
      have hswap :
          ((PMF.channelJoint (model t) (PMF.deterministicChannel T)).map
            Prod.swap) (T a, a) =
            PMF.channelJoint (model t) (PMF.deterministicChannel T) (a, T a) := by
        simpa using
          PMF.map_apply_equiv
            (PMF.channelJoint (model t) (PMF.deterministicChannel T))
            (Equiv.prodComm alpha beta) (a, T a)
      change
        PMF.channelJoint ((model t).bind (PMF.deterministicChannel T)) R
            (T a, a) =
          ((PMF.channelJoint (model t) (PMF.deterministicChannel T)).map
            Prod.swap) (T a, a) at hmass
      rw [PMF.channelJoint_apply, hswap, PMF.channelJoint_apply] at hmass
      have hmass' : (model t).map T (T a) * R (T a) a = model t a := by
        simpa using hmass
      simpa only [g, h] using hmass'.symm
  · rintro ⟨g, h, _hg, hh, hfactor⟩
    rw [IsSufficientStatistic, IsSufficientChannel]
    refine ⟨fisherNeymanRecovery T h hh, ?_⟩
    intro t
    apply PMF.ext
    rintro ⟨b, a⟩
    have hswap :
        ((PMF.channelJoint (model t) (PMF.deterministicChannel T)).map
          Prod.swap) (b, a) =
          PMF.channelJoint (model t) (PMF.deterministicChannel T) (a, b) := by
      simpa using
        PMF.map_apply_equiv
          (PMF.channelJoint (model t) (PMF.deterministicChannel T))
          (Equiv.prodComm alpha beta) (a, b)
    rw [PMF.channelJoint_apply, PMF.bind_deterministicChannel,
      map_statistic_eq_factor_mul_fiberMass model T g h hfactor t b,
      hswap, PMF.channelJoint_apply]
    by_cases hb0 : fisherNeymanFiberMass T h b = 0
    · rw [hb0, mul_zero, zero_mul]
      by_cases hab : b = T a
      · have hweightZero : fisherNeymanFiberWeight T h b a = 0 := by
          apply (ENNReal.tsum_eq_zero.mp ?_) a
          simpa only [fisherNeymanFiberMass] using hb0
        have hha : h a = 0 := by
          simpa only [fisherNeymanFiberWeight, ite_eq_left hab] using hweightZero
        rw [hfactor, ← hab, hha, mul_zero]
        simp [PMF.deterministicChannel, hab]
      · simp [PMF.deterministicChannel, hab]
    · rw [fisherNeymanRecovery_apply_of_fiberMass_ne_zero T h hh hb0]
      by_cases hab : b = T a
      · rw [fisherNeymanFiberWeight, ite_eq_left hab]
        calc
          (g t b * fisherNeymanFiberMass T h b) *
                (h a * (fisherNeymanFiberMass T h b)⁻¹) =
              g t b * h a *
                (fisherNeymanFiberMass T h b *
                  (fisherNeymanFiberMass T h b)⁻¹) := by
            ac_rfl
          _ = g t b * h a := by
            rw [ENNReal.mul_inv_cancel hb0
              (fisherNeymanFiberMass_ne_top T h hh b), mul_one]
          _ = model t a := by
            rw [hab]
            exact (hfactor t a).symm
          _ = model t a * PMF.deterministicChannel T a b := by
            simp [PMF.deterministicChannel, hab]
      · rw [fisherNeymanFiberWeight, ite_eq_right hab, zero_mul, mul_zero]
        simp [PMF.deterministicChannel, hab]

end

end Shannon
end LeanInfoTheory
