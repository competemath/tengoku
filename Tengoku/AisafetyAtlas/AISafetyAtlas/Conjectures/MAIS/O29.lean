module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Conjectures.BinaryPair
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Causal.Decision
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Causal.EffectiveGenericity
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Causal.ParameterChart
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Causal.Query
public import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic
public import Tengoku.Seed.Data.Real.Basic
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Conjectures.MAIS.Common

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# MAIS-O29 — Boltzmann agents

`prob:boltzmann`(a): is the map from models to Boltzmann behaviour injective on
`𝕄(sk, λ)`? That is a question about the map and needs no statistics, which is
why it lives here.

Parts (b) and (c) speak about a minimax risk at budget `N`, which needs a
sampled statistical experiment. `AISafetyAtlas.Conjectures.MAIS.O29Experiment`
builds it — the exact-oracle protocol with the oracle replaced by a coin — and
proves that a collision answering (a) floors (b)'s risk at `1/2` at every budget
and every `β`. Paired with `boltzmannMinimaxRisk_le_one` that **determines (b)'s
quantity up to a factor of two** on such a class, which is (b)'s own *"up to
constants"* — at one print-legal instance and at no other, since a class where
the risk decays is untouched and is where (b)'s rate, its `β → 0` deterioration
and its `(N, β)` crossover live.

Part (c) is untouched, and unlike (b) it can never be a ledger row: *"which
distribution over queries maximizes the minimax rate?"* is a design problem with
no truth-valued clause anywhere in it, so no `Prop` is `Same` as it.

Stated at the MAIS revision pinned in `docs/provenance/mais-source-pin.md`.
Defining a proposition asserts nothing about its truth; resolutions live in
`AISafetyAtlas/Examples/Conjectures/`.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.BinaryPair

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
variable {dim : C → ℕ}

/-! ## Boltzmann behavior -/

/-- Probability mass of one visible observation fibre — the normalizer of
MAIS-A2's conditional `P_M(𝐙 = z ∣ 𝐎' = w; σ)`.-/
@[expose] public noncomputable def fibreMass (M : Model C dim ℝ) (visible : Finset C)
    (mix : ProbMixture C dim ℝ) (observation : Assignment C dim) : ℝ :=
  ∑ v ∈ Finset.univ.filter (fun v : Assignment C dim ↦
    ∀ c ∈ visible, v c = observation c), M.jointProbMix mix.1 v

/-- The source's binary Boltzmann response probability.

MAIS-A2 `subsec:queries` writes it as
`π_β(1 ∣ w; σ, 𝐎') = e^{β E(1,w;σ)} / (e^{β E(0,w;σ)} + e^{β E(1,w;σ)})` with
`E_M^{𝐎'}(d, w; σ) = ∑_z u(d,z) P_M(𝐙 = z ∣ 𝐎' = w; σ)`, and stipulates uniform
answers at zero-probability observations — here `1/2`, the uniform distribution
on a binary decision. `fibreScore / fibreMass` is that conditional expectation.-/
@[expose] public noncomputable def boltzmannTrueProbability (M : Model C dim ℝ)
    (sk : Skeleton C dim Bool ℝ) (visible : Finset C) (mix : ProbMixture C dim ℝ)
    (observation : Assignment C dim) (β : ℝ) : ℝ :=
  if _h : fibreMass M visible mix observation = 0 then 1 / 2 else
    let mass : ℝ := fibreMass M visible mix observation
    let scoreTrue : ℝ := M.fibreScore sk visible mix observation true
    let scoreFalse : ℝ := M.fibreScore sk visible mix observation false
    Real.exp (β * scoreTrue / mass) /
      (Real.exp (β * scoreFalse / mass) + Real.exp (β * scoreTrue / mass))

/-- Equality of the complete Boltzmann behavior family at inverse temperature
`β`, masks included.-/
@[expose] public noncomputable def BoltzmannBehaviorEq (sk : Skeleton C dim Bool ℝ)
    (β : ℝ) (M M' : Model C dim ℝ) : Prop :=
  ∀ (visible : Finset C) (_hvisible : visible ⊆ sk.observed)
    (mix : ProbMixture C dim ℝ) (observation : Assignment C dim),
    boltzmannTrueProbability M sk visible mix observation β =
      boltzmannTrueProbability M' sk visible mix observation β

/-- A two-point softmax is a function of the *difference* of its two scores.-/
private theorem softmax_shift (β s d mass : ℝ) :
    Real.exp (β * s / mass) /
        (Real.exp (β * (s - d) / mass) + Real.exp (β * s / mass)) =
      1 / (Real.exp (-(β * d / mass)) + 1) := by
  have hsplit : β * (s - d) / mass = β * s / mass - β * d / mass := by ring
  have hden : Real.exp (β * s / mass) / Real.exp (β * d / mass) +
      Real.exp (β * s / mass) =
      Real.exp (β * s / mass) * ((Real.exp (β * d / mass))⁻¹ + 1) := by ring
  rw [hsplit, Real.exp_sub, hden, div_mul_eq_div_div,
    div_self (Real.exp_ne_zero _), Real.exp_neg]

/--
**MAIS-O29(a), negative-answer branch.**

MAIS-A2 `prob:boltzmann` part (a) asks, for a known inverse temperature `β`,
whether the map from models to Boltzmann behavior is injective on `𝕄(sk, λ)`.
The negative answer is the statement below, at the source's own quantifiers:
*for every* positive `β`, *some* skeleton over a finite set of binary chance
variables carries two distinct margin-class models with identical complete
Boltzmann response families.

Tables, utilities and mixture weights are real, as in `def:cid` and
`def:margin`; `Fin (m + 1)` is A2's own indexing of `𝐂 = {C₁, …, C_m}`, which
(M5) forces to be nonempty; `Bool` is `def:cid`'s binary decision.-/
@[expose] public noncomputable def maisO29_boltzmannNotInjective : Prop :=
  ∀ β : ℝ, 0 < β →
    ∃ (m : ℕ) (sk : Skeleton (Fin (m + 1)) (binaryDim (Fin (m + 1))) Bool ℝ) (lam : ℝ),
      Skeleton.ValidMargin lam ∧
        ∃ M M' : Model (Fin (m + 1)) (binaryDim (Fin (m + 1))) ℝ,
          sk.MarginClass M lam ∧ sk.MarginClass M' lam ∧ M ≠ M' ∧
            BoltzmannBehaviorEq sk β M M'

end AISafetyAtlas.Conjectures.MAIS
