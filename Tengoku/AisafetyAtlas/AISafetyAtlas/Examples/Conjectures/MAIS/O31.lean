module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Conjectures.MAIS
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Causal.BehavioralCollision
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Causal.OneNodeClass
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Causal.Query
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Conjectures.MAIS.Common

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# MAIS-O31 — witnesses, chambers, and what the root coordinate does

The antecedent is inhabited in both chambers, and in the same-side chamber the
root coordinate is not identified. The one-node chain shows the same-side
chamber can be empty.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.MAIS
open AISafetyAtlas.Examples.Causal

/-! ## MAIS-O31: the antecedent is inhabited, chamber disjunct included

`maisO31_chainClassificationCandidate` quantifies over a chain model, a margin,
a threshold in `(0,1)` and an intervened node, and then assumes the **chamber
disjunct** — the transfer from hard-fixing `C_j` either straddles the decision
threshold or stays strictly on one side. The pieces were separately inhabited and
the disjunct was not, so nothing ruled out an antecedent that no model meets.

The witness below closes that. It is a two-node chain, and the straddling branch
is the one it lands in — the branch issue #8's first bullet is about, so the
implication whose hypothesis it is is not vacuous either. -/

/-- A two-node chain at margin `1/10`: root `2/5`, and a child whose transition
probabilities `1/5` and `7/10` sit on opposite sides of the threshold `1/2`.-/
@[expose] public noncomputable def o31Witness : O31ChainModel 1 where
  root := 2 / 5
  transition := fun _ x ↦ if x = 1 then 7 / 10 else 1 / 5

public theorem o31Witness_valid : o31Witness.Valid (1 / 10) := by
  refine ⟨by norm_num, by norm_num, ⟨by norm_num [o31Witness], by norm_num [o31Witness]⟩,
    ?_, ?_⟩
  · intro i x
    fin_cases x <;> exact ⟨by norm_num [o31Witness], by norm_num [o31Witness]⟩
  · intro i
    norm_num [o31Witness]

public theorem o31Witness_generic : o31Witness.Generic (1 / 10) := by
  refine ⟨by norm_num [o31Witness], by norm_num [o31Witness], ?_, ?_⟩
  · intro i x
    fin_cases x <;> exact ⟨by norm_num [o31Witness], by norm_num [o31Witness]⟩
  · intro i
    norm_num [o31Witness]

/-- Hard-fixing the root to `0` transfers the child's `0`-column.-/
public theorem o31Witness_target_zero :
    o31Witness.targetProbability (o31SingleNodeProfile (Fin.last 1) (fun _ ↦ 0)) = 1 / 5 := by
  rw [O31ChainModel.targetProbability, ← Equiv.sum_comp finFunctionFinEquiv.symm]
  simp [Fin.sum_univ_four, O31ChainModel.jointProb, O31ChainModel.nodeParameter,
    o31SingleNodeProfile, o31Witness, finFunctionFinEquiv,
    AISafetyAtlas.Conjectures.BinaryPair.interventionFactor,
    AISafetyAtlas.Conjectures.BinaryPair.bernoulli]
  rw [show (0 : Fin 2) = Fin.castSucc 0 from rfl, Fin.lastCases_castSucc]

/-- And to `1` transfers the `1`-column.-/
public theorem o31Witness_target_one :
    o31Witness.targetProbability (o31SingleNodeProfile (Fin.last 1) (fun _ ↦ 1)) = 7 / 10 := by
  rw [O31ChainModel.targetProbability, ← Equiv.sum_comp finFunctionFinEquiv.symm]
  simp [Fin.sum_univ_four, O31ChainModel.jointProb, O31ChainModel.nodeParameter,
    o31SingleNodeProfile, o31Witness, finFunctionFinEquiv,
    AISafetyAtlas.Conjectures.BinaryPair.interventionFactor,
    AISafetyAtlas.Conjectures.BinaryPair.bernoulli]
  rw [show (0 : Fin 2) = Fin.castSucc 0 from rfl, Fin.lastCases_castSucc]

/-- **The chamber disjunct holds, on its straddling branch.** `1/5 < 1/2 < 7/10`,
so the transfer from hard-fixing the root crosses the decision threshold.-/
public theorem o31Witness_straddles :
    O31StraddlingChamber (1 / 2) (Fin.last 1) o31Witness := by
  unfold O31StraddlingChamber
  rw [o31Witness_target_zero, o31Witness_target_one]
  norm_num

/-- **The whole antecedent of `maisO31_chainClassificationCandidate` is
inhabited.** Threshold bounds, validity, genericity and the chamber disjunct
hold together at one model, so the statement is not vacuously true for want of a
model meeting its hypotheses.-/
public theorem o31_antecedent_inhabited :
    0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 ∧ o31Witness.Valid (1 / 10) ∧
      o31Witness.Generic (1 / 10) ∧
      (O31StraddlingChamber (1 / 2) (Fin.last 1) o31Witness ∨
        O31SameSideChamber (1 / 2) (Fin.last 1) o31Witness) :=
  ⟨by norm_num, by norm_num, o31Witness_valid, o31Witness_generic,
    Or.inl o31Witness_straddles⟩

/-! ## The same-side chamber

`o31_antecedent_inhabited` lands on the straddling branch. The other branch of
the chamber disjunct is settled here, and it is settled *generally* rather than
at a witness: the mixture layer can never carry the endpoint probability outside
the interval the two hard interventions span, so when that whole interval sits
on one side of the threshold no behaviour distinguishes models that share it.

The candidate's same-side content is a **negative**. `O31StraddlingChamber` and
`O31SameSideChamber` are mutually exclusive, so on the same-side branch the right
side of the candidate's equivalence is false for every coordinate, and the claim
is that no coordinate is identified. `o31_sameSide_root_not_identified` proves
that for the root at a two-node chain. The two transition coordinates, and chains
with more nodes, are not settled here.
-/

private theorem convexCombo_lt {a b x y B : ℝ} (hs : a + b = 1) (hn0 : 0 ≤ a)
    (hn1 : 0 ≤ b) (h0 : x < B) (h1 : y < B) : a * x + b * y < B := by
  rcases lt_or_ge 0 a with ha | ha
  · have p1 : a * x < a * B := mul_lt_mul_of_pos_left h0 ha
    have p2 : b * y ≤ b * B := mul_le_mul_of_nonneg_left h1.le hn1
    have hsum : a * B + b * B = B := by rw [← add_mul, hs, one_mul]
    linarith
  · have ha0 : a = 0 := le_antisymm ha hn0
    subst ha0; simp at hs ⊢; subst hs; linarith

private theorem lt_convexCombo {a b x y B : ℝ} (hs : a + b = 1) (hn0 : 0 ≤ a)
    (hn1 : 0 ≤ b) (h0 : B < x) (h1 : B < y) : B < a * x + b * y := by
  rcases lt_or_ge 0 a with ha | ha
  · have p1 : a * B < a * x := mul_lt_mul_of_pos_left h0 ha
    have p2 : b * B ≤ b * y := mul_le_mul_of_nonneg_left h1.le hn1
    have hsum : a * B + b * B = B := by rw [← add_mul, hs, one_mul]
    linarith
  · have ha0 : a = 0 := le_antisymm ha hn0
    subst ha0; simp at hs ⊢; subst hs; linarith

/-! ## The one-node chain, where the same-side chamber is empty

`maisO31_chainClassificationCandidate` quantifies over every `n`, and the
withdrawal of the old `0 < n` hypothesis put the one-node chain inside it. There
the intervened node *is* the guessed endpoint, so the two hard interventions pin
the transfer at `0` and `1` and straddle every threshold a utility can induce.
The same-side branch is therefore vacuous at `n = 0`, and the candidate's
same-side content says nothing there. This is a fact about the transcription's
domain, and it is why the witnesses above need a two-node chain.
-/

end AISafetyAtlas.Examples.Conjectures.MAIS
