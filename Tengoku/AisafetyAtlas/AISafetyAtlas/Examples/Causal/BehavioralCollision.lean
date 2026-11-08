module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Causal.MarginClass

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Three causal models with one behavior

The construction submitted to MAIS as a candidate negative resolution of
**MAIS-O23** (*Do margins imply behavioral identifiability of causal models?*),
checked here.

## The claim being checked

MAIS-O23 asks: fix a skeleton and `λ ∈ (0, ½)`; if two models of the margin
class `M(s, λ)` have equal behavioral transforms, must they be equal?

The submission (`lionellevine/MAIS` issue #6, filed 2026-08-04, open and
unreviewed at the time of writing) answers **no**, with three distinct models on
two binary variables — the edgeless graph, `X → Y`, and `Y → X` — whose
transforms agree on every one of the sixteen local-intervention profiles.

Skeleton: `C = {X, Y}`, `O = ∅`, `Z = {X, Y}`, `λ = 1/10`, utility gap

```
g(x, y) = 1/2 - 1_{(x,y) = (1,1)}
```

and the three models

| graph | parameters |
|---|---|
| edgeless | `P(X=1) = 1/2`, `P(Y=1) = 4/5` |
| `X → Y` | `P(X=1) = 1/2`, `P(Y=1 ∣ X=0) = 1/5`, `P(Y=1 ∣ X=1) = 4/5` |
| `Y → X` | `P(Y=1) = 4/5`, `P(X=1 ∣ Y=0) = 4/5`, `P(X=1 ∣ Y=1) = 1/2` |

## Why it works

`g` is `1/2` everywhere except at `(1,1)`, so

```
Δ_M(σ) = 1/2 - P_M(X=1, Y=1 ; σ)
```

and the transform reads **only the `(1,1)` cell**. The three models'
observational marginals genuinely differ — `P(Y=1)` is `1/2` under `X → Y` but
`4/5` under the edgeless model — and no behavior can see that, because the
utility gap does not.

**Nothing cancels, and the distinction matters.** The agenda speaks of a
*cancellation mechanism* that a counterexample would reveal, but here no terms
cancel: the three models simply **agree** on the table values at the one
assignment `g` weights. At `(1,1)` all three have `P(X=1 ∣ ·) = 1/2` and
`P(Y=1 ∣ ·) = 4/5`, so the per-variable factors are equal one by one at every
profile, and the hard profiles force exactly this — `do(X=1)` makes `Δ` read
`P(Y=1 ∣ X=1)` and nothing else. The excluded locus is therefore an
intersection of *coordinate* conditions, not the vanishing locus of a generic
polynomial.

**What that says about the margin class.** Conditions (M2), (M3) and (M6)
constrain the gap's magnitude, its sign, and its sensitivity to each utility
parent — and this `g`, constant off a single `z`, satisfies all three. They do
not force `g` to be *rich*. A seventh condition bounding the gap's spread across
`dom(Z)` is the natural repair, and that is the actionable output of this
example for MAIS-O24.

## What is checked

* The transforms of all three models agree at **every** deterministic
  intervention pattern (`collision_edgeless_arrowXY`, `collision_edgeless_arrowYX`,
  `collision_arrowXY_arrowYX`); hence, by `Model.Δmix_congr`, at every ambient
  rational weight function (`collision_mix_edgeless_arrowXY` and companions),
  and therefore at every rational probability mixture. RE24's real simplex is
  not cast here. Since `O = ∅`, the transform *family* `(Δ^{O'})_{O' ⊆ O}` has
  the single component `Δ^∅ = Δ`, so this is equality of the whole family.
* All three models lie in the margin class at `λ = 1/10`: `edgeless_mem`,
  `arrowXY_mem`, `arrowYX_mem`, each a conjunction of six named conditions.
  **Where the weight sits, for a reviewer deciding where to push:** (M1) and (M4)
  are the only conditions the models have to earn. (M2), (M3) and (M6) depend on
  the gap alone, so they are proved once for the skeleton and shared; and (M5)
  holds for *any* model on this skeleton (`skel_M5`), because `Z = C` makes the
  ancestor condition automatic and `O = ∅` makes the hiding condition automatic.
* The models are pairwise distinct as graphs, and the shared transform is not
  degenerate — `transform_identity_edgeless` pins one of its values at `1/10`.

Together: `margin_class_not_identifiable`, two models of `M(s, λ)` at a margin
`λ ∈ (0, ½)`, distinct as graphs, with equal behavioral transforms — the full
family `(Δ^{O'})_{O' ⊆ O}`, not one component of it. **MAIS-O23, as transcribed
in `AISafetyAtlas.Causal.MarginClass`, is answered in the negative.**

`u` and `u_gap` exhibit a utility with values in `[0,1]` realizing the gap, so
the skeleton is one of the source's and not merely one satisfying the conditions
that are phrased in terms of `g`. The utility is now carried by `Skeleton`; the
two theorems sit beside `skel` because they are the concrete witness used to
construct it. The decision layer consumes this same stored utility.

**The masking layer is defined but not exercised here.** `O = ∅`, so
`Skeleton.BehaviorEq` quantifies over the single visible subset `∅` and the
family `(Δ^{O'})` has one member. That is what a counterexample to a statement
quantified over skeletons needs, and `(M5)` permits it (`O ⊊ C`), but a reviewer
should not read the headline as evidence about masking: the agenda's Remark 2.6
failure mode — the unmasked component non-injective while the family is
injective — is exactly what an example with no masks cannot exhibit. The family
layer is here so the *statement* is the source's, not because this example
tests it.

## What is a review question and not a build question

Whether that transcription is faithful to MAIS-A2 Definition 3.1. Three readings
carry the result and a reviewer should check each:

1. **The skeleton fixes no graph**, so the edgeless model belongs to `M(s, λ)`
   whenever the six conditions hold, and (M4) is vacuous for it. The agenda's
   §5 class `MM₂(λ)` is *not* this class — it is defined as the models carrying
   `G→` or `G←`. The result does not need the edgeless model: `arrowXY` and
   `arrowYX` alone are distinct and collide (`collision_mix_arrowXY_arrowYX`,
   `margin_class_not_identifiable_two_graphs`), so it survives the narrower
   reading too.
2. **(M3)'s slice condition** collapses, at `O = ∅`, to *`g` takes both signs*.
3. **This collision uses the gap.** The collision calculations read `g` (the
   derived `Skeleton.gap`), while the decision layer can read the stored `u`.
   `u_mem_unitInterval` and `u_gap` discharge the one thing that could go wrong
   — a gap no admissible utility realizes — for this skeleton.

**Not claimed:** priority. Issue #6 credits the prior construction in issue #4
(MAIS-O34, filed by a different author), and states that its own contribution is
making the O23 consequence explicit and extending it to all three graphs on two
binary variables. The atlas contributes the machine check, not the construction.
-/

namespace AISafetyAtlas.Examples.Causal

open AISafetyAtlas.Causal

local notation:max "Assignment" C:arg =>
  AISafetyAtlas.Causal.Assignment C (binaryDim C)
local notation:max "Model" C:arg =>
  AISafetyAtlas.Causal.Model C (binaryDim C) ℚ
local notation:max "InterventionProfile" C:arg =>
  AISafetyAtlas.Causal.InterventionProfile C (binaryDim C)
local notation:max "Mixture" C:arg =>
  AISafetyAtlas.Causal.Mixture C (binaryDim C) ℚ
local notation:max "Skeleton" C:arg =>
  AISafetyAtlas.Causal.Skeleton C (binaryDim C) Bool ℚ

namespace LocalIntervention

@[expose] public def identity : Fin 2 → Fin 2 := identityIntervention

@[expose] public def fix (b : Bool) : Fin 2 → Fin 2 := fixIntervention (binaryState b)

end LocalIntervention

@[expose] public def bernoulli (q : ℚ) (a : Fin 2) : ℚ := if a = 1 then q else 1 - q

/-- `X` is variable `0`.-/
public abbrev X : Fin 2 := 0
/-- `Y` is variable `1`.-/
public abbrev Y : Fin 2 := 1

/-- The utility gap `g(x, y) = 1/2 - 1_{(x,y) = (1,1)}`, of constant magnitude
`1/2` and taking both signs.-/
@[expose] public def g : Assignment (Fin 2) → ℚ :=
  fun v => if v X = 1 ∧ v Y = 1 then -(1/2) else 1/2

/-- The edgeless model: `P(X=1) = 1/2`, `P(Y=1) = 4/5`, independent.-/
@[expose] public def edgeless : Model (Fin 2) where
  dim_pos := by intro c; simp [binaryDim]
  parents := fun _ => ∅
  acyclic := ⟨fun _ => 0, by intro c p hp; simp at hp⟩
  cpt := fun c a _ => bernoulli (if c = X then 1/2 else 4/5) a
  cpt_parents := by intro c a v w _; rfl
  cpt_nonneg := by
    intro c a v
    fin_cases a <;> simp [bernoulli] <;> split_ifs <;> norm_num
  cpt_sum := by
    intro c v
    rw [Fin.sum_univ_two]
    simp [bernoulli]

/-- The `X → Y` model: `P(X=1) = 1/2`, `P(Y=1 ∣ X=0) = 1/5`, `P(Y=1 ∣ X=1) = 4/5`.-/
@[expose] public def arrowXY : Model (Fin 2) where
  dim_pos := by intro c; simp [binaryDim]
  parents := fun c => if c = Y then {X} else ∅
  acyclic := ⟨fun c => if c = Y then 1 else 0, by decide⟩
  cpt := fun c a v => bernoulli
    (if c = X then 1/2 else if v X = 1 then 4/5 else 1/5) a
  cpt_parents := by
    intro c a v w h
    fin_cases c
    · simp
    · have hX : v X = w X := h X (by simp)
      simp [hX]
  cpt_nonneg := by
    intro c a v
    fin_cases a <;> simp [bernoulli] <;> split_ifs <;> norm_num
  cpt_sum := by
    intro c v
    rw [Fin.sum_univ_two]
    simp [bernoulli]

/-- The `Y → X` model: `P(Y=1) = 4/5`, `P(X=1 ∣ Y=0) = 4/5`, `P(X=1 ∣ Y=1) = 1/2`.-/
@[expose] public def arrowYX : Model (Fin 2) where
  dim_pos := by intro c; simp [binaryDim]
  parents := fun c => if c = X then {Y} else ∅
  acyclic := ⟨fun c => if c = X then 1 else 0, by decide⟩
  cpt := fun c a v => bernoulli
    (if c = Y then 4/5 else if v Y = 1 then 1/2 else 4/5) a
  cpt_parents := by
    intro c a v w h
    fin_cases c
    · have hY : v Y = w Y := h Y (by simp)
      simp [hY]
    · simp
  cpt_nonneg := by
    intro c a v
    fin_cases a <;> simp [bernoulli] <;> split_ifs <;> norm_num
  cpt_sum := by
    intro c v
    rw [Fin.sum_univ_two]
    simp [bernoulli]

/-! ## The margin class

`MAIS-O23` quantifies over `M(s, λ)`, so a collision only bears on it once the
three models are shown to live there. Skeleton: `O = ∅`, `Z = {X, Y}`, utility
gap `g`, and margin `λ = 1/10`.
-/

/- A utility realizing the gap, with values in `[0,1]` as Definition 2.3 requires. -/
@[expose] public def u (d : Bool) (v : Assignment (Fin 2)) : ℚ :=
  if d then (1 + g v)/2 else (1 - g v)/2

/-- The utility takes values in `[0,1]`.-/
public theorem u_mem_unitInterval (d : Bool) (v : Assignment (Fin 2)) :
    0 ≤ u d v ∧ u d v ≤ 1 := by
  have h : g v = 1/2 ∨ g v = -(1/2) := by
    by_cases hv : v X = 1 ∧ v Y = 1
    · right
      simp [g, hv]
    · left
      simp [g, hv]
  cases d <;> rcases h with h | h <;> constructor <;> simp [u, h] <;> norm_num

/-- The utility realizes the gap: `g(z) = u(1,z) - u(0,z)`.-/
public theorem u_gap (v : Assignment (Fin 2)) : u true v - u false v = g v := by
  simp [u]; ring

/-- The skeleton of the construction: nothing observed, both variables scored.-/
@[expose] public def skel : Skeleton (Fin 2) where
  observed := ∅
  utilityParents := Finset.univ
  utility := u
  utility_parents := by
    intro d v w h
    have : v = w := funext fun c => h c (Finset.mem_univ c)
    rw [this]
  utility_mem_unitInterval := u_mem_unitInterval

/-- The gap computed from `skel` is the construction's named gap.-/
public theorem skel_gap : skel.gap = g := by
  funext v
  exact u_gap v

/-- The margin.-/
@[expose] public def lam : ℚ := 1/10

/-- `g` takes the value `1/2` off the corner `(1,1)` and `-1/2` on it, so `|g| = 1/2`.-/
public theorem abs_g (v : Assignment (Fin 2)) : |g v| = 1/2 := by
  by_cases hv : v X = 1 ∧ v Y = 1 <;> simp [g, hv]

/-- **(M2)** holds: the decision always matters, by a margin of `1/2`.-/
public theorem skel_M2 : skel.M2 lam := by
  intro v
  rw [skel_gap, abs_g]
  norm_num [lam]

/-- **(M3)** holds: with nothing observed the slice condition is that `g` takes
both signs, and it does.-/
public theorem skel_M3 : skel.M3 := by
  intro w
  refine ⟨asg false false, asg true true, ?_, ?_, ?_, ?_⟩
  · intro c hc; simp [skel] at hc
  · intro c hc; simp [skel] at hc
  · rw [skel_gap]
    norm_num [g, asg, binaryState]
  · rw [skel_gap]
    norm_num [g, asg, binaryState]

/-- **(M5)** holds for any model on this skeleton: the score reads every
variable, so every parent-closed superset of the utility parents is everything,
and nothing is observed, so something is hidden.-/
public theorem skel_M5 (M : Model (Fin 2)) : skel.M5 M := by
  constructor
  · intro t ht _
    refine Finset.univ_subset_iff.mp fun c _ => ht ?_
    simp [skel]
  · exact Finset.ssubset_univ_iff.mpr (by decide)

/-- **(M6)** holds: flipping either variable at `(1,1)` moves the gap by `1`.-/
public theorem skel_M6 : skel.M6 lam := by
  intro j _
  fin_cases j
  · refine ⟨asg true true, 0, 1, by decide, ?_⟩
    rw [skel_gap]
    norm_num [g, asg, binaryState, lam, Function.update]
  · refine ⟨asg true true, 0, 1, by decide, ?_⟩
    rw [skel_gap]
    norm_num [g, asg, binaryState, lam, Function.update]

/-- The margin lies in `(0, ½)`, where the class is defined.-/
public theorem lam_valid : Skeleton.ValidMargin lam := by
  constructor <;> norm_num [lam]

/-- **(M1)** holds for the edgeless model: entries are `1/2` and `4/5`.-/
public theorem edgeless_M1 : Skeleton.M1 edgeless lam := by
  intro c a v
  fin_cases c <;> fin_cases a <;> constructor <;>
    norm_num [edgeless, bernoulli, lam]

/-- **(M4)** holds vacuously for the edgeless model: it has no edges.-/
public theorem edgeless_M4 : Skeleton.M4 edgeless lam := by
  intro c p hp
  simp [edgeless] at hp

/-- **The edgeless model is in the margin class** at `λ = 1/10`.-/
public theorem edgeless_mem : skel.MarginClass edgeless lam :=
  ⟨lam_valid, edgeless_M1, skel_M2, skel_M3, edgeless_M4, skel_M5 _, skel_M6⟩

/-- **(M1)** holds for `X → Y`: entries are `1/2`, `4/5` and `1/5`.-/
public theorem arrowXY_M1 : Skeleton.M1 arrowXY lam := by
  intro c a v
  fin_cases c <;> fin_cases a <;> by_cases hv : v X = 1 <;>
    constructor <;> simp [arrowXY, bernoulli, hv, lam] <;> norm_num

/-- **(M4)** holds for `X → Y`: the single edge has strength `3/5`.-/
public theorem arrowXY_M4 : Skeleton.M4 arrowXY lam := by
  intro c p hp
  fin_cases c
  · simp [arrowXY] at hp
  · have hpX : p = X := by simpa [arrowXY] using hp
    subst p
    refine ⟨asg true true, 0, 1, 1, by decide, ?_⟩
    norm_num [arrowXY, bernoulli, asg, binaryState, lam, Function.update]

/-- **`X → Y` is in the margin class** at `λ = 1/10`.-/
public theorem arrowXY_mem : skel.MarginClass arrowXY lam :=
  ⟨lam_valid, arrowXY_M1, skel_M2, skel_M3, arrowXY_M4, skel_M5 _, skel_M6⟩

/-- **(M1)** holds for `Y → X`: entries are `4/5` and `1/2`.-/
public theorem arrowYX_M1 : Skeleton.M1 arrowYX lam := by
  intro c a v
  fin_cases c <;> fin_cases a <;> by_cases hv : v Y = 1 <;>
    constructor <;> simp [arrowYX, bernoulli, hv, lam] <;> norm_num

/-- **(M4)** holds for `Y → X`: the single edge has strength `3/10`.-/
public theorem arrowYX_M4 : Skeleton.M4 arrowYX lam := by
  intro c p hp
  fin_cases c
  · have hpY : p = Y := by simpa [arrowYX] using hp
    subst p
    refine ⟨asg true true, 0, 1, 1, by decide, ?_⟩
    norm_num [arrowYX, bernoulli, asg, binaryState, lam, Function.update]
  · simp [arrowYX] at hp

/-- **`Y → X` is in the margin class** at `λ = 1/10`.-/
public theorem arrowYX_mem : skel.MarginClass arrowYX lam :=
  ⟨lam_valid, arrowYX_M1, skel_M2, skel_M3, arrowYX_M4, skel_M5 _, skel_M6⟩

/-!
## Graph shape on two variables

The agenda's §5 class `MM₂(λ)` is defined as the models carrying `G→` or `G←`,
so a claim about it needs the graph pinned, not merely non-empty.
-/

/-! ## The counterexample is a family, not a point

`arrowXY` fixes `P(Y=1 ∣ X=0) = 1/5`. Nothing forces that value: the transform
reads only the `(1,1)` cell, and `P(Y=1 ∣ X=0)` never enters it. So the whole
segment of models obtained by varying that one parameter collides with
`edgeless`, and the counterexample is positive-dimensional inside `M(s, λ)`.

This bears on MAIS-O24(c), which asks how large the excluded set is: at this
skeleton it contains a segment, not a tuned point.
-/

/-- `X → Y` with `P(Y=1 ∣ X=0) = b₀` left free. `arrowXY` is `b₀ = 1/5`.-/
@[expose] public def arrowXYb (b0 : ℚ) (hlo : 0 ≤ b0) (hhi : b0 ≤ 1) : Model (Fin 2) where
  dim_pos := by intro c; simp [binaryDim]
  parents := fun c => if c = Y then {X} else ∅
  acyclic := ⟨fun c => if c = Y then 1 else 0, by decide⟩
  cpt := fun c a v ↦ bernoulli
    (if c = X then 1/2 else if v X = 1 then 4/5 else b0) a
  cpt_parents := by
    intro c a v w h
    fin_cases c
    · simp
    · have hX : v X = w X := h X (by simp)
      simp [hX]
  cpt_nonneg := by
    intro c a v
    fin_cases a <;> simp [bernoulli] <;> split_ifs <;> norm_num <;> linarith
  cpt_sum := by
    intro c v
    rw [Fin.sum_univ_two]
    simp [bernoulli]

/-! ## The relation has teeth

A collision theorem says nothing unless models of the class can *fail* to
collide. `transform_identity_edgeless` rules out one degeneracy — both
transforms identically zero — but not the one that would empty the headline:
`BehaviorEq` holding of every pair.
-/

/-- The edgeless model with `P(X=1) = 1/5` instead of `1/2`. Still in the margin
class; behaviorally distinguishable from `edgeless`.-/
@[expose] public def other : Model (Fin 2) where
  dim_pos := by intro c; simp [binaryDim]
  parents := fun _ => ∅
  acyclic := ⟨fun _ => 0, by intro c p hp; simp at hp⟩
  cpt := fun c a _ ↦ bernoulli (if c = X then 1/5 else 4/5) a
  cpt_parents := by intro c a v w _; rfl
  cpt_nonneg := by
    intro c a v
    fin_cases a <;> simp [bernoulli] <;> split_ifs <;> norm_num
  cpt_sum := by
    intro c v
    rw [Fin.sum_univ_two]
    simp [bernoulli]

/-!
## The answer to MAIS-O23

Two distinct models of the margin class with one behavior.
-/

/-! ## The witness satisfies `def:margin` as printed

`Skeleton.marginClass_iff_printed` proves the categorical six conditions collapse
to `def:margin`'s printed binary ones. Running it on the witness turns that from
a general claim into a checked one on the object MAIS-O23 is answered with: the
model this collision is built from is in the printed class, not merely in an
atlas class that resembles it.

The printed form is worth reading off. `PrintedM1` constrains `P(Cᵢ = 1 | pa)`,
which is what a binary table stores; `PrintedM4` compares the two parent
configurations that differ in the edge's source, at the child's `1`-cell; and
`PrintedM5` is `Anc(U) = 𝐂` together with `𝐎 ⊊ 𝐂`, with `Anc(U)` taken over
`𝐙 ∪ 𝐎` because `def:cid` gives `U` the parents `{D} ∪ 𝐙` and `D` the parents
`𝐎`. -/

end AISafetyAtlas.Examples.Causal
