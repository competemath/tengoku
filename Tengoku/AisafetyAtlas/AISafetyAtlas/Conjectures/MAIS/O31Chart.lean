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
# MAIS-O31 — the binary-chain chart and its transport

The `2n+1`-coordinate chart, its embedding into the causal kernel, and the
threshold machinery. **The bridge runs both ways.**
`toModel_marginClass` carries chart objects into the printed class, and
`exists_O31ChainModel_toModel_eq` carries every printed model with the chain
graph back to a valid chart point, with `toModel_injective` naming none twice.

A one-directional bridge suffices for counterexamples and not for an
identification claim, and the difference is the direction asymmetry rather than a
matter of taste: an existence claim only gets
harder in a larger comparison class, so a chart witness settles it for
`𝕄(sk, λ)` outright, while a uniqueness or singleton-fibre claim gets *easier*
as the class shrinks and would have asserted something weaker than print.

`O31.lean` crosses the bridge: `o31IdentifiesCoordinate_iff_class` and
`o31IdentifiesNodeMass_iff_class` state the two identification predicates against
every model of `𝕄(sk, λ)` carrying the chain graph, which is the comparison class
`q:chain` names in its own parentheses.

Stated at the MAIS revision pinned in `docs/provenance/mais-source-pin.md`.
Defining a proposition asserts nothing about its truth; resolutions live in
`AISafetyAtlas/Examples/Conjectures/`.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.BinaryPair

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
variable {dim : C → ℕ}

/-! ## MAIS-O31: one intervenable variable in a real binary chain -/

/-- The `2n+1` real coordinates of a chain with `n+1` nodes.

Node `0` is the guessed endpoint and node `n` is the root. `transition i x`
is `P(C_i=1 | C_{i+1}=x)`.-/
@[ext] public structure O31ChainModel (n : ℕ) where
  root : ℝ
  transition : Fin n → Fin 2 → ℝ

/-- The source's probability and edge-strength margins on a chain chart.-/
@[expose] public def O31ChainModel.Valid {n : ℕ} (lam : ℝ) (M : O31ChainModel n) : Prop :=
  0 < lam ∧ lam < 1 / 2 ∧ InMarginInterval lam M.root ∧
    (∀ i x, InMarginInterval lam (M.transition i x)) ∧
    ∀ i, lam ≤ |M.transition i 1 - M.transition i 0|

/-- A local-intervention profile on the `n+1` chain nodes.-/
public abbrev O31Profile (n : ℕ) := Fin (n + 1) → (Fin 2 → Fin 2)

/-- The Bernoulli success parameter at one chain node, before intervention.-/
@[expose] public noncomputable def O31ChainModel.nodeParameter {n : ℕ} (M : O31ChainModel n)
    (v : Fin (n + 1) → Fin 2) (c : Fin (n + 1)) : ℝ :=
  Fin.lastCases M.root (fun i ↦ M.transition i (v i.succ)) c

/-- The directed-path graph carried by `O31ChainModel`: node `n` is the root
and every node `i < n` has the single parent `i+1`.-/
@[expose] public def o31ChainParents {n : ℕ} : Fin (n + 1) → Finset (Fin (n + 1)) :=
  fun c ↦ Fin.lastCases ∅ (fun i ↦ {i.succ}) c

/-- The table bounds needed to construct a kernel model from the chain chart.-/
@[expose] public def O31ChainModel.InUnitBox {n : ℕ} (M : O31ChainModel n) : Prop :=
  (0 ≤ M.root ∧ M.root ≤ 1) ∧ ∀ i x, 0 ≤ M.transition i x ∧ M.transition i x ≤ 1

public theorem O31ChainModel.inUnitBox_of_valid {n : ℕ} {lam : ℝ}
    {M : O31ChainModel n} (hM : M.Valid lam) : M.InUnitBox := by
  refine ⟨⟨by linarith [hM.1, hM.2.2.1.1], by linarith [hM.1, hM.2.2.1.2]⟩,
    fun i x ↦ ⟨by linarith [hM.1, (hM.2.2.2.1 i x).1],
      by linarith [hM.1, (hM.2.2.2.1 i x).2]⟩⟩

public theorem O31ChainModel.nodeParameter_mem_unitInterval {n : ℕ}
    {M : O31ChainModel n} (hM : M.InUnitBox) (v : Fin (n + 1) → Fin 2)
    (c : Fin (n + 1)) : 0 ≤ M.nodeParameter v c ∧ M.nodeParameter v c ≤ 1 := by
  induction c using Fin.lastCases with
  | last => simpa [O31ChainModel.nodeParameter] using hM.1
  | cast i => simpa [O31ChainModel.nodeParameter] using hM.2 i (v i.succ)

/-- The chain chart embedded in the causal-model kernel.-/
@[expose] public noncomputable def O31ChainModel.toModel {n : ℕ} (M : O31ChainModel n)
    (hM : M.InUnitBox) : Model (Fin (n + 1)) (binaryDim (Fin (n + 1))) ℝ where
  dim_pos := fun _ ↦ by norm_num
  parents := o31ChainParents
  acyclic := by
    refine ⟨fun c ↦ n - c.val, fun c p hp ↦ ?_⟩
    induction c using Fin.lastCases with
    | last => simp [o31ChainParents] at hp
    | cast i =>
        have hpi : p = i.succ := by simpa [o31ChainParents] using hp
        subst p
        change n - (i.val + 1) < n - i.val
        omega
  cpt := fun c a v ↦ bernoulli (M.nodeParameter v c) a
  cpt_parents := by
    intro c a v w hvw
    induction c using Fin.lastCases with
    | last => simp [O31ChainModel.nodeParameter]
    | cast i =>
        have hparent : v i.succ = w i.succ := hvw i.succ (by simp [o31ChainParents])
        simp [O31ChainModel.nodeParameter, hparent]
  cpt_nonneg := by
    intro c a v
    have hp := M.nodeParameter_mem_unitInterval hM v c
    fin_cases a <;> simp [bernoulli] <;> linarith
  cpt_sum := by
    intro c v
    simp [bernoulli, Fin.sum_univ_two]

/-- The interventional chain joint, using the same local-map semantics as the causal kernel.-/
@[expose] public noncomputable def O31ChainModel.jointProb {n : ℕ} (M : O31ChainModel n)
    (profile : O31Profile n) (v : Fin (n + 1) → Fin 2) : ℝ :=
  ∏ c : Fin (n + 1), interventionFactor (M.nodeParameter v c) (profile c) (v c)

/-- The probability that the guessed endpoint `C₁` equals one.-/
@[expose] public noncomputable def O31ChainModel.targetProbability {n : ℕ}
    (M : O31ChainModel n) (profile : O31Profile n) : ℝ :=
  ∑ v : Fin (n + 1) → Fin 2, if v 0 = 1 then M.jointProb profile v else 0

/-- The chain factor is literally the causal kernel's local-intervention factor.-/
public theorem O31ChainModel.factor_toModel {n : ℕ} (M : O31ChainModel n)
    (hM : M.InUnitBox) (profile : O31Profile n) (v : Fin (n + 1) → Fin 2)
    (c : Fin (n + 1)) :
    (M.toModel hM).factor profile v c =
      interventionFactor (M.nodeParameter v c) (profile c) (v c) := rfl

/-- The chart and causal-kernel interventional joints agree pointwise.-/
public theorem O31ChainModel.jointProb_toModel {n : ℕ} (M : O31ChainModel n)
    (hM : M.InUnitBox) (profile : O31Profile n) (v : Fin (n + 1) → Fin 2) :
    (M.toModel hM).jointProb profile v = M.jointProb profile v := rfl

/-- The chart endpoint marginal is the corresponding causal-kernel marginal.-/
public theorem O31ChainModel.targetProbability_toModel {n : ℕ} (M : O31ChainModel n)
    (hM : M.InUnitBox) (profile : O31Profile n) :
    M.targetProbability profile =
      ∑ v : Assignment (Fin (n + 1)) (binaryDim (Fin (n + 1))),
        if v 0 = 1 then (M.toModel hM).jointProb profile v else 0 := by
  simp only [O31ChainModel.targetProbability, M.jointProb_toModel hM]

/-- The profile that changes only node `j` by the local state map `f`.-/
@[expose] public def o31SingleNodeProfile {n : ℕ} (j : Fin (n + 1))
    (f : Fin 2 → Fin 2) : O31Profile n :=
  fun c ↦ if c = j then f else id

/-- A real probability mixture over the four local maps on one binary node.-/
public structure O31LocalMixture where
  weight : (Fin 2 → Fin 2) → ℝ
  nonneg : ∀ f, 0 ≤ weight f
  sum_one : ∑ f, weight f = 1

/-- Expected endpoint probability under a mixture of interventions at `j`.

Exposed for the same reason `O31ChainModel.targetProbability` is: `O31BehaviorEqAt` is stated over this, so a consumer that cannot unfold it cannot reason about behavioural equality at all.-/
@[expose] public noncomputable def O31ChainModel.mixedTargetProbability {n : ℕ}
    (M : O31ChainModel n) (j : Fin (n + 1)) (mix : O31LocalMixture) : ℝ :=
  ∑ f : Fin 2 → Fin 2, mix.weight f * M.targetProbability (o31SingleNodeProfile j f)

/-- The endpoint marginal computed from the embedded causal-kernel model.-/
@[expose] public noncomputable def O31ChainModel.kernelTargetProbability {n : ℕ}
    (M : O31ChainModel n) (hM : M.InUnitBox) (profile : O31Profile n) : ℝ :=
  ∑ v : Assignment (Fin (n + 1)) (binaryDim (Fin (n + 1))),
    if v 0 = 1 then (M.toModel hM).jointProb profile v else 0

public theorem O31ChainModel.kernelTargetProbability_eq {n : ℕ}
    (M : O31ChainModel n) (hM : M.InUnitBox) (profile : O31Profile n) :
    M.kernelTargetProbability hM profile = M.targetProbability profile := by
  symm
  exact M.targetProbability_toModel hM profile

/-- The mixed endpoint marginal computed wholly through the causal kernel.-/
@[expose] public noncomputable def O31ChainModel.kernelMixedTargetProbability {n : ℕ}
    (M : O31ChainModel n) (hM : M.InUnitBox) (j : Fin (n + 1))
    (mix : O31LocalMixture) : ℝ :=
  ∑ f : Fin 2 → Fin 2,
    mix.weight f * M.kernelTargetProbability hM (o31SingleNodeProfile j f)

public theorem O31ChainModel.kernelMixedTargetProbability_eq {n : ℕ}
    (M : O31ChainModel n) (hM : M.InUnitBox) (j : Fin (n + 1))
    (mix : O31LocalMixture) :
    M.kernelMixedTargetProbability hM j mix = M.mixedTargetProbability j mix := by
  simp [O31ChainModel.kernelMixedTargetProbability,
    O31ChainModel.mixedTargetProbability, M.kernelTargetProbability_eq hM]

/-- Two binary tasks share at least one optimal action distribution.

At a tie either endpoint action may be shared. This is the existential
policy-family quantifier used by the identified set, not equality of the two
complete optimizer sets.-/
@[expose] public def ShareBinaryOptimum (x y : ℝ) : Prop :=
  (0 ≤ x ∧ 0 ≤ y) ∨ (x ≤ 0 ∧ y ≤ 0)

/-- A binary action is optimal when the advantage of `true` over `false` has
the corresponding sign; ties make both actions optimal.-/
@[expose] public def BinaryOptimalAction (advantage : ℝ) (d : Bool) : Prop :=
  if d then 0 ≤ advantage else advantage ≤ 0

/-- Equality of all optimal-policy information obtainable by intervening only at `j`.

The threshold `t` is the unique endpoint probability at which guessing zero
and guessing one have equal expected utility.-/
@[expose] public noncomputable def O31BehaviorEqAt {n : ℕ} (t : ℝ) (j : Fin (n + 1))
    (M M' : O31ChainModel n) : Prop :=
  ∀ mix : O31LocalMixture,
    ShareBinaryOptimum (M.mixedTargetProbability j mix - t)
      (M'.mixedTargetProbability j mix - t)

/-- The same restricted behavioral comparison, now computed from two actual
causal-kernel models.-/
@[expose] public noncomputable def O31KernelBehaviorEqAt {n : ℕ} (t : ℝ)
    (j : Fin (n + 1)) (M M' : O31ChainModel n) (hM : M.InUnitBox)
    (hM' : M'.InUnitBox) : Prop :=
  ∀ mix : O31LocalMixture,
    ShareBinaryOptimum (M.kernelMixedTargetProbability hM j mix - t)
      (M'.kernelMixedTargetProbability hM' j mix - t)

/-- Chart behavior is exactly restricted behavior of the embedded kernel
models, for every threshold and every local intervention mixture.-/
public theorem o31BehaviorEqAt_iff_kernel {n : ℕ} (t : ℝ) (j : Fin (n + 1))
    (M M' : O31ChainModel n) (hM : M.InUnitBox) (hM' : M'.InUnitBox) :
    O31BehaviorEqAt t j M M' ↔ O31KernelBehaviorEqAt t j M M' hM hM' := by
  simp [O31BehaviorEqAt, O31KernelBehaviorEqAt,
    M.kernelMixedTargetProbability_eq hM, M'.kernelMixedTargetProbability_eq hM']

/-- The utility MAIS-O31 quantifies over, as its gap at the single utility
parent `𝐙 = {C₁}`.

`q:chain` says "`u` with margin (M2)–(M3)". With one binary utility parent the
gap `g(z) = u(1,z) - u(0,z)` is two numbers: (M3) makes them opposite in sign,
(M2) bounds each by the margin, and `u`-values in `[0,1]` bound each by one.

**Which slot carries the positive sign is not fixed by print.** (M3) reads
"there exist `z⁺, z⁻` … with `g(z⁺) > 0 > g(z⁻)`" — an existential over the
slice, so `g(0) > 0 > g(1)` satisfies it exactly as `g(0) < 0 < g(1)` does. Hard-coding
the second would exclude half of the legal utilities; `g₀ * g₁ < 0` is the printed
condition and nothing more.

Widening it costs nothing downstream, and the reason is worth recording:
`ShareBinaryOptimum` is invariant under negating both of its arguments, and the
advantage is `(1 - p) g₀ + p g₁ = (g₁ - g₀) (p - t)`. Reversing the sign order
scales every compared advantage by one negative constant, so which action is
optimal flips but *whether two models agree* does not. The threshold stays in
`(0, 1)` either way.-/
@[expose] public def O31UtilityGap (lam g₀ g₁ : ℝ) : Prop :=
  -1 ≤ g₀ ∧ g₀ ≤ 1 ∧ -1 ≤ g₁ ∧ g₁ ≤ 1 ∧ g₀ * g₁ < 0 ∧ lam ≤ |g₀| ∧ lam ≤ |g₁|

/-- The endpoint utility gap named by `q:chain`, read from the state of `C₁`.-/
@[expose] public noncomputable def o31EndpointGap {n : ℕ} (g₀ g₁ : ℝ)
    (v : Assignment (Fin (n + 1)) (binaryDim (Fin (n + 1)))) : ℝ :=
  if v 0 = 0 then g₀ else g₁

private theorem fin_two_eq_zero_or_one (x : Fin 2) : x = 0 ∨ x = 1 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    apply Fin.ext
    have hxval : x.val ≠ 0 := by
      intro hzero
      exact hx (Fin.ext hzero)
    have hlt := x.isLt
    simp only [Fin.val_one]
    omega

/-- A normalized binary utility whose gap is `o31EndpointGap`.-/
@[expose] public noncomputable def o31GapUtility {n : ℕ} (g₀ g₁ : ℝ)
    (d : Bool) (v : Assignment (Fin (n + 1)) (binaryDim (Fin (n + 1)))) : ℝ :=
  if d then (1 + o31EndpointGap g₀ g₁ v) / 2
  else (1 - o31EndpointGap g₀ g₁ v) / 2

/-- The printed chain skeleton for a margin-admissible endpoint utility.-/
@[expose] public noncomputable def o31Skeleton {n : ℕ} {lam g₀ g₁ : ℝ}
    (hg : O31UtilityGap lam g₀ g₁) :
    Skeleton (Fin (n + 1)) (binaryDim (Fin (n + 1))) Bool ℝ where
  observed := ∅
  utilityParents := {0}
  utility := o31GapUtility g₀ g₁
  utility_parents := by
    intro d v w h
    have hzero : v 0 = w 0 := h 0 (by simp)
    simp [o31GapUtility, o31EndpointGap, hzero]
  utility_mem_unitInterval := by
    intro d v
    by_cases hv : v 0 = 0
    · cases d <;> simp [o31GapUtility, o31EndpointGap, hv] <;> constructor <;> linarith [hg.1, hg.2.1]
    · have hv1 : v 0 = 1 := by
        let x : Fin 2 := v 0
        have hx : x ≠ 0 := by simpa [x] using hv
        have hx1 : x = 1 := by
          apply Fin.ext
          have hxlt := x.isLt
          simp only [Fin.val_one]
          omega
        simpa [x] using hx1
      cases d <;> simp [o31GapUtility, o31EndpointGap, hv1] <;> constructor <;>
        linarith [hg.2.2.1, hg.2.2.2.1]

@[simp] public theorem o31Skeleton_observed {n : ℕ} {lam g₀ g₁ : ℝ}
    (hg : O31UtilityGap lam g₀ g₁) : (o31Skeleton (n := n) hg).observed = ∅ := rfl

@[simp] public theorem o31Skeleton_utilityParents {n : ℕ} {lam g₀ g₁ : ℝ}
    (hg : O31UtilityGap lam g₀ g₁) :
    (o31Skeleton (n := n) hg).utilityParents = {0} := rfl

/-- The normalized skeleton realizes exactly the supplied endpoint gap.-/
public theorem o31Skeleton_gap {n : ℕ} {lam g₀ g₁ : ℝ}
    (hg : O31UtilityGap lam g₀ g₁) :
    (o31Skeleton (n := n) hg).gap = o31EndpointGap g₀ g₁ := by
  funext v
  simp [Skeleton.gap, o31Skeleton, o31GapUtility]
  ring

/-- Every chain Bernoulli parameter lies in the printed margin interval.-/
public theorem O31ChainModel.nodeParameter_mem_marginInterval {n : ℕ} {lam : ℝ}
    {M : O31ChainModel n} (hM : M.Valid lam) (v : Fin (n + 1) → Fin 2)
    (c : Fin (n + 1)) : InMarginInterval lam (M.nodeParameter v c) := by
  induction c using Fin.lastCases with
  | last => simpa [O31ChainModel.nodeParameter] using hM.2.2.1
  | cast i => simpa [O31ChainModel.nodeParameter] using hM.2.2.2.1 i (v i.succ)

public theorem O31ChainModel.toModel_printedM1 {n : ℕ} {lam : ℝ}
    {M : O31ChainModel n} (hM : M.Valid lam) :
    Skeleton.PrintedM1 (M.toModel (M.inUnitBox_of_valid hM)) lam := by
  intro c v
  simpa [O31ChainModel.toModel, bernoulli, InMarginInterval] using
    M.nodeParameter_mem_marginInterval hM v c

public theorem O31ChainModel.toModel_printedM4 {n : ℕ} {lam : ℝ}
    {M : O31ChainModel n} (hM : M.Valid lam) :
    Skeleton.PrintedM4 (M.toModel (M.inUnitBox_of_valid hM)) lam := by
  intro c p hp
  induction c using Fin.lastCases with
  | last => simp [O31ChainModel.toModel, o31ChainParents] at hp
  | cast i =>
      have hp' : p = i.succ := by
        simpa [O31ChainModel.toModel, o31ChainParents] using hp
      subst p
      refine ⟨fun _ ↦ 0, ?_⟩
      simpa [O31ChainModel.toModel, O31ChainModel.nodeParameter, bernoulli,
        Function.update, abs_sub_comm] using hM.2.2.2.2 i

public theorem o31Skeleton_m2 {n : ℕ} {lam g₀ g₁ : ℝ}
    (hg : O31UtilityGap lam g₀ g₁) : (o31Skeleton (n := n) hg).M2 lam := by
  intro v
  rw [o31Skeleton_gap]
  by_cases hv : v 0 = 0
  · simpa [o31EndpointGap, hv] using hg.2.2.2.2.2.1
  · simpa [o31EndpointGap, hv] using hg.2.2.2.2.2.2

public theorem o31Skeleton_m3 {n : ℕ} {lam g₀ g₁ : ℝ}
    (hg : O31UtilityGap lam g₀ g₁) : (o31Skeleton (n := n) hg).M3 := by
  rcases mul_neg_iff.mp hg.2.2.2.2.1 with ⟨hg₀, hg₁⟩ | ⟨hg₀, hg₁⟩
  · intro w
    refine ⟨fun _ ↦ 0, fun _ ↦ 1, ?_, ?_, ?_, ?_⟩
    · simp [o31Skeleton]
    · simp [o31Skeleton]
    · simpa [o31Skeleton_gap, o31EndpointGap] using hg₀
    · simpa [o31Skeleton_gap, o31EndpointGap] using hg₁
  · intro w
    refine ⟨fun _ ↦ 1, fun _ ↦ 0, ?_, ?_, ?_, ?_⟩
    · simp [o31Skeleton]
    · simp [o31Skeleton]
    · simpa [o31Skeleton_gap, o31EndpointGap] using hg₁
    · simpa [o31Skeleton_gap, o31EndpointGap] using hg₀

public theorem o31Skeleton_m6 {n : ℕ} {lam g₀ g₁ : ℝ}
    (hg : O31UtilityGap lam g₀ g₁) : (o31Skeleton (n := n) hg).M6 lam := by
  intro j hj
  have hj0 : j = 0 := by simpa [o31Skeleton] using hj
  subst j
  refine ⟨fun _ ↦ 0, 0, 1, by norm_num [binaryDim], ?_⟩
  rw [o31Skeleton_gap]
  change lam ≤ |g₀ - g₁|
  rcases mul_neg_iff.mp hg.2.2.2.2.1 with ⟨hg₀, hg₁⟩ | ⟨hg₀, hg₁⟩
  · rw [abs_of_pos (by linarith)]
    have hm := hg.2.2.2.2.2.1
    rw [abs_of_pos hg₀] at hm
    linarith
  · rw [abs_of_neg (by linarith)]
    have hm := hg.2.2.2.2.2.2
    rw [abs_of_pos hg₁] at hm
    linarith

public theorem O31ChainModel.o31Skeleton_printedM5 {n : ℕ} {lam g₀ g₁ : ℝ}
    (hg : O31UtilityGap lam g₀ g₁) {M : O31ChainModel n} (hM : M.Valid lam) :
    (o31Skeleton (n := n) hg).PrintedM5 (M.toModel (M.inUnitBox_of_valid hM)) := by
  constructor
  · rw [Model.ancestors_eq_univ_iff]
    intro t ht hclosed
    have hzero : (0 : Fin (n + 1)) ∈ t := ht (by simp [o31Skeleton])
    have hstep : ∀ i : Fin n, i.castSucc ∈ t → i.succ ∈ t := by
      intro i hi
      exact hclosed i.castSucc hi i.succ (by simp [O31ChainModel.toModel, o31ChainParents])
    apply Finset.eq_univ_of_forall
    intro c
    have hall : ∀ k : ℕ, ∀ hk : k < n + 1, (⟨k, hk⟩ : Fin (n + 1)) ∈ t := by
      intro k
      induction k with
      | zero => intro _; simpa using hzero
      | succ k ih =>
          intro hk
          have hik : k < n + 1 := by omega
          have hkn : k < n := by omega
          exact hstep ⟨k, hkn⟩ (ih hik)
    exact hall c.val c.isLt
  · simp [o31Skeleton]

/-- Every valid chain chart and legal endpoint utility instantiate the printed
margin class in the causal kernel.-/
public theorem O31ChainModel.toModel_marginClass {n : ℕ} {lam g₀ g₁ : ℝ}
    (hg : O31UtilityGap lam g₀ g₁) {M : O31ChainModel n} (hM : M.Valid lam) :
    (o31Skeleton (n := n) hg).MarginClass (M.toModel (M.inUnitBox_of_valid hM)) lam := by
  rw [Skeleton.marginClass_iff_printed]
  exact ⟨⟨hM.1, hM.2.1⟩, M.toModel_printedM1 hM, o31Skeleton_m2 hg,
    o31Skeleton_m3 hg, M.toModel_printedM4 hM, M.o31Skeleton_printedM5 hg hM,
    o31Skeleton_m6 hg⟩

/-! ## The chart is onto the printed chain family

The bridge above carries chart points into `𝕄(sk, λ)`. Nothing so far carried
printed models back, and the module header records why that mattered: an
existence claim only gets harder in a larger class, so a chart witness settles a
counterexample outright, while an identification claim proved over chart points
alone would be **weaker** than print, since collisions are easier to rule out in
a smaller comparison class.

`ofModel` reads a printed model's own tables as chart coordinates and
`toModel_ofModel` shows that reading loses nothing, so the two comparison
classes coincide and the direction asymmetry stops mattering. This is the chain
analogue of `BinaryPair.exists_pairModel_toModel_eq`, which does the same job for
`def:twovar`'s two-variable family. -/

/-- The chart coordinates a printed chain model carries in its own tables.

The root cell is read at the all-zero configuration and each transition cell at
the configuration that sets its single parent; `cpt_parents` makes both readings
independent of the coordinates the cell does not depend on.-/
@[expose] public noncomputable def O31ChainModel.ofModel {n : ℕ}
    (N : Model (Fin (n + 1)) (binaryDim (Fin (n + 1))) ℝ) : O31ChainModel n where
  root := N.cpt (Fin.last n) 1 (fun _ ↦ 0)
  transition := fun i x ↦
    N.cpt i.castSucc 1 (Function.update (fun _ ↦ (0 : Fin 2)) i.succ x)

private theorem o31_cpt_zero_eq {n : ℕ}
    {N : Model (Fin (n + 1)) (binaryDim (Fin (n + 1))) ℝ}
    (c : Fin (n + 1)) (v : Fin (n + 1) → Fin 2) : N.cpt c 0 v = 1 - N.cpt c 1 v := by
  have hsum := N.cpt_sum c v
  rw [Fin.sum_univ_two] at hsum
  linarith

/-- The root cell reads no coordinate: `o31ChainParents` gives the last node no
parents.-/
private theorem o31_cpt_root_congr {n : ℕ}
    {N : Model (Fin (n + 1)) (binaryDim (Fin (n + 1))) ℝ}
    (hp : N.parents = o31ChainParents) (a : Fin 2) (v w : Fin (n + 1) → Fin 2) :
    N.cpt (Fin.last n) a v = N.cpt (Fin.last n) a w := by
  refine N.cpt_parents _ _ _ _ ?_
  intro p hmem
  rw [hp] at hmem
  simp [o31ChainParents] at hmem

/-- A transition cell reads exactly its own successor coordinate.-/
private theorem o31_cpt_child_congr {n : ℕ}
    {N : Model (Fin (n + 1)) (binaryDim (Fin (n + 1))) ℝ}
    (hp : N.parents = o31ChainParents) (i : Fin n) (a : Fin 2)
    (v w : Fin (n + 1) → Fin 2) (hvw : v i.succ = w i.succ) :
    N.cpt i.castSucc a v = N.cpt i.castSucc a w := by
  refine N.cpt_parents _ _ _ _ ?_
  intro p hmem
  rw [hp] at hmem
  simp only [o31ChainParents, Fin.lastCases_castSucc, Finset.mem_singleton] at hmem
  subst hmem
  exact hvw

/-- The chart coordinates read off a printed chain model satisfy the printed
margins: `(M1)` gives every interval and `(M4)` the edge strength.-/
public theorem O31ChainModel.ofModel_valid {n : ℕ} {lam g₀ g₁ : ℝ}
    (hg : O31UtilityGap lam g₀ g₁)
    {N : Model (Fin (n + 1)) (binaryDim (Fin (n + 1))) ℝ}
    (hN : (o31Skeleton (n := n) hg).MarginClass N lam)
    (hp : N.parents = o31ChainParents) :
    (O31ChainModel.ofModel N).Valid lam := by
  rw [Skeleton.marginClass_iff_printed] at hN
  obtain ⟨⟨hlam0, hlam2⟩, hm1, -, -, hm4, -, -⟩ := hN
  refine ⟨hlam0, hlam2, hm1 _ _, fun i x ↦ hm1 _ _, fun i ↦ ?_⟩
  have hmem : i.succ ∈ N.parents i.castSucc := by
    rw [hp]
    simp [o31ChainParents]
  obtain ⟨w, hw⟩ := hm4 i.castSucc i.succ hmem
  have htrans : ∀ x : Fin 2, (O31ChainModel.ofModel N).transition i x
      = N.cpt i.castSucc 1 (Function.update w i.succ x) := by
    intro x
    show N.cpt i.castSucc 1 (Function.update (fun _ ↦ (0 : Fin 2)) i.succ x) = _
    exact o31_cpt_child_congr hp i 1 _ _ (by simp)
  rw [htrans 1, htrans 0, abs_sub_comm]
  exact hw

/-- `ofModel` is a left inverse of `toModel`, so the chart is injective too.-/
public theorem O31ChainModel.ofModel_toModel {n : ℕ} (M : O31ChainModel n)
    (h : M.InUnitBox) : O31ChainModel.ofModel (M.toModel h) = M := by
  refine O31ChainModel.ext ?_ (funext fun i ↦ funext fun x ↦ ?_)
  · show bernoulli (M.nodeParameter (fun _ ↦ 0) (Fin.last n)) 1 = M.root
    simp [bernoulli, O31ChainModel.nodeParameter]
  · show bernoulli (M.nodeParameter
      (Function.update (fun _ ↦ (0 : Fin 2)) i.succ x) i.castSucc) 1
        = M.transition i x
    simp [bernoulli, O31ChainModel.nodeParameter]

/-- The decision threshold such a utility induces: the endpoint probability at
which guessing zero and guessing one have equal expected utility.

MAIS issue #8 writes "let `t ∈ (0,1)` be the utility decision threshold" and
does not say which `t` a utility produces. Solving
`(1 - p)·g₀ + p·g₁ = 0` supplies it, so the statement quantifies over the
utility `q:chain` names and *derives* `t`, rather than positing a threshold
the source leaves unexplained.-/
@[expose] public noncomputable def o31Threshold (g₀ g₁ : ℝ) : ℝ := -g₀ / (g₁ - g₀)

/-- The actual expected utility gap under the local intervention mixture.-/
@[expose] public noncomputable def O31ChainModel.kernelMixedUtilityGap {n : ℕ}
    {lam g₀ g₁ : ℝ} (hg : O31UtilityGap lam g₀ g₁) (M : O31ChainModel n)
    (hM : M.InUnitBox) (j : Fin (n + 1)) (mix : O31LocalMixture) : ℝ :=
  ∑ f : Fin 2 → Fin 2, mix.weight f *
    (M.toModel hM).Δ (o31Skeleton (n := n) hg).gap (o31SingleNodeProfile j f)

/-- Restricted shared-optimum behavior computed from the actual normalized
utility and the two embedded causal-kernel models.-/
@[expose] public noncomputable def O31UtilityKernelBehaviorEq {n : ℕ}
    {lam g₀ g₁ : ℝ} (hg : O31UtilityGap lam g₀ g₁) (j : Fin (n + 1))
    (M M' : O31ChainModel n) (hM : M.InUnitBox) (hM' : M'.InUnitBox) : Prop :=
  ∀ mix : O31LocalMixture,
    ShareBinaryOptimum (M.kernelMixedUtilityGap hg hM j mix)
      (M'.kernelMixedUtilityGap hg hM' j mix)

end AISafetyAtlas.Conjectures.MAIS
