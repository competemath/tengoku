module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Causal.MarginClass
public import Tengoku.Seed.Algebra.Order.GroupWithZero.Finset
public import Tengoku.Seed.Order.Bounds.Basic
public import Tengoku.Seed.Tactic.Linarith
public import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite unmediated decision tasks

This is the Assumption 1 projection of a finite single-decision CID. The chance
joint is independent of the decision, a policy is a distribution on an arbitrary
finite decision alphabet conditional on visible chance variables, and value is
the resulting expected utility.

## Grounding and non-claims

* `Policy`, `value`, `regret` and the query packaging carry the value field `𝕜` as a
  parameter, so probability mixtures are the RE24 Definition-3 simplex over whichever
  field a statement picks, and the printed real case is an instance rather than an
  extrapolation.
* Policies and expected utility are the unmediated projection of RE24 Section
  2.2. RE24 Definition 4 and Everitt et al. 2021 Definition 4 are mediated CIDs,
  so they motivate this projection but are not its literal definition.
* `HasRegretAtMost` is the regret inequality used in the A2 query model and the
  RE24 main text. RE24 Definition 5 packages the policy oracle, not this inequality.
  Zero-regret fibrewise optimality is proved below; it is not stored in the definition.
* `gap`, `signPolicy`, and `value_const_sub` are binary-decision corollaries.
  Appendix B equation (3) is one hard-intervention instance, not their definition.
* `InIdentifiedSet`, `modelError`, and `IsRadius` remain A2 query packaging.
  They are related to RE24 Theorem 2, but are not its recovered `G' ⊆ G` or
  its function `γ(δ)`.
* Decision and utility are not DAG vertices here. Mediated tasks require a full
  CID layer and are outside this handoff.
-/

namespace AISafetyAtlas.Causal

variable {C : Type*} [Fintype C] [DecidableEq C]
variable {dim : C → ℕ}
variable {Decision : Type*} [Fintype Decision] [DecidableEq Decision]
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ## Policies -/

/-- A stochastic decision rule on a finite decision alphabet.-/
public structure Policy {C : Type*} [Fintype C] [DecidableEq C]
    {dim : C → ℕ} (visible : Finset C) (Decision : Type*)
    [Fintype Decision] [DecidableEq Decision]
    (𝕜 : Type*) [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] where
  /-- Conditional decision probabilities.-/
  prob : Assignment C dim → Decision → 𝕜
  /-- Policy probabilities are nonnegative.-/
  prob_nonneg : ∀ v d, 0 ≤ prob v d
  /-- Each conditional decision distribution sums to one.-/
  prob_sum : ∀ v, ∑ d : Decision, prob v d = 1
  /-- The policy reads only the visible variables.-/
  prob_parents :
    ∀ v w d, (∀ c ∈ visible, v c = w c) → prob v d = prob w d

/-- Two policies are equal when their probability kernels are equal.-/
@[ext] public theorem Policy.ext {visible : Finset C}
    {π π' : Policy (dim := dim) visible Decision 𝕜} (h : π.prob = π'.prob) : π = π' := by
  cases π
  cases π'
  cases h
  rfl

/-- The deterministic constant policy `do(D=d)`.-/
public def Policy.const (visible : Finset C) (d₀ : Decision) :
    Policy (dim := dim) visible Decision 𝕜 where
  prob := fun _ d ↦ if d = d₀ then 1 else 0
  prob_nonneg := by
    intro v d
    split_ifs <;> norm_num
  prob_sum := by
    intro v
    simp
  prob_parents := by
    intro v w d _
    rfl

/-- A canonical full assignment representing a visible fibre.-/
@[expose] public def fibreRep (M : Model C dim 𝕜) (visible : Finset C)
    (v : Assignment C dim) : Assignment C dim :=
  fun c ↦ if _h : c ∈ visible then v c else ⟨0, M.dim_pos c⟩

namespace Model

/-- Expected utility contributed by one visible fibre if decision `d` is chosen.-/
@[expose] public def fibreScore (M : Model C dim 𝕜) (sk : Skeleton C dim Decision 𝕜)
    (visible : Finset C) (w : ProbMixture C dim 𝕜) (r : Assignment C dim)
    (d : Decision) : 𝕜 :=
  ∑ v ∈ Finset.univ.filter (fun v : Assignment C dim ↦
    ∀ c ∈ visible, v c = r c), M.jointProbMix w.1 v * sk.utility d v

/-- Value, written once per visible fibre.-/
@[expose] public def value (M : Model C dim 𝕜) (sk : Skeleton C dim Decision 𝕜)
    (visible : Finset C) (π : Policy (dim := dim) visible Decision 𝕜)
    (w : ProbMixture C dim 𝕜) : 𝕜 :=
  ∑ r ∈ Finset.univ.image (fibreRep M visible),
    ∑ d : Decision, π.prob r d * M.fibreScore sk visible w r d

/-! ## Fibrewise optimum -/

public noncomputable def bestDecision [Nonempty Decision] (M : Model C dim 𝕜)
    (sk : Skeleton C dim Decision 𝕜) (visible : Finset C) (w : ProbMixture C dim 𝕜)
    (r : Assignment C dim) : Decision :=
  Classical.choose
    (Finset.exists_max_image Finset.univ (M.fibreScore sk visible w r)
      Finset.univ_nonempty)

omit [DecidableEq Decision] in
public theorem fibreScore_le_best [Nonempty Decision] (M : Model C dim 𝕜)
    (sk : Skeleton C dim Decision 𝕜) (visible : Finset C) (w : ProbMixture C dim 𝕜)
    (r : Assignment C dim) (d : Decision) :
    M.fibreScore sk visible w r d ≤
      M.fibreScore sk visible w r (M.bestDecision sk visible w r) := by
  exact (Classical.choose_spec
    (Finset.exists_max_image Finset.univ (M.fibreScore sk visible w r)
      Finset.univ_nonempty)).2 d (Finset.mem_univ d)

/-- A deterministic policy choosing a fibrewise maximizer.-/
public noncomputable def bestPolicy [Nonempty Decision] (M : Model C dim 𝕜)
    (sk : Skeleton C dim Decision 𝕜) (visible : Finset C) (w : ProbMixture C dim 𝕜) :
    Policy (dim := dim) visible Decision 𝕜 where
  prob := fun v d ↦
    if d = M.bestDecision sk visible w (fibreRep M visible v) then 1 else 0
  prob_nonneg := by
    intro v d
    split_ifs <;> norm_num
  prob_sum := by
    intro v
    simp
  prob_parents := by
    intro v v' d h
    have hrep : fibreRep M visible v = fibreRep M visible v' := by
      funext c
      by_cases hc : c ∈ visible
      · simp [fibreRep, hc, h c hc]
      · simp [fibreRep, hc]
    rw [hrep]

@[expose] public noncomputable def optimalValue [Nonempty Decision] (M : Model C dim 𝕜)
    (sk : Skeleton C dim Decision 𝕜) (visible : Finset C) (w : ProbMixture C dim 𝕜) : 𝕜 :=
  ∑ r ∈ Finset.univ.image (fibreRep M visible),
    M.fibreScore sk visible w r (M.bestDecision sk visible w r)

@[expose] public noncomputable def regret [Nonempty Decision] (M : Model C dim 𝕜)
    (sk : Skeleton C dim Decision 𝕜) (visible : Finset C)
    (π : Policy (dim := dim) visible Decision 𝕜) (w : ProbMixture C dim 𝕜) : 𝕜 :=
  M.optimalValue sk visible w - M.value sk visible π w

@[expose] public noncomputable def IsOptimal [Nonempty Decision] (M : Model C dim 𝕜)
    (sk : Skeleton C dim Decision 𝕜) (visible : Finset C)
    (π : Policy (dim := dim) visible Decision 𝕜) (w : ProbMixture C dim 𝕜) : Prop :=
  M.regret sk visible π w = 0

/-- The regret inequality used by the A2 query model and the RE24 main text.-/
@[expose] public noncomputable def HasRegretAtMost [Nonempty Decision]
    (M : Model C dim 𝕜) (sk : Skeleton C dim Decision 𝕜) (visible : Finset C)
    (π : Policy (dim := dim) visible Decision 𝕜) (w : ProbMixture C dim 𝕜) (δ : 𝕜) : Prop :=
  M.regret sk visible π w ≤ δ

end Model

/-! ## Binary-decision corollaries -/

namespace Model

/-- The two binary fibre scores differ by exactly the masked gap transform.

This is the fibrewise form of MAIS-A2's decomposition `eq:decomp`, and it is what
makes the behavioral transform carry all behavioral information: anything read
off the *difference* of the two scores — a sign, a regret, a softmax response —
is a function of `Δmask` alone, so two models with equal transforms are
indistinguishable through any of them.-/
public theorem fibreScore_true_sub_false (M : Model C dim 𝕜) (sk : Skeleton C dim Bool 𝕜)
    (visible : Finset C) (w : ProbMixture C dim 𝕜) (r : Assignment C dim) :
    M.fibreScore sk visible w r true - M.fibreScore sk visible w r false =
      M.Δmask sk.gap visible r w := by
  unfold fibreScore Δmask Skeleton.gap
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun v _ ↦ by ring

public def preferredDecision (M : Model C dim 𝕜) (sk : Skeleton C dim Bool 𝕜)
    (visible : Finset C) (w : ProbMixture C dim 𝕜) (v : Assignment C dim) : Bool :=
  decide (0 < M.Δmask sk.gap visible v w)

/-- The binary policy choosing `true` exactly when its fibre gap is positive.-/
@[expose] public def signPolicy (M : Model C dim 𝕜) (sk : Skeleton C dim Bool 𝕜)
    (visible : Finset C) (w : ProbMixture C dim 𝕜) :
    Policy (dim := dim) visible Bool 𝕜 where
  prob := fun v d ↦
    if d = M.preferredDecision sk visible w v then 1 else 0
  prob_nonneg := by
    intro v d
    split_ifs <;> norm_num
  prob_sum := by
    intro v
    rw [Fintype.sum_bool]
    cases M.preferredDecision sk visible w v <;> simp
  prob_parents := by
    intro v v' d h
    have hfilter :
        Finset.univ.filter (fun u : Assignment C dim ↦ ∀ c ∈ visible, u c = v c) =
          Finset.univ.filter (fun u : Assignment C dim ↦ ∀ c ∈ visible, u c = v' c) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hu c hc
        exact (hu c hc).trans (h c hc)
      · intro hu c hc
        exact (hu c hc).trans (h c hc).symm
    have hmask : M.Δmask sk.gap visible v w = M.Δmask sk.gap visible v' w := by
      unfold Model.Δmask
      rw [hfilter]
    have hpref : M.preferredDecision sk visible w v =
        M.preferredDecision sk visible w v' := by
      unfold preferredDecision
      rw [hmask]
    rw [hpref]

private theorem coeff_le_sign (gap p : 𝕜) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * gap ≤ (if 0 < gap then (1 : 𝕜) else 0) * gap := by
  by_cases hgap : 0 < gap
  · simp only [ite_eq_left hgap, one_mul]
    exact mul_le_of_le_one_left (le_of_lt hgap) hp1
  · simp only [ite_eq_right hgap, zero_mul]
    exact mul_nonpos_of_nonneg_of_nonpos hp0 (le_of_not_gt hgap)

end Model

/-! ## A2 identified-set packaging -/

public abbrev PolicyFamily (sk : Skeleton C dim Bool 𝕜) :=
  ∀ (visible : Finset C), visible ⊆ sk.observed →
    ProbMixture C dim 𝕜 → Policy (dim := dim) visible Bool 𝕜

@[expose] public noncomputable def AdmissibleFamily (M : Model C dim 𝕜)
    (sk : Skeleton C dim Bool 𝕜) (δ : 𝕜) (family : PolicyFamily sk) : Prop :=
  ∀ (visible : Finset C) (hvisible : visible ⊆ sk.observed) (w : ProbMixture C dim 𝕜),
    M.HasRegretAtMost sk visible (family visible hvisible w) w δ

@[expose] public noncomputable def InIdentifiedSet (sk : Skeleton C dim Bool 𝕜)
    (lam δ : 𝕜) (M M' : Model C dim 𝕜) : Prop :=
  sk.MarginClass M lam ∧ sk.MarginClass M' lam ∧
    ∃ family : PolicyFamily sk,
      AdmissibleFamily M sk δ family ∧ AdmissibleFamily M' sk δ family

public noncomputable def optimalPolicyFamily (M : Model C dim 𝕜)
    (sk : Skeleton C dim Bool 𝕜) : PolicyFamily sk :=
  fun visible _ w ↦ M.bestPolicy sk visible w

/-! ## A2 model error and radius -/

@[expose] public noncomputable def cptError (M M' : Model C dim 𝕜) (c : C) : 𝕜 :=
  Finset.sup' Finset.univ
    ⟨(⟨0, M.dim_pos c⟩, fun i ↦ ⟨0, M.dim_pos i⟩), Finset.mem_univ _⟩
    fun av : Fin (dim c) × Assignment C dim ↦
      |M.cpt c av.1 av.2 - M'.cpt c av.1 av.2|

public theorem cptError_nonneg (M M' : Model C dim 𝕜) (c : C) :
    0 ≤ cptError M M' c := by
  classical
  unfold cptError
  let z : Fin (dim c) × Assignment C dim :=
    (⟨0, M.dim_pos c⟩, fun i ↦ ⟨0, M.dim_pos i⟩)
  calc
    0 ≤ |M.cpt c z.1 z.2 - M'.cpt c z.1 z.2| := abs_nonneg _
    _ ≤ Finset.sup' Finset.univ
        ⟨z, Finset.mem_univ z⟩
        (fun av : Fin (dim c) × Assignment C dim ↦
          |M.cpt c av.1 av.2 - M'.cpt c av.1 av.2|) :=
      Finset.le_sup'
        (fun av : Fin (dim c) × Assignment C dim ↦
          |M.cpt c av.1 av.2 - M'.cpt c av.1 av.2|)
        (Finset.mem_univ z)

@[expose] public noncomputable def modelError [Nonempty C] (M M' : Model C dim 𝕜) : 𝕜 :=
  if M.parents = M'.parents then
    Finset.sup' Finset.univ Finset.univ_nonempty (cptError M M')
  else 1

/-- Table entries lie in the unit interval, so their differences lie in `[-1, 1]`
and every `cptError` is at most `1`.-/
public theorem cptError_le_one (M M' : Model C dim 𝕜) (c : C) :
    cptError M M' c ≤ 1 := by
  classical
  refine Finset.sup'_le _ _ fun av _ ↦ ?_
  rw [abs_le]
  have h1 := M.cpt_nonneg c av.1 av.2
  have h2 := M.cpt_le_one c av.1 av.2
  have h3 := M'.cpt_nonneg c av.1 av.2
  have h4 := M'.cpt_le_one c av.1 av.2
  constructor <;> linarith

/-- The printed error is non-negative. On the graph branch it is `1`; on the
table branch it is a supremum of absolute values.-/
public theorem modelError_nonneg [Nonempty C] (M M' : Model C dim 𝕜) :
    0 ≤ modelError M M' := by
  classical
  unfold modelError
  by_cases hp : M.parents = M'.parents
  · rw [ite_eq_left hp]
    exact le_trans (cptError_nonneg M M' (Classical.arbitrary C))
      (Finset.le_sup' _ (Finset.mem_univ _))
  · rw [ite_eq_right hp]
    exact zero_le_one

/-- The printed error is at most `1`, which is what makes it integrable against
any probability measure. Both branches are bounded by `1`: the graph branch is
`1` exactly, and the table branch is a supremum of differences of numbers in the
unit interval.-/
public theorem modelError_le_one [Nonempty C] (M M' : Model C dim 𝕜) :
    modelError M M' ≤ 1 := by
  classical
  unfold modelError
  by_cases hp : M.parents = M'.parents
  · rw [ite_eq_left hp]
    exact Finset.sup'_le _ _ fun c _ ↦ cptError_le_one M M' c
  · rw [ite_eq_right hp]

@[expose] public def radiusErrors [Nonempty C] (sk : Skeleton C dim Bool 𝕜)
    (lam δ : 𝕜) : Set 𝕜 :=
  {e | ∃ M M' : Model C dim 𝕜, sk.MarginClass M lam ∧ InIdentifiedSet sk lam δ M M' ∧
    e = modelError M M'}

@[expose] public def IsRadius [Nonempty C] (sk : Skeleton C dim Bool 𝕜)
    (lam δ r : 𝕜) : Prop :=
  IsLUB (radiusErrors sk lam δ) r

end AISafetyAtlas.Causal
