module

public import Tengoku.Seed.Data.Fintype.Pi
public import Tengoku.Seed.Data.Fintype.Prod
public import Tengoku.Seed.Data.Fintype.BigOperators
public import Tengoku.Seed.Data.Finset.Max
public import Tengoku.Seed.Data.Real.Basic
public import Tengoku.Seed.Algebra.BigOperators.Fin
public import Tengoku.Seed.Algebra.BigOperators.Ring.Finset
public import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
public import Tengoku.Seed.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Tengoku.Seed.Logic.Equiv.Fin.Basic
public import Tengoku.Seed.Tactic.FinCases
public import Tengoku.Seed.Tactic.Linarith
public import Tengoku.Seed.Tactic.NormNum
public import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite categorical causal models and local interventions

This is the reusable finite categorical kernel used by the causal examples.
It is constructive data `(G, θ)`, not Pearl's semantic Definition 1.3.1.

## Grounding

| Lean | Source |
|---|---|
| `dim`, `Assignment`, full-simplex `cpt` | Richens--Everitt 2024, Appendix A.2 |
| `LocalIntervention`, `factor` | Richens--Everitt Definition 2 and equation (1) |
| `hardInterventionProfile`, `jointProb_hardInterventionProfile` | Pearl 2009, truncated factorization (1.37) |
| `jointProb` | the atlas's own product over every local-intervention profile; (1.37) is its hard-intervention corollary, not its definition |
| `ProbMixture`, `jointProbMix` | Richens--Everitt Definition 3, at whichever field `𝕜` a statement picks |

`factor` is literally the preimage sum in equation (1). A local intervention
is therefore any map on a variable's finite state space; identity, translations,
Boolean NOT, and hard fixes are instances rather than constructors.

The CPT stores the full simplex. Appendix A.2 omits the final cell only as a
free-coordinate chart for an almost-every argument, which is outside this layer.

## Scope fences

* `Model` is not Pearl Definition 1.3.1, do-calculus, or an identification result.
* Chance variables only are graph vertices. Decision and utility nodes belong to
  a later CID layer; `Decision.lean` is the unmediated projection.
* Tables and mixture weights carry the value field `𝕜` as a parameter, so the
  printed real parameter space is an instance rather than an extrapolation.
  Rational witnesses transport to any characteristic-zero ordered field via
  `Model.mapRat` and the transport lemmas in `MarginClass.lean`.
* `Δ` is the general expected utility-gap transform. RE24 Appendix B equation (3)
  is one two-variable hard-intervention instance with the opposite sign.
-/

namespace AISafetyAtlas.Causal

/-- An assignment to categorical variables with dimensions `dim`.-/
public abbrev Assignment (C : Type*) (dim : C → ℕ) := (c : C) → Fin (dim c)

/-- The categorical dimensions used by every binary specialization.-/
public abbrev binaryDim (C : Type*) : C → ℕ := fun _ ↦ 2

/-- A local intervention on `c`: the state map of RE24 Definition 2.-/
public abbrev LocalIntervention {C : Type*} (dim : C → ℕ) (c : C) :=
  Fin (dim c) → Fin (dim c)

/-- One local state map per chance variable.-/
public abbrev InterventionProfile (C : Type*) (dim : C → ℕ) :=
  (c : C) → LocalIntervention dim c

/-- The identity local intervention.-/
@[expose] public def identityIntervention {n : ℕ} : Fin n → Fin n := id

/-- A hard intervention fixing a variable to `a`.-/
@[expose] public def fixIntervention {n : ℕ} (a : Fin n) : Fin n → Fin n := fun _ ↦ a

/-- The profile hard-fixing every chance variable to the corresponding target state.-/
@[expose] public def fixProfile {C : Type*} {dim : C → ℕ}
    (target : Assignment C dim) : InterventionProfile C dim :=
  fun c ↦ fixIntervention (target c)

/-- Pearl hard intervention on a selected set of chance variables.-/
@[expose] public def hardInterventionProfile {C : Type*} [DecidableEq C]
    {dim : C → ℕ} (targets : Finset C) (target : Assignment C dim) :
    InterventionProfile C dim :=
  fun c ↦ if c ∈ targets then fixIntervention (target c) else identityIntervention

/-- Boolean NOT transported to `Fin 2`.-/
@[expose] public def flipIntervention : Fin 2 → Fin 2 :=
  fun a ↦ finTwoEquiv.symm (!finTwoEquiv a)

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {C : Type*} [Fintype C] [DecidableEq C]
variable {dim : C → ℕ}

/-- A finite categorical Bayesian-network presentation.

The structure is constructive `(G, θ)`. `acyclic` is existential so distinct
ranking witnesses do not make otherwise identical models unequal.-/
public structure Model (C : Type*) [Fintype C] [DecidableEq C] (dim : C → ℕ)
    (𝕜 : Type*) [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] where
  /-- Every categorical variable has at least one state.-/
  dim_pos : ∀ c, 0 < dim c
  /-- The parents of each chance variable.-/
  parents : C → Finset C
  /-- Some ranking sends every parent strictly earlier.-/
  acyclic : ∃ rank : C → ℕ, ∀ c, ∀ p ∈ parents c, rank p < rank c
  /-- Full-simplex conditional probability tables.-/
  cpt : (c : C) → Fin (dim c) → Assignment C dim → 𝕜
  /-- A table reads only the declared parents.-/
  cpt_parents :
    ∀ c a v w, (∀ p ∈ parents c, v p = w p) → cpt c a v = cpt c a w
  /-- Every table cell is nonnegative.-/
  cpt_nonneg : ∀ c a v, 0 ≤ cpt c a v
  /-- Every conditional table is a probability simplex.-/
  cpt_sum : ∀ c v, ∑ a : Fin (dim c), cpt c a v = 1

namespace Model

/-- Every table cell is at most `1`: it is one summand of a simplex whose other
summands are non-negative. Stated here rather than derived at each use, because
the pair `cpt_nonneg`/`cpt_le_one` is what puts a table entry in the unit
interval, and several layers need that and not the sum itself.-/
public theorem cpt_le_one (M : Model C dim 𝕜) (c : C) (a : Fin (dim c))
    (v : Assignment C dim) : M.cpt c a v ≤ 1 := by
  classical
  calc M.cpt c a v ≤ ∑ b : Fin (dim c), M.cpt c b v :=
        Finset.single_le_sum (fun b _ ↦ M.cpt_nonneg c b v) (Finset.mem_univ a)
    _ = 1 := M.cpt_sum c v

/-- RE24 equation (1): sum the original CPT over the preimage of the realized state.-/
@[expose] public def factor (M : Model C dim 𝕜) (σ : InterventionProfile C dim)
    (v : Assignment C dim) (c : C) : 𝕜 :=
  ∑ a : Fin (dim c), if σ c a = v c then M.cpt c a v else 0

/-- A factor reads the child's realized state and its parent coordinates only.

This is a consequence of constructing the factor from `cpt_parents`; it is not
a transcription of Pearl Definition 1.3.1(iii).-/
public theorem factor_congr (M : Model C dim 𝕜) (σ : InterventionProfile C dim)
    (v w : Assignment C dim) (c : C)
    (hpar : ∀ p ∈ M.parents c, v p = w p) (hval : v c = w c) :
    M.factor σ v c = M.factor σ w c := by
  unfold factor
  apply Finset.sum_congr rfl
  intro a _
  rw [hval, M.cpt_parents c a v w hpar]

/-- The product of the local-intervention factors. For profiles made of identities
and hard fixes this is Pearl's truncated factorization (1.37), with consistency
indicators restoring the deleted factors.-/
@[expose] public def jointProb (M : Model C dim 𝕜) (σ : InterventionProfile C dim)
    (v : Assignment C dim) : 𝕜 :=
  ∏ c : C, M.factor σ v c

/-- The expected utility-gap transform under one deterministic profile.-/
@[expose] public def Δ (M : Model C dim 𝕜) (g : Assignment C dim → 𝕜)
    (σ : InterventionProfile C dim) : 𝕜 :=
  ∑ v : Assignment C dim, M.jointProb σ v * g v

/-- Acyclicity rules out self-parent edges.-/
public theorem notMem_parents_self (M : Model C dim 𝕜) (c : C) : c ∉ M.parents c := by
  obtain ⟨rank, hrank⟩ := M.acyclic
  exact fun h ↦ lt_irrefl _ (hrank c c h)

/-- Summing a factor over its realized state gives one.-/
public theorem factor_sum (M : Model C dim 𝕜) (σ : InterventionProfile C dim)
    (v : Assignment C dim) (c : C) :
    ∑ b : Fin (dim c), M.factor σ (Function.update v c b) c = 1 := by
  have hcpt : ∀ a b, M.cpt c a (Function.update v c b) = M.cpt c a v := by
    intro a b
    apply M.cpt_parents c a _ v
    intro p hp
    have hne : p ≠ c := fun h ↦ M.notMem_parents_self c (h ▸ hp)
    simp [hne]
  unfold factor
  rw [Finset.sum_comm]
  simp only [Function.update_self, hcpt]
  simpa using M.cpt_sum c v

/-- A hard-fix factor is the consistency indicator for the target state.-/
@[simp] public theorem factor_fixProfile (M : Model C dim 𝕜) (target actual : Assignment C dim)
    (c : C) :
    M.factor (fixProfile target) actual c = if target c = actual c then 1 else 0 := by
  by_cases h : target c = actual c
  · simp [factor, fixProfile, fixIntervention, h, M.cpt_sum]
  · simp [factor, fixProfile, fixIntervention, h]

/-- A selected hard intervention deletes the original factor and replaces it
with a consistency indicator; every unselected factor is unchanged.-/
@[simp] public theorem factor_hardInterventionProfile (M : Model C dim 𝕜)
    (targets : Finset C) (target actual : Assignment C dim) (c : C) :
    M.factor (hardInterventionProfile targets target) actual c =
      if c ∈ targets then (if target c = actual c then 1 else 0)
      else M.cpt c (actual c) actual := by
  by_cases hc : c ∈ targets
  · by_cases hval : target c = actual c
    · simp [factor, hardInterventionProfile, fixIntervention, hc, hval, M.cpt_sum]
    · simp [factor, hardInterventionProfile, fixIntervention, hc, hval]
  · simp [factor, hardInterventionProfile, identityIntervention, hc]

/-! ### Normalization of the finite DAG product -/

private def zeroAssignment (M : Model C dim 𝕜) : Assignment C dim :=
  fun c ↦ ⟨0, M.dim_pos c⟩

private abbrev FixedAt (M : Model C dim 𝕜) (c : C) :=
  {v : Assignment C dim // v c = M.zeroAssignment c}

private noncomputable instance instFintypeFixedAt (M : Model C dim 𝕜) (c : C) :
    Fintype (M.FixedAt c) :=
  Fintype.subtype
    (Finset.univ.filter fun v : Assignment C dim ↦ v c = M.zeroAssignment c) (by simp)

private def splitAt (M : Model C dim 𝕜) (c : C) :
    M.FixedAt c × Fin (dim c) ≃ Assignment C dim where
  toFun x := Function.update x.1.1 c x.2
  invFun v :=
    (⟨Function.update v c (M.zeroAssignment c), Function.update_self _ _ _⟩, v c)
  left_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      funext i
      by_cases h : i = c
      · subst i
        simp [x.1.2]
      · simp [h]
    · simp
  right_inv v := by
    funext i
    by_cases h : i = c
    · subst i
      simp
    · simp [h]

private theorem sum_splitAt (M : Model C dim 𝕜) (c : C)
    (f : Assignment C dim → 𝕜) :
    (∑ v, f v) = ∑ x : M.FixedAt c, ∑ a : Fin (dim c),
      f (Function.update x.1 c a) := by
  rw [← (M.splitAt c).sum_comp f, Fintype.sum_prod_type]
  rfl

/-- A set closed under taking parents.-/
@[expose] public def ParentClosed (M : Model C dim 𝕜) (s : Finset C) : Prop :=
  ∀ c ∈ s, ∀ p ∈ M.parents c, p ∈ s

public instance instDecidableParentClosed (M : Model C dim 𝕜) (s : Finset C) :
    Decidable (M.ParentClosed s) := by
  unfold ParentClosed
  infer_instance

private def partialWeight (M : Model C dim 𝕜) (σ : InterventionProfile C dim)
    (s : Finset C) (v : Assignment C dim) : 𝕜 :=
  ∏ c ∈ s, M.factor σ v c

private theorem partialWeight_update (M : Model C dim 𝕜) (σ : InterventionProfile C dim)
    (s : Finset C) (c : C) (hcs : c ∉ s)
    (hsink : ∀ d ∈ s, c ∉ M.parents d) (v : Assignment C dim) (a : Fin (dim c)) :
    M.partialWeight σ s (Function.update v c a) = M.partialWeight σ s v := by
  unfold partialWeight
  apply Finset.prod_congr rfl
  intro d hd
  apply M.factor_congr
  · intro p hp
    have hne : p ≠ c := fun h ↦ hsink d hd (h ▸ hp)
    simp [hne]
  · have hne : d ≠ c := fun h ↦ hcs (h ▸ hd)
    simp [hne]

private theorem sum_partialWeight_insert (M : Model C dim 𝕜)
    (σ : InterventionProfile C dim) (s : Finset C) (c : C) (hcs : c ∉ s)
    (hsink : ∀ d ∈ s, c ∉ M.parents d) :
    (dim c : 𝕜) * (∑ v : Assignment C dim, M.partialWeight σ (insert c s) v) =
      ∑ v : Assignment C dim, M.partialWeight σ s v := by
  rw [M.sum_splitAt c, M.sum_splitAt c, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hindep : ∀ a : Fin (dim c),
      M.partialWeight σ s (Function.update x.1 c a) = M.partialWeight σ s x.1 :=
    fun a ↦ M.partialWeight_update σ s c hcs hsink x.1 a
  calc
    (dim c : 𝕜) * ∑ a : Fin (dim c),
        M.partialWeight σ (insert c s) (Function.update x.1 c a) =
        (dim c : 𝕜) * M.partialWeight σ s x.1 := by
          unfold partialWeight at hindep ⊢
          simp_rw [Finset.prod_insert hcs, hindep]
          rw [← Finset.sum_mul, M.factor_sum σ x.1 c]
          ring
    _ = ∑ a : Fin (dim c), M.partialWeight σ s (Function.update x.1 c a) := by
          simp only [hindep, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          norm_num

private theorem exists_sink (M : Model C dim 𝕜) (rank : C → ℕ)
    (hrank : ∀ c, ∀ p ∈ M.parents c, rank p < rank c)
    (s : Finset C) (hs : s.Nonempty) :
    ∃ c ∈ s, ∀ d ∈ s, c ∉ M.parents d := by
  rcases Finset.exists_max_image s rank hs with ⟨c, hc, hmax⟩
  refine ⟨c, hc, ?_⟩
  intro d hd hparent
  exact (not_lt_of_ge (hmax d hd)) (hrank d c hparent)

private def dimProd (𝕜 : Type*) [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (s : Finset C) : 𝕜 := ∏ c ∈ s, (dim c : 𝕜)

private theorem normalize_aux (M : Model C dim 𝕜) (σ : InterventionProfile C dim)
    (rank : C → ℕ) (hrank : ∀ c, ∀ p ∈ M.parents c, rank p < rank c)
    (s : Finset C) (hclosed : M.ParentClosed s) :
    dimProd 𝕜 (dim := dim) s * (∑ v, M.partialWeight σ s v) =
      Fintype.card (Assignment C dim) := by
  refine Finset.strongInductionOn s (fun s ih hclosed ↦ ?_) hclosed
  by_cases hs0 : s = ∅
  · subst s
    simp [dimProd, partialWeight]
  · have hs : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs0
    rcases M.exists_sink rank hrank s hs with ⟨c, hc, hsink⟩
    let t := s.erase c
    have hct : c ∉ t := by simp [t]
    have hst : s = insert c t := (Finset.insert_erase hc).symm
    have htsub : t ⊂ s := by simpa [t] using Finset.erase_ssubset hc
    have htclosed : M.ParentClosed t := by
      intro d hd p hp
      have hd_s : d ∈ s := Finset.mem_of_mem_erase hd
      have hp_s : p ∈ s := hclosed d hd_s p hp
      have hp_ne : p ≠ c := fun h ↦ hsink d hd_s (h ▸ hp)
      exact Finset.mem_erase.mpr ⟨hp_ne, hp_s⟩
    have hrec := ih t htsub htclosed
    have hsum := M.sum_partialWeight_insert σ t c hct
      (fun d hd ↦ hsink d (Finset.mem_of_mem_erase hd))
    rw [hst, dimProd, Finset.prod_insert hct]
    calc
      ((dim c : 𝕜) * ∏ x ∈ t, (dim x : 𝕜)) *
          ∑ v, M.partialWeight σ (insert c t) v =
          (∏ x ∈ t, (dim x : 𝕜)) *
            ((dim c : 𝕜) * ∑ v, M.partialWeight σ (insert c t) v) := by ring
      _ = (∏ x ∈ t, (dim x : 𝕜)) * ∑ v, M.partialWeight σ t v := by rw [hsum]
      _ = Fintype.card (Assignment C dim) := by simpa [dimProd] using hrec

/-! ## Marginals

Every printed statement past equation (1.37) — Pearl's Properties 1 and 2, and
every identification result built on them — compares **marginals** of two members
of the interventional family. `jointProb_sum` is the marginal onto the empty set;
what follows is the general form, and it is stated for an arbitrary
parent-closed set on purpose. A lemma that only normalizes supports only
normalization. -/

/-- The assignments agreeing with `w` on `s`.-/
@[expose] public def agreeSet (s : Finset C) (w : Assignment C dim) :
    Finset (Assignment C dim) :=
  Finset.univ.filter fun v ↦ ∀ c ∈ s, v c = w c

public theorem mem_agreeSet {s : Finset C} {w v : Assignment C dim} :
    v ∈ agreeSet s w ↔ ∀ c ∈ s, v c = w c := by
  simp [agreeSet]

@[simp] public theorem agreeSet_univ (w : Assignment C dim) :
    agreeSet (Finset.univ : Finset C) w = {w} := by
  ext v
  simp [mem_agreeSet, funext_iff]

/-- Fixing one more variable splits `agreeSet` into its fibres.-/
public theorem agreeSet_filter (s : Finset C) (w : Assignment C dim) {c : C}
    (hc : c ∉ s) (a : Fin (dim c)) :
    (agreeSet s w).filter (fun v ↦ v c = a) =
      agreeSet (insert c s) (Function.update w c a) := by
  classical
  ext v
  simp only [Finset.mem_filter, mem_agreeSet, Finset.mem_insert]
  constructor
  · rintro ⟨hv, hva⟩ d hd
    rcases hd with rfl | hd
    · simpa using hva
    · have hne : d ≠ c := by rintro rfl; exact hc hd
      rw [Function.update_of_ne hne]
      exact hv d hd
  · intro h
    refine ⟨fun d hd ↦ ?_, ?_⟩
    · have hne : d ≠ c := by rintro rfl; exact hc hd
      have := h d (Or.inr hd)
      rwa [Function.update_of_ne hne] at this
    · simpa using h c (Or.inl rfl)

private theorem exists_source (M : Model C dim 𝕜) (rank : C → ℕ)
    (hrank : ∀ c, ∀ p ∈ M.parents c, rank p < rank c)
    (t : Finset C) (ht : t.Nonempty) :
    ∃ c ∈ t, ∀ p ∈ M.parents c, p ∉ t := by
  rcases Finset.exists_min_image t rank ht with ⟨c, hc, hmin⟩
  refine ⟨c, hc, fun p hp hpt ↦ ?_⟩
  exact absurd (hrank c p hp) (not_lt_of_ge (hmin p hpt))

private theorem sum_agree_compl (M : Model C dim 𝕜) (σ : InterventionProfile C dim)
    (rank : C → ℕ) (hrank : ∀ c, ∀ p ∈ M.parents c, rank p < rank c) :
    ∀ t : Finset C, ∀ w : Assignment C dim,
      ∑ v ∈ agreeSet tᶜ w, ∏ c ∈ t, M.factor σ v c = 1 := by
  classical
  intro t
  induction t using Finset.strongInduction with
  | _ t ih =>
    intro w
    rcases Finset.eq_empty_or_nonempty t with rfl | ht
    · simp
    · obtain ⟨c, hct, hsrc⟩ := M.exists_source rank hrank t ht
      have hc : c ∉ tᶜ := by simpa using hct
      have hsub : t.erase c ⊂ t := Finset.erase_ssubset hct
      have hcompl : (t.erase c)ᶜ = insert c tᶜ := by
        ext d
        by_cases hd : d = c <;> simp [hd, hct]
      rw [← Finset.sum_fiberwise_of_maps_to
        (g := fun v : Assignment C dim ↦ v c) (t := Finset.univ)
        (fun v _ ↦ Finset.mem_univ _)]
      have key : ∀ a : Fin (dim c),
          (∑ v ∈ (agreeSet tᶜ w).filter (fun v ↦ v c = a),
            ∏ d ∈ t, M.factor σ v d)
            = M.factor σ (Function.update w c a) c := by
        intro a
        rw [agreeSet_filter tᶜ w hc a]
        have hprod : ∀ v ∈ agreeSet (insert c tᶜ) (Function.update w c a),
            ∏ d ∈ t, M.factor σ v d
              = M.factor σ (Function.update w c a) c * ∏ d ∈ t.erase c, M.factor σ v d := by
          intro v hv
          rw [← Finset.prod_erase_mul t _ hct, mul_comm]
          congr 1
          refine M.factor_congr σ v (Function.update w c a) c (fun p hp ↦ ?_) ?_
          · exact mem_agreeSet.mp hv p (Finset.mem_insert_of_mem (by simpa using hsrc p hp))
          · exact mem_agreeSet.mp hv c (Finset.mem_insert_self _ _)
        rw [Finset.sum_congr rfl hprod, ← Finset.mul_sum, ← hcompl]
        rw [ih (t.erase c) hsub (Function.update w c a), mul_one]
      rw [Finset.sum_congr rfl (fun a _ ↦ key a)]
      exact M.factor_sum σ w c

/-- The **marginal** of an interventional joint on the variables `s`.-/
@[expose] public noncomputable def marginal (M : Model C dim 𝕜)
    (σ : InterventionProfile C dim) (s : Finset C) (w : Assignment C dim) : 𝕜 :=
  ∑ v ∈ agreeSet s w, M.jointProb σ v

/-- **`s` carries its own factors under `σ`**: the factors of its members read
only coordinates in `s`.

This, and not parent-closure, is what marginalization actually needs. The
difference is exactly the intervened variables: a hard intervention replaces a
variable's factor by a consistency indicator, which reads that variable alone
however many parents the *graph* gives it. Stating the hypothesis this way is
what lets the same theorem serve Pearl's Properties 1 and 2, where the
conditioning set is a variable together with its parents — parent-closed only
by accident, and self-determining under `do(Pa)` always.-/
@[expose] public def SelfDetermining (M : Model C dim 𝕜)
    (σ : InterventionProfile C dim) (s : Finset C) : Prop :=
  ∀ c ∈ s, ∀ v w : Assignment C dim, (∀ d ∈ s, v d = w d) →
    M.factor σ v c = M.factor σ w c

/-- **The observational profile**: intervene nowhere. Pearl's `P` itself, as the
member of the family at the empty intervention.-/
@[expose] public def observationalProfile (C : Type*) (dim : C → ℕ) :
    InterventionProfile C dim :=
  fun _ ↦ identityIntervention

omit [Fintype C] in
@[simp] public theorem hardInterventionProfile_empty (target : Assignment C dim) :
    hardInterventionProfile (∅ : Finset C) target = observationalProfile C dim := by
  funext c
  simp [hardInterventionProfile, observationalProfile]

/-- Hard-fixing every chance variable produces the Dirac joint at the target assignment.-/
@[simp] public theorem jointProb_fixProfile (M : Model C dim 𝕜)
    (target actual : Assignment C dim) :
    M.jointProb (fixProfile target) actual = if actual = target then 1 else 0 := by
  by_cases h : actual = target
  · subst actual
    simp [jointProb]
  · rw [ite_eq_right h]
    have hcoord : ∃ c, actual c ≠ target c := by
      by_contra hnone
      apply h
      funext c
      by_contra hc
      exact hnone ⟨c, hc⟩
    rcases hcoord with ⟨c, hc⟩
    unfold jointProb
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    have hct : target c ≠ actual c := Ne.symm hc
    simp [hct]

/-- Full-profile hard intervention evaluates an outcome function at its target.-/
@[simp]
public theorem Δ_fixProfile (M : Model C dim 𝕜) (g : Assignment C dim → 𝕜)
    (target : Assignment C dim) : M.Δ g (fixProfile target) = g target := by
  unfold Δ
  rw [Fintype.sum_eq_single target]
  · simp
  · intro actual hactual
    simp [hactual]

/-- A model is its graph and full-simplex tables.-/
@[ext] public theorem ext {M M' : Model C dim 𝕜} (hp : M.parents = M'.parents)
    (hc : M.cpt = M'.cpt) : M = M' := by
  cases M
  cases M'
  cases hp
  cases hc
  rfl

public theorem sum_weighted_congr {ι : Type*} (s : Finset ι) (w : ι → 𝕜)
    (M M' : Model C dim 𝕜) (g : Assignment C dim → 𝕜)
    (σ : ι → InterventionProfile C dim)
    (h : ∀ i ∈ s, M.Δ g (σ i) = M'.Δ g (σ i)) :
    ∑ i ∈ s, w i * M.Δ g (σ i) = ∑ i ∈ s, w i * M'.Δ g (σ i) :=
  Finset.sum_congr rfl fun i hi ↦ by rw [h i hi]

end Model

/-! ## Mixtures -/

/-- Value-field weights on deterministic profiles. Probability mixtures are the
simplex subtype `ProbMixture`; the ambient space remains useful for linearity.-/
public abbrev Mixture (C : Type*) [Fintype C] [DecidableEq C] (dim : C → ℕ)
    (𝕜 : Type*) :=
  InterventionProfile C dim → 𝕜

/-- The RE24 Definition-3 simplex over whichever field a statement picks.-/
@[expose] public def IsProbabilityMixture (w : Mixture C dim 𝕜) : Prop :=
  (∀ σ, 0 ≤ w σ) ∧ ∑ σ : InterventionProfile C dim, w σ = 1

/-- A probability mixture of deterministic local-intervention profiles.-/
public abbrev ProbMixture (C : Type*) [Fintype C] [DecidableEq C] (dim : C → ℕ)
    (𝕜 : Type*) [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] :=
  {w : Mixture C dim 𝕜 // IsProbabilityMixture w}

namespace ProbMixture

/-- The point mass at one deterministic intervention profile.-/
@[expose] public def dirac (σ₀ : InterventionProfile C dim) : ProbMixture C dim 𝕜 :=
  ⟨fun σ ↦ if σ = σ₀ then 1 else 0, by
    constructor
    · intro σ
      by_cases h : σ = σ₀ <;> simp [h]
    · simp⟩

@[simp] public theorem dirac_apply (σ₀ σ : InterventionProfile C dim) :
    (dirac (𝕜 := 𝕜) σ₀ : Mixture C dim 𝕜) σ = if σ = σ₀ then 1 else 0 := by
  rfl

end ProbMixture

namespace Model

@[expose] public def jointProbMix (M : Model C dim 𝕜) (w : Mixture C dim 𝕜)
    (v : Assignment C dim) : 𝕜 :=
  ∑ σ, w σ * M.jointProb σ v

@[expose] public def Δmix (M : Model C dim 𝕜) (g : Assignment C dim → 𝕜)
    (w : Mixture C dim 𝕜) : 𝕜 :=
  ∑ v, M.jointProbMix w v * g v

public theorem Δmix_eq_sum (M : Model C dim 𝕜) (g : Assignment C dim → 𝕜)
    (w : Mixture C dim 𝕜) :
    M.Δmix g w = ∑ σ, w σ * M.Δ g σ := by
  unfold Δmix jointProbMix Δ
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun σ _ ↦ Finset.sum_congr rfl fun v _ ↦ by ring

public theorem Δmix_congr (M M' : Model C dim 𝕜) (g : Assignment C dim → 𝕜)
    (w : Mixture C dim 𝕜) (h : ∀ σ, M.Δ g σ = M'.Δ g σ) :
    M.Δmix g w = M'.Δmix g w := by
  rw [Δmix_eq_sum, Δmix_eq_sum]
  exact sum_weighted_congr Finset.univ w M M' g id fun σ _ ↦ h σ

/-- Equality on probability mixtures is equivalent to equality on deterministic profiles.-/
public theorem Δmix_eq_on_probMixture_iff (M M' : Model C dim 𝕜)
    (g : Assignment C dim → 𝕜) :
    (∀ w : ProbMixture C dim 𝕜, M.Δmix g w.1 = M'.Δmix g w.1) ↔
      ∀ σ : InterventionProfile C dim, M.Δ g σ = M'.Δ g σ := by
  constructor
  · intro h σ
    simpa [Δmix_eq_sum] using h (ProbMixture.dirac (𝕜 := 𝕜) σ)
  · intro h w
    exact M.Δmix_congr M' g w.1 h

end Model

/-! ## Binary two-variable arithmetic -/

/-- Transport a Boolean state into the binary categorical state type.-/
@[expose] public def binaryState (b : Bool) : Fin 2 := finTwoEquiv.symm b

@[simp] public theorem binaryState_false : binaryState false = 0 := rfl

@[simp] public theorem binaryState_true : binaryState true = 1 := rfl

@[simp] public theorem finTwoEquiv_symm_false : finTwoEquiv.symm false = (0 : Fin 2) := rfl

@[simp] public theorem finTwoEquiv_symm_true : finTwoEquiv.symm true = (1 : Fin 2) := rfl

/-- The assignment sending variable `0` to `a` and variable `1` to `b`.-/
@[expose] public def asg (a b : Bool) : Assignment (Fin 2) (binaryDim (Fin 2)) :=
  ![binaryState a, binaryState b]

/-! ## Ancestor closure -/

namespace Model

@[expose] public def ancestors (M : Model C dim 𝕜) (s : Finset C) : Finset C :=
  Finset.univ.filter fun c ↦ ∀ t : Finset C, s ⊆ t → M.ParentClosed t → c ∈ t

public theorem subset_ancestors (M : Model C dim 𝕜) (s : Finset C) : s ⊆ M.ancestors s := by
  intro c hc
  simp only [ancestors, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun t hst _ ↦ hst hc

public theorem parentClosed_ancestors (M : Model C dim 𝕜) (s : Finset C) :
    M.ParentClosed (M.ancestors s) := by
  unfold ParentClosed
  intro c hc p hp
  simp only [ancestors, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
  exact fun t hst ht ↦ ht c (hc t hst ht) p hp

public theorem ancestors_subset (M : Model C dim 𝕜) {s t : Finset C}
    (hst : s ⊆ t) (ht : M.ParentClosed t) : M.ancestors s ⊆ t := by
  intro c hc
  simp only [ancestors, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  exact hc t hst ht

public theorem ancestors_eq_univ_iff (M : Model C dim 𝕜) (s : Finset C) :
    M.ancestors s = Finset.univ ↔
      ∀ t : Finset C, s ⊆ t → M.ParentClosed t → t = Finset.univ := by
  constructor
  · intro h t hst ht
    exact Finset.univ_subset_iff.mp (h ▸ M.ancestors_subset hst ht)
  · intro h
    exact h _ (M.subset_ancestors s) (M.parentClosed_ancestors s)

private theorem ancestors_notMem_parents (M : Model C dim 𝕜) (rank : C → ℕ)
    (hrank : ∀ c, ∀ p ∈ M.parents c, rank p < rank c) (c : C) :
    ∀ d ∈ M.ancestors (insert c (M.parents c)), c ∉ M.parents d := by
  classical
  have hclosed : M.ParentClosed (Finset.univ.filter fun d ↦ rank d ≤ rank c) := by
    intro d hd p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    exact le_of_lt (lt_of_lt_of_le (hrank d p hp) hd)
  have hsub : insert c (M.parents c) ⊆ Finset.univ.filter fun d ↦ rank d ≤ rank c := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact le_rfl
    · exact le_of_lt (hrank c d hd)
  intro d hd hcd
  have := M.ancestors_subset hsub hclosed hd
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact absurd (hrank d c hcd) (not_lt_of_ge this)

end Model

end AISafetyAtlas.Causal
