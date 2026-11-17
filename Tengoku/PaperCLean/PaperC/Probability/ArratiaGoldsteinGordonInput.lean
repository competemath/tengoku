import Tengoku.PaperCLean.PaperC.Probability.FinitePMF
import Tengoku.Seed.Combinatorics.SimpleGraph.Finite
import Tengoku.Seed.Probability.Distributions.Poisson.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 1200000

/-!
# Arratia--Goldstein--Gordon input

This module records the external Chen--Stein theorem used in Theorem 13.7.
The interface is deliberately finite: `μ` is an arbitrary probability mass
function on a finite sample space, and `X α` is a finite family of Boolean
indicators.

For a simple graph `G` on the index type, `closedNeighborhood G α` is the
chosen set `B_α`.  The predicate `HasExactDependencyGraph μ X G` states
literal independence of `X α` from the complete Boolean vector outside
`B_α`; in the terminology of Arratia--Goldstein--Gordon this makes `b₃`
exactly zero.  The adjacency relation need not be minimal: adding edges
preserves the intended dependency-neighborhood interpretation.

The law of the indicator sum and the Poisson law are represented by their
real mass functions on `ℕ`.  Total variation uses the standard half-`ℓ¹`
normalization.  No external result is introduced as a Lean axiom: every use
of Theorem 13.7 must explicitly receive
`ArratiaGoldsteinGordonStatement` as a hypothesis.
-/

namespace PaperC
namespace ArratiaGoldsteinGordonInput

open scoped BigOperators NNReal

open ProbabilityTheory

noncomputable section

universe u v

/-! ## Finite events and indicator families -/

/-- Probability of an event under a finite probability mass function.-/
noncomputable def eventProbability
    {Ω : Type u} [Fintype Ω]
    (μ : FinitePMF Ω) (event : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if event ω then μ.prob ω else 0

/-- Event probabilities are nonnegative.
@isnad1 id=le.0h3v.s4.625454f08fa4 from=translated src=- shape=9befd6ab vocab=b8cd9b38
-/
theorem eventProbability_nonneg
    {Ω : Type u} [Fintype Ω]
    (μ : FinitePMF Ω) (event : Ω → Prop) :
    0 ≤ eventProbability μ event := by
  classical
  unfold eventProbability
  exact Finset.sum_nonneg fun ω _ ↦ by
    split_ifs
    · exact μ.nonneg ω
    · exact le_rfl

/-- The Bernoulli marginal `p_α = P(X_α = 1)`.-/
noncomputable def marginal
    {Ω : Type u} {ι : Type v} [Fintype Ω]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) (α : ι) : ℝ :=
  eventProbability μ fun ω ↦ X α ω = true

/-- The joint Bernoulli mass `p_{αβ} = P(X_α = X_β = 1)`.-/
noncomputable def jointMarginal
    {Ω : Type u} {ι : Type v} [Fintype Ω]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (α β : ι) : ℝ :=
  eventProbability μ fun ω ↦
    X α ω = true ∧ X β ω = true

/--
@isnad1 id=le.0h5v.s5.847027085d5d from=translated src=- shape=c181798b vocab=46368cfb
-/
theorem marginal_nonneg
    {Ω : Type u} {ι : Type v} [Fintype Ω]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) (α : ι) :
    0 ≤ marginal μ X α :=
  eventProbability_nonneg μ _

/--
@isnad1 id=le.0h6v.s5.e6d21b9835d2 from=translated src=- shape=d5ba6d23 vocab=e7abcc5c
-/
theorem jointMarginal_nonneg
    {Ω : Type u} {ι : Type v} [Fintype Ω]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (α β : ι) :
    0 ≤ jointMarginal μ X α β :=
  eventProbability_nonneg μ _

/-- The mean parameter `λ = ∑_α p_α`.-/
noncomputable def poissonParameter
    {Ω : Type u} {ι : Type v} [Fintype Ω] [Fintype ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) : ℝ :=
  ∑ α, marginal μ X α

/--
@isnad1 id=le.0h4v.s5.9b4264b3e243 from=translated src=- shape=ba9a9680 vocab=7e53900e
-/
theorem poissonParameter_nonneg
    {Ω : Type u} {ι : Type v} [Fintype Ω] [Fintype ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) :
    0 ≤ poissonParameter μ X := by
  unfold poissonParameter
  exact Finset.sum_nonneg fun α _ ↦ marginal_nonneg μ X α

/-- `λ` packaged as a nonnegative real for Mathlib's Poisson PMF.-/
noncomputable def poissonRate
    {Ω : Type u} {ι : Type v} [Fintype Ω] [Fintype ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) : ℝ≥0 :=
  ⟨poissonParameter μ X, poissonParameter_nonneg μ X⟩

/-! ## Closed neighborhoods and exact finite dependence -/

/-- The closed graph neighborhood `B_α = {α} ∪ {β : α ∼ β}`.-/
noncomputable def closedNeighborhood
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (α : ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun β ↦ β = α ∨ G.Adj α β

/--
@isnad1 id=iff.0h4v.s5.ede82d9ebf24 from=translated src=- shape=8a73a797 vocab=a5090e14
-/
@[simp]
theorem mem_closedNeighborhood
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} {α β : ι} :
    β ∈ closedNeighborhood G α ↔
      β = α ∨ G.Adj α β := by
  classical
  simp [closedNeighborhood]

/--
@isnad1 id=mem.0h3v.s4.9f09b3cbdcbd from=translated src=- shape=eabbea16 vocab=87cd4346
-/
@[simp]
theorem self_mem_closedNeighborhood
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (α : ι) :
    α ∈ closedNeighborhood G α := by
  simp

/-- Indices outside the chosen dependency neighborhood of `α`.-/
def OutsideIndex
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (α : ι) :=
  {β : ι // β ∉ closedNeighborhood G α}

/--
The complete outside vector has the prescribed Boolean pattern.

Quantifying over all such patterns is the finite, atom-by-atom version of
the sigma-field generated by the indicators outside `B_α`.-/
def HasOutsidePattern
    {Ω : Type u} {ι : Type v}
    [Fintype ι] [DecidableEq ι]
    (X : ι → Ω → Bool) (G : SimpleGraph ι) (α : ι)
    (pattern : OutsideIndex G α → Bool) (ω : Ω) : Prop :=
  ∀ β : OutsideIndex G α, X β.1 ω = pattern β

/--
`G` is an exact dependency graph for the finite indicator family.

For every vertex, the indicator at that vertex is independent of every atom
of the complete indicator vector outside its closed neighborhood.  This is
an exact equality, not an asymptotic or approximate independence claim, and
is precisely the finite hypothesis which removes the `b₃` term.-/
def HasExactDependencyGraph
    {Ω : Type u} {ι : Type v}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι) : Prop :=
  ∀ (α : ι) (value : Bool)
      (pattern : OutsideIndex G α → Bool),
    eventProbability μ (fun ω ↦
        X α ω = value ∧ HasOutsidePattern X G α pattern ω) =
      eventProbability μ (fun ω ↦ X α ω = value) *
        eventProbability μ (HasOutsidePattern X G α pattern)

/-! ## The two Chen--Stein error terms -/

/--
The first Arratia--Goldstein--Gordon term
`b₁ = ∑_α ∑_{β∈B_α} p_α p_β`.-/
noncomputable def bOne
    {Ω : Type u} {ι : Type v}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι) : ℝ :=
  ∑ α, ∑ β ∈ closedNeighborhood G α,
    marginal μ X α * marginal μ X β

/--
The second Arratia--Goldstein--Gordon term
`b₂ = ∑_α ∑_{β∈B_α, β≠α} p_{αβ}`.

Because a simple graph is loopless, `B_α \ {α}` is exactly the open
neighborhood of `α`.-/
noncomputable def bTwo
    {Ω : Type u} {ι : Type v}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι) : ℝ :=
  ∑ α, ∑ β ∈ (closedNeighborhood G α).erase α,
    jointMarginal μ X α β

/--
@isnad1 id=le.0h5v.s5.88393def9c73 from=translated src=- shape=f4696f94 vocab=4a9eb80b
-/
theorem bOne_nonneg
    {Ω : Type u} {ι : Type v}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι) :
    0 ≤ bOne μ X G := by
  unfold bOne
  exact Finset.sum_nonneg fun α _ ↦
    Finset.sum_nonneg fun β _ ↦
      mul_nonneg (marginal_nonneg μ X α)
        (marginal_nonneg μ X β)

/--
@isnad1 id=le.0h5v.s5.3121b683fbd2 from=translated src=- shape=f4696f94 vocab=e91794ff
-/
theorem bTwo_nonneg
    {Ω : Type u} {ι : Type v}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι) :
    0 ≤ bTwo μ X G := by
  unfold bTwo
  exact Finset.sum_nonneg fun α _ ↦
    Finset.sum_nonneg fun β _ ↦
      jointMarginal_nonneg μ X α β

/-! ## Law of the indicator sum and Poisson total variation -/

/-- The integer-valued indicator sum `W = ∑_α X_α`.-/
noncomputable def indicatorSum
    {Ω : Type u} {ι : Type v} [Fintype ι]
    (X : ι → Ω → Bool) (ω : Ω) : ℕ := by
  classical
  exact (Finset.univ.filter fun α ↦ X α ω = true).card

/-- The law of `W`, represented by its real mass function on `ℕ`.-/
noncomputable def indicatorSumLaw
    {Ω : Type u} {ι : Type v} [Fintype Ω] [Fintype ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) (k : ℕ) : ℝ :=
  eventProbability μ fun ω ↦ indicatorSum X ω = k

/--
@isnad1 id=le.0h5v.s5.7e89bdec1898 from=translated src=- shape=81f16932 vocab=effdf931
-/
theorem indicatorSumLaw_nonneg
    {Ω : Type u} {ι : Type v} [Fintype Ω] [Fintype ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) (k : ℕ) :
    0 ≤ indicatorSumLaw μ X k :=
  eventProbability_nonneg μ _

/-!
## The external input

The source theorem has a third error term `b₃`.  Under
`HasExactDependencyGraph`, the variable `X_α` is independent of the complete
outside vector, so the specialization used here has `b₃ = 0`.  We retain the
weaker but convention-independent consequence
`dTV ≤ 2 (b₁ + b₂)` requested by the manuscript interface.
-/

/- AUDIT_BRIDGE
{
  "id": "AGG89-T1-finite-dependency-b3-zero",
  "kind": "external",
  "status": "open",
  "lean_name": "PaperC.ArratiaGoldsteinGordonInput.ArratiaGoldsteinGordonStatement",
  "citation": {
    "authors": ["Richard Arratia", "Larry Goldstein", "Louis Gordon"],
    "title": "Two moments suffice for Poisson approximations: the Chen–Stein method",
    "journal": "The Annals of Probability 17 (1989), 9–25",
    "doi": "10.1214/aop/1176991491",
    "locator": "Theorem 1, p. 10"
  },
  "source_statement": {
    "verbatim": "≤ 2(b₁ + b₂ + b₃).",
    "verbatim_is_excerpt": true,
    "source_url": "https://doi.org/10.1214/aop/1176991491",
    "verification": "manual_primary_source_check_required"
  },
  "manuscript_locator": {
    "result": "Theorem 13.7",
    "equation": "Arratia–Goldstein–Gordon bound with b₃ = 0",
    "pages": "41–42"
  },
  "formalization_relation": "finite-family specialization of Theorem 1 to closed graph neighborhoods and exact independence outside each neighborhood, hence b₃ = 0; total variation is defined with the standard half-L¹ normalization"
}
AUDIT_BRIDGE -/

end

end ArratiaGoldsteinGordonInput
end PaperC
