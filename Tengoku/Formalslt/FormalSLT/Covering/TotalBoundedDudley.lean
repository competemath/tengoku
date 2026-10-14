import Tengoku
import Tengoku.Formalslt.FormalSLT.Covering.FiniteSubGaussianChaining

/-!
# Total-bounded Dudley bridge

This module starts the continuous/total-bounded Dudley lane without claiming a
continuous Dudley integral. The immediate goal is smaller and structural:
connect Mathlib's `TotallyBounded` metric-space API to the finite-net records
used by `FiniteSubGaussianChaining`.

The main construction extracts, from a totally bounded index space and a
positive radius, a bundled `FiniteNet` over the ambient metric distance. This
is the topology adapter needed before the finite dyadic chaining machinery can
be fed by total-bounded covering hypotheses.

Scope:

* metric index spaces, via `PseudoMetricSpace`;
* finite nets extracted at one positive scale;
* finite terminal wrappers that compose those nets with the existing finite
  Dudley entropy-budget theorem;
* no continuous entropy integral yet;
* no measurable supremum over arbitrary index classes yet.
-/

open Set
open scoped BigOperators Interval

namespace FormalSLT.Covering.TotalBoundedDudley

open FormalSLT.Covering.FiniteSubGaussianChaining

noncomputable section

universe u

variable {T : Type u}

/-- A finite net bundled with its finite index type.

`FiniteSubGaussianChaining.FiniteNet` is indexed by an explicit finite type of
centers. Mathlib's total-boundedness API returns finite sets of centers, so this
small bundle carries the finite subtype and the resulting `FiniteNet` together.
-/
structure BundledFiniteNet (T : Type u) where
  A : Type u
  instFintype : Fintype A
  instNonempty : Nonempty A
  net : @FiniteNet T A instFintype

namespace BundledFiniteNet

attribute [instance] instFintype instNonempty

/-- Cardinality of the bundled finite net. -/
def coveringNumber (B : BundledFiniteNet T) : ℕ :=
  @FiniteNet.coveringNumber T B.A B.instFintype B.net

end BundledFiniteNet

/-- Convert an explicit finite metric cover of the whole space into the
finite-net record used by the finite chaining layer. -/
def finiteNetOfCoverSet [PseudoMetricSpace T] [Nonempty T]
    (C : Set T) (hCfinite : C.Finite)
    (r : ℝ) (hr : 0 ≤ r)
    (hcover : ∀ t : T, ∃ c : T, c ∈ C ∧ dist t c ≤ r) :
    BundledFiniteNet T := by
  classical
  let A : Type u := {c : T // c ∈ C}
  let instFintype : Fintype A := hCfinite.fintype
  have instNonempty : Nonempty A := by
    obtain ⟨t⟩ := (inferInstance : Nonempty T)
    obtain ⟨c, hc, _hc_dist⟩ := hcover t
    exact ⟨⟨c, hc⟩⟩
  let project : T → A := fun t =>
    ⟨Classical.choose (hcover t), (Classical.choose_spec (hcover t)).1⟩
  let N : @FiniteNet T A instFintype :=
    { dist := fun s t => dist s t
      dist_nonneg := fun s t => dist_nonneg
      center := fun a => a.1
      project := project
      radius := r
      radius_nonneg := hr
      covers := by
        intro t
        exact (Classical.choose_spec (hcover t)).2 }
  exact
    { A := A
      instFintype := instFintype
      instNonempty := instNonempty
      net := N }

/-- The identity finite net on a finite metric index type.

This is the terminal net used by the dyadic total-bounded wrapper: earlier
scales are supplied by total boundedness, while the final finite scale is exact
so the existing finite chaining telescope can close. -/
def identityBundledFiniteNet [PseudoMetricSpace T] [Fintype T] [Nonempty T] :
    BundledFiniteNet T := by
  classical
  let N : FiniteNet T T :=
    { dist := fun s t => dist s t
      dist_nonneg := fun s t => dist_nonneg
      center := id
      project := id
      radius := 0
      radius_nonneg := le_rfl
      covers := by
        intro t
        simp }
  exact
    { A := T
      instFintype := inferInstance
      instNonempty := inferInstance
      net := N }

/--
@isnad1 id=eq.0h1v.s5.5723bda93561 from=translated src=- shape=84c616ba vocab=30772e0a
-/
@[simp] theorem identityBundledFiniteNet_radius
    [PseudoMetricSpace T] [Fintype T] [Nonempty T] :
    (identityBundledFiniteNet (T := T)).net.radius = 0 := by
  rfl

/--
@isnad1 id=eq.0h1v.s5.9af0c6b039ce from=translated src=- shape=c46f4818 vocab=2f0c10f0
-/
@[simp] theorem identityBundledFiniteNet_dist
    [PseudoMetricSpace T] [Fintype T] [Nonempty T] :
    (identityBundledFiniteNet (T := T)).net.dist = fun s t => dist s t := by
  rfl

/--
@isnad1 id=eq.0h2v.s5.a406903810d6 from=translated src=- shape=492e91b0 vocab=60502953
-/
@[simp] theorem identityBundledFiniteNet_projection
    [PseudoMetricSpace T] [Fintype T] [Nonempty T] (t : T) :
    (identityBundledFiniteNet (T := T)).net.projection t = t := by
  rfl

/-- A totally bounded metric index space admits a finite metric cover at every
positive real radius. This is the Mathlib extraction step, stated with `dist`
and `≤` so it can feed `FiniteNet`.
@isnad1 id=ex.2h2v.s5.92a44deccc9c from=translated src=- shape=6be7a2ba vocab=4d59f82d
-/
theorem finiteMetricCoverOfTotallyBoundedUniv [PseudoMetricSpace T]
    (hT : TotallyBounded (Set.univ : Set T)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Set T, C.Finite ∧ ∀ t : T, ∃ c : T, c ∈ C ∧ dist t c ≤ ε := by
  obtain ⟨C, _hC_subset, hCfinite, hcover⟩ :=
    Metric.finite_approx_of_totallyBounded (s := Set.univ) hT ε hε
  refine ⟨C, hCfinite, ?_⟩
  intro t
  have ht : t ∈ (Set.univ : Set T) := by simp
  have ht_cover : t ∈ ⋃ y ∈ C, Metric.ball y ε := hcover ht
  simp only [mem_iUnion, Metric.mem_ball] at ht_cover
  obtain ⟨c, hc, hdist_lt⟩ := ht_cover
  exact ⟨c, hc, le_of_lt hdist_lt⟩

/-- Extract a bundled finite net from a totally bounded metric index space at
any positive radius. The net uses the ambient metric distance and covers every
point within radius `ε`. -/
def finiteNetOfTotallyBoundedUniv [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) (ε : ℝ) (hε : 0 < ε) :
    BundledFiniteNet T := by
  classical
  let cover := finiteMetricCoverOfTotallyBoundedUniv (T := T) hT hε
  exact finiteNetOfCoverSet
    (Classical.choose cover)
    (Classical.choose_spec cover).1
    ε hε.le
    (Classical.choose_spec cover).2

/-- The finite net extracted from total boundedness uses the requested radius.
@isnad1 id=eq.2h2v.s5.dfafdd1f7bc2 from=translated src=- shape=3aedba70 vocab=4d3f65c2
-/
@[simp] theorem finiteNetOfTotallyBoundedUniv_radius
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) (ε : ℝ) (hε : 0 < ε) :
    (finiteNetOfTotallyBoundedUniv (T := T) hT ε hε).net.radius = ε := by
  rfl

/-- The finite net extracted from total boundedness uses the ambient metric
distance.
@isnad1 id=eq.2h2v.s6.871382a384f6 from=translated src=- shape=de8144fc vocab=0f7cbdd2
-/
@[simp] theorem finiteNetOfTotallyBoundedUniv_dist
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) (ε : ℝ) (hε : 0 < ε) :
    (finiteNetOfTotallyBoundedUniv (T := T) hT ε hε).net.dist = fun s t => dist s t := by
  rfl

/-- The projection selected by the total-bounded finite net is within the
requested metric radius.
@isnad1 id=le.2h3v.s6.b399b899a3dd from=translated src=- shape=8aab1a01 vocab=fc69f5a5
-/
theorem finiteNetOfTotallyBoundedUniv_covers
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) {ε : ℝ} (hε : 0 < ε)
    (t : T) :
    dist t ((finiteNetOfTotallyBoundedUniv (T := T) hT ε hε).net.projection t) ≤ ε := by
  simpa [finiteNetOfTotallyBoundedUniv_radius]
    using (finiteNetOfTotallyBoundedUniv (T := T) hT ε hε).net.projection_dist_le t

/-! ## Dyadic net schedule for the Dudley bridge -/

/-- Radius used for the dyadic finite-net schedule in the first
total-bounded Dudley bridge.

The extra `2^2` shrinkage leaves room for adjacent projection increments:
`r_j + r_{j+1} <= radiusScale / 2^j`. -/
def dyadicChainingNetRadius (radiusScale : ℝ) (j : ℕ) : ℝ :=
  radiusScale / (2 : ℝ) ^ (j + 2)

/-- Positivity of the dyadic net radius under a positive top scale.
@isnad1 id=lt.1h2v.s4.cdf60852195c from=translated src=- shape=9141f3a7 vocab=e6d5fdfb
-/
theorem dyadicChainingNetRadius_pos {radiusScale : ℝ}
    (hradiusScale : 0 < radiusScale) (j : ℕ) :
    0 < dyadicChainingNetRadius radiusScale j := by
  unfold dyadicChainingNetRadius
  exact div_pos hradiusScale (pow_pos (by norm_num) _)

/-- Nonnegativity of the dyadic net radius under a nonnegative top scale.
@isnad1 id=le.1h2v.s4.4f7a69ef3096 from=translated src=- shape=9141f3a7 vocab=8f32a83b
-/
theorem dyadicChainingNetRadius_nonneg {radiusScale : ℝ}
    (hradiusScale : 0 ≤ radiusScale) (j : ℕ) :
    0 ≤ dyadicChainingNetRadius radiusScale j := by
  unfold dyadicChainingNetRadius
  exact div_nonneg hradiusScale (pow_pos (by norm_num) _).le

/-- Adjacent dyadic net radii fit inside the finite chaining radius budget.
@isnad1 id=le.1h2v.s6.3c840a9fb243 from=translated src=- shape=f9bb5800 vocab=161db782
-/
theorem dyadicChainingNetRadius_pair_sum_le {radiusScale : ℝ}
    (hradiusScale_nonneg : 0 ≤ radiusScale) (j : ℕ) :
    dyadicChainingNetRadius radiusScale j +
        dyadicChainingNetRadius radiusScale (j + 1) ≤
      radiusScale / (2 : ℝ) ^ j := by
  unfold dyadicChainingNetRadius
  have hrewrite1 : (2 : ℝ) ^ (j + 2) = (2 : ℝ) ^ j * 4 := by
    rw [pow_add]
    norm_num
  have hrewrite2 : (2 : ℝ) ^ (j + 1 + 2) = (2 : ℝ) ^ j * 8 := by
    have : j + 1 + 2 = j + 3 := by omega
    rw [this, pow_add]
    norm_num
  rw [hrewrite1, hrewrite2]
  have hbase_pos : 0 < (2 : ℝ) ^ j := pow_pos (by norm_num) _
  field_simp [hbase_pos.ne']
  nlinarith [hradiusScale_nonneg]

/-- The dyadic finite-net schedule extracted from total boundedness. -/
def dyadicChainingFiniteNetOfTotallyBoundedUniv
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    BundledFiniteNet T :=
  finiteNetOfTotallyBoundedUniv
    (T := T) hT (dyadicChainingNetRadius radiusScale j)
    (dyadicChainingNetRadius_pos hradiusScale j)

/-- The dyadic finite-net schedule has the expected radius at each scale.
@isnad1 id=eq.2h3v.s6.ed4f1e4ffd13 from=translated src=- shape=ca4f7769 vocab=0a1ea1d0
-/
@[simp] theorem dyadicChainingFiniteNetOfTotallyBoundedUniv_radius
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).net.radius =
      dyadicChainingNetRadius radiusScale j := by
  rfl

/-- The dyadic finite-net schedule uses the ambient metric distance.
@isnad1 id=eq.2h3v.s6.6e9234b7d676 from=translated src=- shape=87184d35 vocab=9dfa6165
-/
@[simp] theorem dyadicChainingFiniteNetOfTotallyBoundedUniv_dist
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).net.dist = fun s t => dist s t := by
  rfl

/-- Each dyadic finite net covers every index point at its scheduled radius.
@isnad1 id=le.2h4v.s6.cf4b624ef78c from=translated src=- shape=dcf309df vocab=30f1a853
-/
theorem dyadicChainingFiniteNetOfTotallyBoundedUniv_covers
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ)
    (t : T) :
    dist t
        ((dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale j).net.projection t) ≤
      dyadicChainingNetRadius radiusScale j := by
  unfold dyadicChainingFiniteNetOfTotallyBoundedUniv
  apply finiteNetOfTotallyBoundedUniv_covers

/-- Adjacent extracted dyadic nets satisfy the radius hypothesis expected by
the existing finite Dudley chaining theorems.
@isnad1 id=le.2h3v.s7.1cb2da22e7d6 from=translated src=- shape=0882dac8 vocab=83d204eb
-/
theorem dyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_le
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale j).net.radius +
      (dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale (j + 1)).net.radius ≤
      radiusScale / (2 : ℝ) ^ j := by
  simpa using
    dyadicChainingNetRadius_pair_sum_le
      (radiusScale := radiusScale) hradiusScale.le j

/-- Adjacent extracted dyadic nets have positive combined radius. This is the
finite positivity condition needed by the finite sub-Gaussian max bound at
each projected-chaining scale.
@isnad1 id=lt.2h3v.s7.c8e6f324c423 from=translated src=- shape=4a1ae90d vocab=b6b4c4f7
-/
theorem dyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_pos
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    0 <
      (dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale j).net.radius +
      (dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale (j + 1)).net.radius := by
  have hleft :
      0 <
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale j).net.radius := by
    simp [dyadicChainingNetRadius_pos hradiusScale j]
  have hright :
      0 ≤
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale (j + 1)).net.radius :=
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale (j + 1)).net.radius_nonneg
  linarith

/-! ## Projected dyadic wrapper -/

/-- Product of adjacent covering numbers for the pure total-bounded dyadic
schedule, without adding an identity terminal net.

This records the chosen finite covers at adjacent scales; it is not a minimal
covering-number claim. -/
def dyadicChainingCoverCount
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) : ℕ :=
  (dyadicChainingFiniteNetOfTotallyBoundedUniv
    (T := T) hT hradiusScale j).net.coveringNumber *
  (dyadicChainingFiniteNetOfTotallyBoundedUniv
    (T := T) hT hradiusScale (j + 1)).net.coveringNumber

/-- The concrete coarse budget used by the continuous covering-number corollary:
the expected finite supremum over the image of the coarsest dyadic net. -/
def dyadicChainingCoarseBudget
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) : ℝ :=
  finiteExpectation P.weight
    (fun ω => finiteSup
      (fun u : FiniteNet.ProjectedIndex
          (dyadicChainingFiniteNetOfTotallyBoundedUniv
            (T := T) hT hradiusScale 0).net =>
        P.X ω
          ((dyadicChainingFiniteNetOfTotallyBoundedUniv
            (T := T) hT hradiusScale 0).net.center u.1)))

/-- The terminal-scale coarse supremum is bounded by the level-0 projected
coarse supremum.
@isnad1 id=le.2h6v.s8.c145409b6fdd from=translated src=- shape=e843c25e vocab=90a2a216
-/
theorem dyadicChainingCoarseProjectedSup_le_levelZero
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale)
    (m : ℕ) (ω : Ω) :
    finiteSup
        (fun u : FiniteNet.ProjectedIndex
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale m).net =>
          P.X ω
            ((dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale 0).net.projection
              (FiniteNet.ProjectedIndex.source
                (dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net u))) ≤
      finiteSup
        (fun u : FiniteNet.ProjectedIndex
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale 0).net =>
          P.X ω
            ((dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale 0).net.center u.1)) := by
  classical
  let N₀ :=
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale 0).net
  let Nₘ :=
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale m).net
  unfold finiteSup
  apply Finset.sup'_le
  intro u _hu
  let v : FiniteNet.ProjectedIndex N₀ :=
    ⟨N₀.project (FiniteNet.ProjectedIndex.source Nₘ u),
      ⟨FiniteNet.ProjectedIndex.source Nₘ u, rfl⟩⟩
  have hv :
      P.X ω (N₀.center v.1) ≤
        (Finset.univ : Finset (FiniteNet.ProjectedIndex N₀)).sup'
          Finset.univ_nonempty
          (fun u : FiniteNet.ProjectedIndex N₀ => P.X ω (N₀.center u.1)) := by
    exact Finset.le_sup'
      (fun u : FiniteNet.ProjectedIndex N₀ => P.X ω (N₀.center u.1))
      (Finset.mem_univ v)
  simpa [N₀, Nₘ, v, FiniteNet.projection] using hv

/-- The concrete level-0 coarse budget dominates every terminal-scale coarse
projection budget in the dyadic total-bounded construction.
@isnad1 id=le.2h5v.s7.63b131dbaa08 from=translated src=- shape=0574db82 vocab=5030baa3
-/
theorem dyadicChainingCoarseBudget_bound
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale)
    (m : ℕ) :
    finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net =>
            P.X ω
              ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale 0).net.projection
                (FiniteNet.ProjectedIndex.source
                  (dyadicChainingFiniteNetOfTotallyBoundedUniv
                    (T := T) hT hradiusScale m).net u)))) ≤
      dyadicChainingCoarseBudget (T := T) P hT hradiusScale := by
  simpa [dyadicChainingCoarseBudget] using
    finiteExpectation_mono P.weight_nonneg
      (fun ω =>
        dyadicChainingCoarseProjectedSup_le_levelZero
          (T := T) P hT hradiusScale m ω)

/-- Twice the next dyadic radius is bounded by a quarter of the top scale.
@isnad1 id=le.1h2v.s6.a4a56050885e from=translated src=- shape=956d04c2 vocab=b8f71623
-/
theorem two_mul_dyadicChainingNetRadius_succ_le_quarter
    {radiusScale : ℝ} (hradiusScale : 0 ≤ radiusScale) (j : ℕ) :
    2 * dyadicChainingNetRadius radiusScale (j + 1) ≤ radiusScale / 4 := by
  unfold dyadicChainingNetRadius
  have hpow_ge : (4 : ℝ) ≤ (2 : ℝ) ^ (j + 2) := by
    have hpow : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ (j + 2) :=
      pow_le_pow_right₀ (by norm_num) (Nat.le_add_left 2 j)
    norm_num at hpow
    exact hpow
  have hden_pos : 0 < (2 : ℝ) ^ (j + 2) := pow_pos (by norm_num) _
  have hdiv :
      radiusScale / (2 : ℝ) ^ (j + 2) ≤ radiusScale / 4 :=
    div_le_div_of_nonneg_left hradiusScale (by norm_num) hpow_ge
  have hpow_succ :
      (2 : ℝ) ^ (j + 1 + 2) = (2 : ℝ) ^ (j + 2) * 2 := by
    have hnat : j + 1 + 2 = j + 2 + 1 := by omega
    rw [hnat, pow_succ]
  calc
    2 * (radiusScale / (2 : ℝ) ^ (j + 1 + 2))
        = radiusScale / (2 : ℝ) ^ (j + 2) := by
          rw [hpow_succ]
          field_simp [hden_pos.ne']
    _ ≤ radiusScale / 4 := hdiv

/-- Dichotomy for the top-scale separation hypothesis.

Either there is a pair separated by more than `radiusScale / 4`, which is the
nondegenerate branch used to produce nontrivial dyadic projection-pair
families, or every pair has distance at most `radiusScale / 4`, which is the
small-diameter branch needed for the later fallback theorem.
@isnad1 id=or.0h2v.s6.bfea288da482 from=translated src=- shape=95cc95e1 vocab=a4d42daf
-/
theorem radiusScale_quarter_separated_or_smallDiameter
    [PseudoMetricSpace T] (radiusScale : ℝ) :
    (∃ x y : T, radiusScale / 4 < dist x y) ∨
      (∀ x y : T, dist x y ≤ radiusScale / 4) := by
  classical
  by_cases hsep : ∃ x y : T, radiusScale / 4 < dist x y
  · exact Or.inl hsep
  · refine Or.inr ?_
    intro x y
    exact le_of_not_gt (fun hxy => hsep ⟨x, y, hxy⟩)

/-- Two points separated beyond twice the next dyadic radius give two realized
projection pairs at scale `j`.
@isnad1 id=lt.3h5v.s8.b9dd17e2282b from=translated src=- shape=55645f38 vocab=e0ba8fb2
-/
theorem dyadicChainingProjectionPair_card_gt_one_of_dist_gt_two_next_radius
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale)
    (x y : T) (j : ℕ)
    (hxy : 2 * dyadicChainingNetRadius radiusScale (j + 1) < dist x y) :
    1 < Fintype.card (FiniteNet.ProjectionPair
      (dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale j).net
      (dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale (j + 1)).net) := by
  classical
  let N₀ :=
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).net
  let N₁ :=
    (dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale (j + 1)).net
  refine Fintype.one_lt_card_iff.mpr
    ⟨FiniteNet.projectionPairOf N₀ N₁ x,
      FiniteNet.projectionPairOf N₀ N₁ y, ?_⟩
  intro hpair
  have hproj : N₁.project x = N₁.project y := by
    exact congrArg (fun p : FiniteNet.ProjectionPair N₀ N₁ => p.1.2) hpair
  have hcenter : N₁.projection x = N₁.projection y := by
    simp [FiniteNet.projection, hproj]
  have hx : dist x (N₁.projection x) ≤ N₁.radius := by
    simpa [N₁] using N₁.projection_dist_le x
  have hy : dist y (N₁.projection y) ≤ N₁.radius := by
    simpa [N₁] using N₁.projection_dist_le y
  have hxy_le : dist x y ≤ N₁.radius + N₁.radius := by
    calc
      dist x y ≤ dist x (N₁.projection x) + dist (N₁.projection x) y :=
        dist_triangle x (N₁.projection x) y
      _ = dist x (N₁.projection x) + dist (N₁.projection y) y := by
        rw [hcenter]
      _ = dist x (N₁.projection x) + dist y (N₁.projection y) := by
        rw [dist_comm (N₁.projection y) y]
      _ ≤ N₁.radius + N₁.radius := add_le_add hx hy
  have hrad :
      N₁.radius = dyadicChainingNetRadius radiusScale (j + 1) := by
    simp [N₁]
  have hxy_le' : dist x y ≤ 2 * dyadicChainingNetRadius radiusScale (j + 1) := by
    rw [hrad] at hxy_le
    linarith
  exact not_lt_of_ge hxy_le' hxy

/-- A top-scale separated pair gives nontrivial realized projection-pair families
at every dyadic scale.
@isnad1 id=lt.3h5v.s8.6482dd755dd5 from=translated src=- shape=420ef17a vocab=3cb91e04
-/
theorem dyadicChainingProjectionPair_card_gt_one_of_radiusScale_quarter_lt_dist
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale)
    {x y : T} (hxy : radiusScale / 4 < dist x y) :
    ∀ j : ℕ,
      1 < Fintype.card (FiniteNet.ProjectionPair
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale j).net
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale (j + 1)).net) := by
  intro j
  have htwo :
      2 * dyadicChainingNetRadius radiusScale (j + 1) < dist x y :=
    lt_of_le_of_lt
      (two_mul_dyadicChainingNetRadius_succ_le_quarter
        (radiusScale := radiusScale) hradiusScale.le j)
      hxy
  exact dyadicChainingProjectionPair_card_gt_one_of_dist_gt_two_next_radius
    (T := T) hT hradiusScale x y j htwo

/-- The concrete eventual finite-scale obligations for the dyadic
total-bounded construction.

The cardinality side is built from a separated pair at the top scale. The coarse
side is bounded by the level-0 projected finite supremum budget.
@isnad1 id=eventual.3h4v.s8.f083c68f0129 from=translated src=- shape=60fb2df9 vocab=d8b48d25
-/
theorem dyadicChaining_eventual_card_coarse_obligations
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale)
    (hseparated : ∃ x y : T, radiusScale / 4 < dist x y) :
    ∀ᶠ m : ℕ in Filter.atTop,
        (∀ j ∈ Finset.range m,
          1 < Fintype.card (FiniteNet.ProjectionPair
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale j).net
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale (j + 1)).net)) ∧
        (finiteExpectation P.weight
          (fun ω => finiteSup
            (fun u : FiniteNet.ProjectedIndex
                (dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net =>
              P.X ω
                ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale 0).net.projection
                  (FiniteNet.ProjectedIndex.source
                    (dyadicChainingFiniteNetOfTotallyBoundedUniv
                      (T := T) hT hradiusScale m).net u)))) ≤
          dyadicChainingCoarseBudget (T := T) P hT hradiusScale) := by
  rcases hseparated with ⟨x, y, hxy⟩
  have hcard_all :
      ∀ j : ℕ,
        1 < Fintype.card (FiniteNet.ProjectionPair
          (dyadicChainingFiniteNetOfTotallyBoundedUniv
            (T := T) hT hradiusScale j).net
          (dyadicChainingFiniteNetOfTotallyBoundedUniv
            (T := T) hT hradiusScale (j + 1)).net) :=
    dyadicChainingProjectionPair_card_gt_one_of_radiusScale_quarter_lt_dist
      (T := T) hT hradiusScale hxy
  exact Filter.Eventually.of_forall
    (fun m =>
      ⟨(fun j _hj => hcard_all j),
        dyadicChainingCoarseBudget_bound (T := T) P hT hradiusScale m⟩)

/-- The concrete eventual coarse-budget obligation for the dyadic total-bounded
construction, without any nontrivial projection-pair cardinality requirement.
@isnad1 id=eventual.2h4v.s7.d324eaea38ef from=translated src=- shape=c10d835c vocab=5b7e356f
-/
theorem dyadicChaining_eventual_coarse_obligations
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) :
    ∀ᶠ m : ℕ in Filter.atTop,
        finiteExpectation P.weight
          (fun ω => finiteSup
            (fun u : FiniteNet.ProjectedIndex
                (dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net =>
              P.X ω
                ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale 0).net.projection
                  (FiniteNet.ProjectedIndex.source
                    (dyadicChainingFiniteNetOfTotallyBoundedUniv
                      (T := T) hT hradiusScale m).net u)))) ≤
          dyadicChainingCoarseBudget (T := T) P hT hradiusScale := by
  exact Filter.Eventually.of_forall
    (fun m => dyadicChainingCoarseBudget_bound (T := T) P hT hradiusScale m)

/-- Total-bounded dyadic finite-net schedule packaged as a reusable
`FiniteDyadicNetSequence`.

The caller supplies the global nontrivial projection-pair cardinality
hypothesis. The existing total-bounded wrappers only need this on
`Finset.range m`; this packaged object is deliberately stronger because it is
intended for examples or APIs that want one reusable all-scale sequence. -/
def dyadicChainingFiniteNetSequenceOfTotallyBounded
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hcard : ∀ j : ℕ,
      1 < Fintype.card
        (FiniteNet.ProjectionPair
          (dyadicChainingFiniteNetOfTotallyBoundedUniv
            (T := T) hT hradiusScale j).net
          (dyadicChainingFiniteNetOfTotallyBoundedUniv
            (T := T) hT hradiusScale (j + 1)).net)) :
    FiniteSubGaussianProcess.FiniteDyadicNetSequence P
      (fun j : ℕ =>
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale j).A) where
  N := fun j => (dyadicChainingFiniteNetOfTotallyBoundedUniv
    (T := T) hT hradiusScale j).net
  coverCount := fun j => dyadicChainingCoverCount (T := T) hT hradiusScale j
  radiusScale := radiusScale
  dist_eq := by
    intro j
    rw [dyadicChainingFiniteNetOfTotallyBoundedUniv_dist, hdistP]
  dist_symm := by
    intro s t
    rw [hdistP]
    exact dist_comm s t
  dist_triangle := by
    intro x y z
    rw [hdistP]
    exact dist_triangle x y z
  radiusScale_nonneg := hradiusScale.le
  radius_pos := by
    intro j
    exact dyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_pos
      (T := T) hT hradiusScale j
  radius_geometric := by
    intro j
    exact dyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_le
      (T := T) hT hradiusScale j
  pair_card_gt_one := hcard
  coverCount_le := by
    intro j
    rfl

/-- Total-bounded dyadic finite-net schedule packaged as a reusable
`FiniteDyadicDudleyInstance`.

This is the bridge from the total-bounded boundary layer to the packaged finite
Dudley API. It intentionally requires a global coarse projected-supremum budget;
single-scale total-bounded wrappers keep their older direct theorem shape. -/
def finiteDyadicDudleyInstanceOfTotallyBounded
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale)
    (coarseBudget : ℝ)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hcard : ∀ j : ℕ,
      1 < Fintype.card
        (FiniteNet.ProjectionPair
          (dyadicChainingFiniteNetOfTotallyBoundedUniv
            (T := T) hT hradiusScale j).net
          (dyadicChainingFiniteNetOfTotallyBoundedUniv
            (T := T) hT hradiusScale (j + 1)).net))
    (hcoarse : ∀ m : ℕ,
      finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net =>
            P.X ω
              ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale 0).net.projection
                (FiniteNet.ProjectedIndex.source
                  (dyadicChainingFiniteNetOfTotallyBoundedUniv
                    (T := T) hT hradiusScale m).net u)))) ≤
        coarseBudget) :
    FiniteSubGaussianProcess.FiniteDyadicDudleyInstance P
      (fun j : ℕ =>
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale j).A) where
  netSequence :=
    dyadicChainingFiniteNetSequenceOfTotallyBounded
      P hT hradiusScale hdistP hcard
  coarseBudget := coarseBudget
  variance_pos := hvariance
  coarse_bound := hcoarse

/-- A finite skeleton and terminal-scale certificate for an epsilonized
total-bounded Dudley boundary step.

For a requested error budget `eta` and dyadic terminal scale `m`, this predicate
packages exactly the data needed by
`finite_witnessedSup_modulus_dudley_totalBounded_dyadic_entropy_truncatedIntervalIntegral_comparison`:
a finite skeleton, approximate maximizers for the supplied supremum functional,
a finite-skeleton selector, a pathwise terminal modulus, the finite entropy
side conditions at scale `m`, and a total approximation-error budget bounded by
`eta`.

The predicate is intentionally finite and explicit. It does not assert
separability, construct arbitrary measurable suprema, or claim a continuous
Dudley theorem.
-/
def EpsilonizedSupremumBoundaryChoice
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    (eta : ℝ) (m : ℕ) : Prop :=
  ∃ (K : Type u), ∃ (_instK : Fintype K), ∃ (_nonemptyK : Nonempty K),
  ∃ (embed : K → T), ∃ (nearest : T → K), ∃ (witness : Ω → T),
  ∃ (witnessError : ℝ), ∃ (skeletonError : ℝ), ∃ (terminalError : ℝ),
    witnessError + skeletonError + terminalError ≤ eta ∧
    (∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale j).net
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale (j + 1)).net)) ∧
    (∀ j ∈ Finset.range m,
      FiniteSubGaussianProcess.finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log
            (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
    (∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
    (∀ ω : Ω,
      supFunctional ω ≤ P.X ω (witness ω) + witnessError) ∧
    (∀ ω : Ω, ∀ t : T,
      P.X ω t ≤ P.X ω (embed (nearest t)) + skeletonError) ∧
    (∀ ω : Ω, ∀ s t : T,
      dist s t ≤ dyadicChainingNetRadius radiusScale m →
        P.X ω s ≤ P.X ω t + terminalError) ∧
    (finiteExpectation P.weight
      (fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale m).net =>
          P.X ω
            ((dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale 0).net.projection
              (FiniteNet.ProjectedIndex.source
                (dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net u)))) ≤
      coarseBudget m)

/-- Singleton-safe finite skeleton and terminal-scale certificate for an
epsilonized total-bounded Dudley boundary step.

This is the no-cardinality variant of `EpsilonizedSupremumBoundaryChoice`; the
finite chaining layer below uses covering numbers and nonempty finite families. -/
def EpsilonizedSupremumBoundaryChoiceNonempty
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    (eta : ℝ) (m : ℕ) : Prop :=
  ∃ (K : Type u), ∃ (_instK : Fintype K), ∃ (_nonemptyK : Nonempty K),
  ∃ (embed : K → T), ∃ (nearest : T → K), ∃ (witness : Ω → T),
  ∃ (witnessError : ℝ), ∃ (skeletonError : ℝ), ∃ (terminalError : ℝ),
    witnessError + skeletonError + terminalError ≤ eta ∧
    (∀ j ∈ Finset.range m,
      FiniteSubGaussianProcess.finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log
            (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
    (∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
    (∀ ω : Ω,
      supFunctional ω ≤ P.X ω (witness ω) + witnessError) ∧
    (∀ ω : Ω, ∀ t : T,
      P.X ω t ≤ P.X ω (embed (nearest t)) + skeletonError) ∧
    (∀ ω : Ω, ∀ s t : T,
      dist s t ≤ dyadicChainingNetRadius radiusScale m →
        P.X ω s ≤ P.X ω t + terminalError) ∧
    (finiteExpectation P.weight
      (fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale m).net =>
          P.X ω
            ((dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale 0).net.projection
              (FiniteNet.ProjectedIndex.source
                (dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net u)))) ≤
      coarseBudget m)

/-- A finite-cover skeleton gives the skeleton approximation required by the
epsilonized boundary certificate when sample paths have a one-sided modulus at
the cover radius.

This is the elementary bridge from finite-cover geometry to the finite-skeleton
assumption used by the Dudley boundary adapter.
@isnad1 id=le.2h10v.s6.d8dc99bcc5e1 from=translated src=- shape=411608b2 vocab=1f82c410
-/
lemma skeletonApprox_of_finiteCover_pathwiseModulus
    {Ω : Type*} {K : Type u}
    [Fintype Ω] [PseudoMetricSpace T]
    (P : FiniteSubGaussianProcess Ω T)
    (embed : K → T) (nearest : T → K)
    (skeletonRadius skeletonError : ℝ)
    (hcover : ∀ t : T, dist t (embed (nearest t)) ≤ skeletonRadius)
    (hmodulus : ∀ ω : Ω, ∀ s t : T,
      dist s t ≤ skeletonRadius → P.X ω s ≤ P.X ω t + skeletonError) :
    ∀ ω : Ω, ∀ t : T,
      P.X ω t ≤ P.X ω (embed (nearest t)) + skeletonError := by
  intro ω t
  exact hmodulus ω t (embed (nearest t)) (hcover t)

/-- A finite-cover/pathwise-modulus certificate for the epsilonized
total-bounded Dudley boundary step.

Compared with `EpsilonizedSupremumBoundaryChoice`, this predicate exposes the
recognizable continuous-boundary hypotheses:
* a finite skeleton and nearest-skeleton selector;
* a finite-cover radius for the selector;
* a pathwise modulus at that finite-cover radius;
* approximate witnesses for the supplied supremum functional;
* a terminal pathwise modulus at the dyadic terminal scale.

It remains a finite-choice certificate. It does not construct a dense sequence,
prove separability, construct arbitrary measurable suprema, or claim the full
continuous Dudley theorem.
-/
def FiniteCoverSupremumBoundaryChoice
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    (eta : ℝ) (m : ℕ) : Prop :=
  ∃ (K : Type u), ∃ (_instK : Fintype K), ∃ (_nonemptyK : Nonempty K),
  ∃ (embed : K → T), ∃ (nearest : T → K), ∃ (witness : Ω → T),
  ∃ (witnessError : ℝ), ∃ (skeletonRadius : ℝ),
  ∃ (skeletonError : ℝ), ∃ (terminalError : ℝ),
    witnessError + skeletonError + terminalError ≤ eta ∧
    (∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale j).net
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale (j + 1)).net)) ∧
    (∀ j ∈ Finset.range m,
      FiniteSubGaussianProcess.finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log
            (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
    (∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
    (∀ t : T, dist t (embed (nearest t)) ≤ skeletonRadius) ∧
    (∀ ω : Ω, ∀ s t : T,
      dist s t ≤ skeletonRadius →
        P.X ω s ≤ P.X ω t + skeletonError) ∧
    (∀ ω : Ω,
      supFunctional ω ≤ P.X ω (witness ω) + witnessError) ∧
    (∀ ω : Ω, ∀ s t : T,
      dist s t ≤ dyadicChainingNetRadius radiusScale m →
        P.X ω s ≤ P.X ω t + terminalError) ∧
    (finiteExpectation P.weight
      (fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale m).net =>
          P.X ω
            ((dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale 0).net.projection
              (FiniteNet.ProjectedIndex.source
                (dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net u)))) ≤
              coarseBudget m)

/-- Singleton-safe finite-cover/pathwise-modulus certificate for the
epsilonized total-bounded Dudley boundary step. -/
def FiniteCoverSupremumBoundaryChoiceNonempty
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    (eta : ℝ) (m : ℕ) : Prop :=
  ∃ (K : Type u), ∃ (_instK : Fintype K), ∃ (_nonemptyK : Nonempty K),
  ∃ (embed : K → T), ∃ (nearest : T → K), ∃ (witness : Ω → T),
  ∃ (witnessError : ℝ), ∃ (skeletonRadius : ℝ),
  ∃ (skeletonError : ℝ), ∃ (terminalError : ℝ),
    witnessError + skeletonError + terminalError ≤ eta ∧
    (∀ j ∈ Finset.range m,
      FiniteSubGaussianProcess.finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log
            (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
    (∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
    (∀ t : T, dist t (embed (nearest t)) ≤ skeletonRadius) ∧
    (∀ ω : Ω, ∀ s t : T,
      dist s t ≤ skeletonRadius →
        P.X ω s ≤ P.X ω t + skeletonError) ∧
    (∀ ω : Ω,
      supFunctional ω ≤ P.X ω (witness ω) + witnessError) ∧
    (∀ ω : Ω, ∀ s t : T,
      dist s t ≤ dyadicChainingNetRadius radiusScale m →
        P.X ω s ≤ P.X ω t + terminalError) ∧
    (finiteExpectation P.weight
      (fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale m).net =>
          P.X ω
            ((dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale 0).net.projection
              (FiniteNet.ProjectedIndex.source
                (dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net u)))) ≤
      coarseBudget m)

/-- A finite-cover/pathwise-modulus certificate produces the epsilonized
supremum-boundary certificate used by the Dudley adapter.

This theorem is the reusable finite-cover bridge: finite-cover geometry plus
pathwise modulus discharges the explicit finite-skeleton approximation
hypothesis in `EpsilonizedSupremumBoundaryChoice`.
@isnad1 id=epsiloni.3h9v.s6.75c5a1a2d111 from=translated src=- shape=50ec1f20 vocab=594920e3
-/
theorem epsilonizedSupremumBoundaryChoice_of_finiteCoverSupremumBoundaryChoice
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    {eta : ℝ} {m : ℕ}
    (hchoice :
      FiniteCoverSupremumBoundaryChoice
        (P := P) (hT := hT) (coarseBudget := coarseBudget)
        (radiusScale := radiusScale) (hradiusScale := hradiusScale)
        (entropyAtRadius := entropyAtRadius)
        (supFunctional := supFunctional) eta m) :
    EpsilonizedSupremumBoundaryChoice
      (P := P) (hT := hT) (coarseBudget := coarseBudget)
      (radiusScale := radiusScale) (hradiusScale := hradiusScale)
      (entropyAtRadius := entropyAtRadius)
      (supFunctional := supFunctional) eta m := by
  rcases hchoice with
    ⟨K, instK, nonemptyK, embed, nearest, witness,
      witnessError, skeletonRadius, skeletonError, terminalError,
      herror, hcard, hentropyAtRadius, hintervalIntegrable, hcover,
      hskeletonModulus, hwitness, hterminalModulus, hcoarse⟩
  letI : Fintype K := instK
  letI : Nonempty K := nonemptyK
  refine ⟨K, instK, nonemptyK, embed, nearest, witness,
    witnessError, skeletonError, terminalError, herror, hcard,
    hentropyAtRadius, hintervalIntegrable, hwitness, ?_, hterminalModulus,
    hcoarse⟩
  exact skeletonApprox_of_finiteCover_pathwiseModulus
    (P := P) embed nearest skeletonRadius skeletonError hcover
    hskeletonModulus

/-- Singleton-safe finite-cover bridge into the epsilonized boundary
certificate.
@isnad1 id=epsiloni.3h9v.s6.f2cbd97e9526 from=translated src=- shape=50ec1f20 vocab=293f4b6b
-/
theorem epsilonizedSupremumBoundaryChoiceNonempty_of_finiteCoverSupremumBoundaryChoiceNonempty
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    {eta : ℝ} {m : ℕ}
    (hchoice :
      FiniteCoverSupremumBoundaryChoiceNonempty
        (P := P) (hT := hT) (coarseBudget := coarseBudget)
        (radiusScale := radiusScale) (hradiusScale := hradiusScale)
        (entropyAtRadius := entropyAtRadius)
        (supFunctional := supFunctional) eta m) :
    EpsilonizedSupremumBoundaryChoiceNonempty
      (P := P) (hT := hT) (coarseBudget := coarseBudget)
      (radiusScale := radiusScale) (hradiusScale := hradiusScale)
      (entropyAtRadius := entropyAtRadius)
      (supFunctional := supFunctional) eta m := by
  rcases hchoice with
    ⟨K, instK, nonemptyK, embed, nearest, witness,
      witnessError, skeletonRadius, skeletonError, terminalError,
      herror, hentropyAtRadius, hintervalIntegrable, hcover,
      hskeletonModulus, hwitness, hterminalModulus, hcoarse⟩
  letI : Fintype K := instK
  letI : Nonempty K := nonemptyK
  refine ⟨K, instK, nonemptyK, embed, nearest, witness,
    witnessError, skeletonError, terminalError, herror,
    hentropyAtRadius, hintervalIntegrable, hwitness, ?_, hterminalModulus,
    hcoarse⟩
  exact skeletonApprox_of_finiteCover_pathwiseModulus
    (P := P) embed nearest skeletonRadius skeletonError hcover
    hskeletonModulus

/-- Real-order closure for epsilonized upper bounds.

If `x` is at most `y + eta` for every positive `eta`, then `x ≤ y`.
This small analytic adapter is the final bookkeeping step used to remove the
explicit boundary error from epsilonized Dudley statements under a uniform
finite-budget hypothesis.
@isnad1 id=le.1h2v.s5.2ee79f5afcc4 from=translated src=- shape=aca71d2c vocab=91bdb49a
-/
lemma le_of_forall_pos_le_add {x y : ℝ}
    (h : ∀ eta : ℝ, 0 < eta → x ≤ y + eta) :
    x ≤ y := by
  by_contra hxy
  have hyx : y < x := lt_of_not_ge hxy
  have heta : 0 < (x - y) / 2 := by
    linarith
  have hxle := h ((x - y) / 2) heta
  linarith

/-- A separability/terminal-projection certificate for the epsilonized
total-bounded Dudley boundary step.

Compared with `EpsilonizedSupremumBoundaryChoice`, this predicate exposes the
cleaner boundary hypotheses used in continuous Dudley arguments:
* a finite skeleton `K` embedded in the index space;
* a supplied supremum functional bounded by that finite skeleton up to a
  separability error;
* terminal dyadic projection approximation on that skeleton;
* finite entropy side conditions and a coarse-scale projected budget.

It is still a finite-choice boundary certificate. It does not construct an
arbitrary measurable supremum, prove separability from a dense sequence, or
claim the full continuous Dudley theorem.
-/
def SeparableTerminalSupremumBoundaryChoice
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    (eta : ℝ) (m : ℕ) : Prop :=
  ∃ (K : Type u), ∃ (_instK : Fintype K), ∃ (_nonemptyK : Nonempty K),
  ∃ (embed : K → T), ∃ (separabilityError : ℝ), ∃ (terminalError : ℝ),
    separabilityError + terminalError ≤ eta ∧
    (∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale j).net
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale (j + 1)).net)) ∧
    (∀ j ∈ Finset.range m,
      FiniteSubGaussianProcess.finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log
            (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
    (∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
    (∀ ω : Ω,
      supFunctional ω ≤
        finiteSup (fun k : K => P.X ω (embed k)) + separabilityError) ∧
    (∀ ω : Ω, ∀ k : K,
      P.X ω (embed k) ≤
        P.X ω
          ((dyadicChainingFiniteNetOfTotallyBoundedUniv
            (T := T) hT hradiusScale m).net.projection (embed k)) +
          terminalError) ∧
    (finiteExpectation P.weight
      (fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale m).net =>
          P.X ω
            ((dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale 0).net.projection
              (FiniteNet.ProjectedIndex.source
                (dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net u)))) ≤
              coarseBudget m)

/-- Singleton-safe separability/terminal-projection certificate for the
epsilonized total-bounded Dudley boundary step. -/
def SeparableTerminalSupremumBoundaryChoiceNonempty
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    (eta : ℝ) (m : ℕ) : Prop :=
  ∃ (K : Type u), ∃ (_instK : Fintype K), ∃ (_nonemptyK : Nonempty K),
  ∃ (embed : K → T), ∃ (separabilityError : ℝ), ∃ (terminalError : ℝ),
    separabilityError + terminalError ≤ eta ∧
    (∀ j ∈ Finset.range m,
      FiniteSubGaussianProcess.finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log
            (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
    (∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
    (∀ ω : Ω,
      supFunctional ω ≤
        finiteSup (fun k : K => P.X ω (embed k)) + separabilityError) ∧
    (∀ ω : Ω, ∀ k : K,
      P.X ω (embed k) ≤
        P.X ω
          ((dyadicChainingFiniteNetOfTotallyBoundedUniv
            (T := T) hT hradiusScale m).net.projection (embed k)) +
          terminalError) ∧
    (finiteExpectation P.weight
      (fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex
            (dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale m).net =>
          P.X ω
            ((dyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale 0).net.projection
              (FiniteNet.ProjectedIndex.source
                (dyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net u)))) ≤
      coarseBudget m)

/-- A pathwise terminal modulus discharges the terminal-projection
approximation required by the separable Dudley boundary certificate.

The terminal dyadic net already covers every skeleton point at radius
`dyadicChainingNetRadius radiusScale m`; this lemma packages the direct
one-sided continuity/modulus step needed to move from a skeleton point to its
terminal projection.
@isnad1 id=le.3h10v.s7.4efadf7ae6cc from=translated src=- shape=4094b735 vocab=29fbce89
-/
lemma terminalApprox_of_pathwiseTerminalModulus
    {Ω : Type*} {K : Type u} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (radiusScale terminalError : ℝ)
    (hradiusScale : 0 < radiusScale) (m : ℕ)
    (embed : K → T)
    (hmodulus : ∀ ω : Ω, ∀ s t : T,
      dist s t ≤ dyadicChainingNetRadius radiusScale m →
        P.X ω s ≤ P.X ω t + terminalError) :
    ∀ ω : Ω, ∀ k : K,
      P.X ω (embed k) ≤
        P.X ω
          ((dyadicChainingFiniteNetOfTotallyBoundedUniv
            (T := T) hT hradiusScale m).net.projection (embed k)) +
          terminalError := by
  intro ω k
  exact hmodulus ω (embed k)
    ((dyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale m).net.projection (embed k))
    (dyadicChainingFiniteNetOfTotallyBoundedUniv_covers
      (T := T) hT hradiusScale m (embed k))

/-- Build a separability/terminal-projection Dudley boundary certificate from
explicit finite-skeleton and pathwise terminal-modulus hypotheses.

This constructor is the clean boundary interface used on the path toward
continuous Dudley: a finite skeleton controls the supplied supremum functional,
and a pathwise terminal modulus controls projection to the terminal dyadic net.
It is still a finite certificate, not a theorem about arbitrary measurable
suprema or separability by itself.
@isnad1 id=separabl.9h13v.s9.fe67ad39270f from=translated src=- shape=6ada3aa3 vocab=6fe5e583
-/
theorem separableTerminalSupremumBoundaryChoice_of_pathwiseTerminalModulus
    {Ω : Type*} [Fintype Ω]
    {K : Type u} [Fintype K] [Nonempty K]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    {eta : ℝ} {m : ℕ}
    (embed : K → T)
    (separabilityError terminalError : ℝ)
    (herror : separabilityError + terminalError ≤ eta)
    (hcard : ∀ j ∈ Finset.range m,
      1 < Fintype.card (FiniteNet.ProjectionPair
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale j).net
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale (j + 1)).net))
    (hentropyAtRadius : ∀ j ∈ Finset.range m,
      FiniteSubGaussianProcess.finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log
            (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hintervalIntegrable : ∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hseparable :
      ∀ ω : Ω,
        supFunctional ω ≤
          finiteSup (fun k : K => P.X ω (embed k)) + separabilityError)
    (hterminalModulus : ∀ ω : Ω, ∀ s t : T,
      dist s t ≤ dyadicChainingNetRadius radiusScale m →
        P.X ω s ≤ P.X ω t + terminalError)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net =>
            P.X ω
              ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale 0).net.projection
                (FiniteNet.ProjectedIndex.source
                  (dyadicChainingFiniteNetOfTotallyBoundedUniv
                    (T := T) hT hradiusScale m).net u)))) ≤
      coarseBudget m) :
    SeparableTerminalSupremumBoundaryChoice
      (P := P) (hT := hT) (coarseBudget := coarseBudget)
      (radiusScale := radiusScale) (hradiusScale := hradiusScale)
      (entropyAtRadius := entropyAtRadius)
      (supFunctional := supFunctional) eta m := by
  refine ⟨K, inferInstance, inferInstance, embed, separabilityError,
    terminalError, herror, hcard, hentropyAtRadius, hintervalIntegrable,
    hseparable, ?_, hcoarse⟩
  exact terminalApprox_of_pathwiseTerminalModulus
    (P := P) (hT := hT) (radiusScale := radiusScale)
    (terminalError := terminalError) (hradiusScale := hradiusScale)
    (m := m) (embed := embed) hterminalModulus

/-- Singleton-safe constructor for separability/terminal-projection Dudley
boundary certificates from pathwise terminal modulus.
@isnad1 id=separabl.8h13v.s9.b5662fc567c1 from=translated src=- shape=80980ffe vocab=eeafb5a5
-/
theorem separableTerminalSupremumBoundaryChoiceNonempty_of_pathwiseTerminalModulus
    {Ω : Type*} [Fintype Ω]
    {K : Type u} [Fintype K] [Nonempty K]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    {eta : ℝ} {m : ℕ}
    (embed : K → T)
    (separabilityError terminalError : ℝ)
    (herror : separabilityError + terminalError ≤ eta)
    (hentropyAtRadius : ∀ j ∈ Finset.range m,
      FiniteSubGaussianProcess.finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log
            (dyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hintervalIntegrable : ∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hseparable :
      ∀ ω : Ω,
        supFunctional ω ≤
          finiteSup (fun k : K => P.X ω (embed k)) + separabilityError)
    (hterminalModulus : ∀ ω : Ω, ∀ s t : T,
      dist s t ≤ dyadicChainingNetRadius radiusScale m →
        P.X ω s ≤ P.X ω t + terminalError)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net =>
            P.X ω
              ((dyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale 0).net.projection
                (FiniteNet.ProjectedIndex.source
                  (dyadicChainingFiniteNetOfTotallyBoundedUniv
                    (T := T) hT hradiusScale m).net u)))) ≤
      coarseBudget m) :
    SeparableTerminalSupremumBoundaryChoiceNonempty
      (P := P) (hT := hT) (coarseBudget := coarseBudget)
      (radiusScale := radiusScale) (hradiusScale := hradiusScale)
      (entropyAtRadius := entropyAtRadius)
      (supFunctional := supFunctional) eta m := by
  refine ⟨K, inferInstance, inferInstance, embed, separabilityError,
    terminalError, herror, hentropyAtRadius, hintervalIntegrable,
    hseparable, ?_, hcoarse⟩
  exact terminalApprox_of_pathwiseTerminalModulus
    (P := P) (hT := hT) (radiusScale := radiusScale)
    (terminalError := terminalError) (hradiusScale := hradiusScale)
    (m := m) (embed := embed) hterminalModulus

/-- A finite-cover/pathwise-modulus certificate also gives the cleaner
separability/terminal-projection certificate.

This bridges the usable finite-cover hypotheses in
`FiniteCoverSupremumBoundaryChoice` to the more continuous-looking
`SeparableTerminalSupremumBoundaryChoice` interface. The finite cover and
pathwise modulus discharge the separability error; the terminal dyadic modulus
discharges terminal projection on the finite skeleton.

The result is still a finite-choice boundary adapter. It does not construct an
arbitrary measurable supremum, prove separability from a dense sequence, or
claim a continuous Dudley theorem.
@isnad1 id=separabl.3h9v.s6.0a384f594f10 from=translated src=- shape=50ec1f20 vocab=6707baa0
-/
theorem separableTerminalSupremumBoundaryChoice_of_finiteCoverSupremumBoundaryChoice
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    {eta : ℝ} {m : ℕ}
    (hchoice :
      FiniteCoverSupremumBoundaryChoice
        (P := P) (hT := hT) (coarseBudget := coarseBudget)
        (radiusScale := radiusScale) (hradiusScale := hradiusScale)
        (entropyAtRadius := entropyAtRadius)
        (supFunctional := supFunctional) eta m) :
    SeparableTerminalSupremumBoundaryChoice
      (P := P) (hT := hT) (coarseBudget := coarseBudget)
      (radiusScale := radiusScale) (hradiusScale := hradiusScale)
      (entropyAtRadius := entropyAtRadius)
      (supFunctional := supFunctional) eta m := by
  rcases hchoice with
    ⟨K, instK, nonemptyK, embed, nearest, witness,
      witnessError, skeletonRadius, skeletonError, terminalError,
      herror, hcard, hentropyAtRadius, hintervalIntegrable, hcover,
      hskeletonModulus, hwitness, hterminalModulus, hcoarse⟩
  letI : Fintype K := instK
  letI : Nonempty K := nonemptyK
  have hskeletonApprox :
      ∀ ω : Ω, ∀ t : T,
        P.X ω t ≤ P.X ω (embed (nearest t)) + skeletonError :=
    skeletonApprox_of_finiteCover_pathwiseModulus
      (P := P) embed nearest skeletonRadius skeletonError hcover
      hskeletonModulus
  refine ⟨K, instK, nonemptyK, embed, witnessError + skeletonError,
    terminalError, ?_, hcard, hentropyAtRadius, hintervalIntegrable, ?_,
    ?_, hcoarse⟩
  · simpa [add_assoc] using herror
  · exact supFunctional_le_skeletonSup_add_of_witnessed_pointwise_approx
      (embed := embed) (nearest := nearest) (Y := P.X)
      (supFunctional := supFunctional) (witness := witness)
      (witnessError := witnessError) (skeletonError := skeletonError)
      hwitness hskeletonApprox
  · intro ω k
    exact hterminalModulus ω (embed k)
      ((dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale m).net.projection (embed k))
      (dyadicChainingFiniteNetOfTotallyBoundedUniv_covers
        (T := T) hT hradiusScale m (embed k))

/-- Singleton-safe finite-cover bridge to the separability/terminal-projection
certificate.
@isnad1 id=separabl.3h9v.s6.7df3d4591d6c from=translated src=- shape=50ec1f20 vocab=0fe623ed
-/
theorem separableTerminalSupremumBoundaryChoiceNonempty_of_finiteCoverSupremumBoundaryChoiceNonempty
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    {eta : ℝ} {m : ℕ}
    (hchoice :
      FiniteCoverSupremumBoundaryChoiceNonempty
        (P := P) (hT := hT) (coarseBudget := coarseBudget)
        (radiusScale := radiusScale) (hradiusScale := hradiusScale)
        (entropyAtRadius := entropyAtRadius)
        (supFunctional := supFunctional) eta m) :
    SeparableTerminalSupremumBoundaryChoiceNonempty
      (P := P) (hT := hT) (coarseBudget := coarseBudget)
      (radiusScale := radiusScale) (hradiusScale := hradiusScale)
      (entropyAtRadius := entropyAtRadius)
      (supFunctional := supFunctional) eta m := by
  rcases hchoice with
    ⟨K, instK, nonemptyK, embed, nearest, witness,
      witnessError, skeletonRadius, skeletonError, terminalError,
      herror, hentropyAtRadius, hintervalIntegrable, hcover,
      hskeletonModulus, hwitness, hterminalModulus, hcoarse⟩
  letI : Fintype K := instK
  letI : Nonempty K := nonemptyK
  have hskeletonApprox :
      ∀ ω : Ω, ∀ t : T,
        P.X ω t ≤ P.X ω (embed (nearest t)) + skeletonError :=
    skeletonApprox_of_finiteCover_pathwiseModulus
      (P := P) embed nearest skeletonRadius skeletonError hcover
      hskeletonModulus
  refine ⟨K, instK, nonemptyK, embed, witnessError + skeletonError,
    terminalError, ?_, hentropyAtRadius, hintervalIntegrable, ?_,
    ?_, hcoarse⟩
  · simpa [add_assoc] using herror
  · exact supFunctional_le_skeletonSup_add_of_witnessed_pointwise_approx
      (embed := embed) (nearest := nearest) (Y := P.X)
      (supFunctional := supFunctional) (witness := witness)
      (witnessError := witnessError) (skeletonError := skeletonError)
      hwitness hskeletonApprox
  · intro ω k
    exact hterminalModulus ω (embed k)
      ((dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale m).net.projection (embed k))
      (dyadicChainingFiniteNetOfTotallyBoundedUniv_covers
        (T := T) hT hradiusScale m (embed k))

/-! ## Finite terminal dyadic wrapper -/

/-- Center type used by the finite terminal dyadic wrapper.

The second component carries the total-bounded dyadic net at scale `j`; the
first component lets the same type support the identity terminal net. -/
def dyadicTerminalNetCenterType
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) : Type u :=
  T × (dyadicChainingFiniteNetOfTotallyBoundedUniv
    (T := T) hT hradiusScale j).A

instance dyadicTerminalNetCenterType.instFintype
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    Fintype (dyadicTerminalNetCenterType (T := T) hT hradiusScale j) := by
  let D := dyadicChainingFiniteNetOfTotallyBoundedUniv
    (T := T) hT hradiusScale j
  letI : Fintype D.A := D.instFintype
  change Fintype (T × D.A)
  infer_instance

/-- Finite net used by the finite terminal Dudley wrapper.

For `j < m`, this is the total-bounded dyadic net at scale `j`, padded with an
unused `T` coordinate. At and after the terminal level, it is the identity net,
so the existing finite chaining telescope closes exactly. -/
def dyadicTerminalFiniteNet
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (m j : ℕ) :
    FiniteNet T (dyadicTerminalNetCenterType (T := T) hT hradiusScale j) := by
  classical
  let D := dyadicChainingFiniteNetOfTotallyBoundedUniv
    (T := T) hT hradiusScale j
  letI : Fintype D.A := D.instFintype
  letI : Nonempty D.A := D.instNonempty
  by_cases hj : j < m
  · exact
      { dist := fun s t => dist s t
        dist_nonneg := fun s t => dist_nonneg
        center := fun a => D.net.center a.2
        project := fun t => (Classical.choice (inferInstance : Nonempty T), D.net.project t)
        radius := D.net.radius
        radius_nonneg := D.net.radius_nonneg
        covers := by
          intro t
          simpa [D, FiniteNet.projection] using D.net.projection_dist_le t }
  · exact
      { dist := fun s t => dist s t
        dist_nonneg := fun s t => dist_nonneg
        center := fun a => a.1
        project := fun t => (t, Classical.choice D.instNonempty)
        radius := 0
        radius_nonneg := le_rfl
        covers := by
          intro t
          simp }

/--
@isnad1 id=eq.2h4v.s6.9509b9062e0d from=translated src=- shape=97bd346f vocab=f7fef49c
-/
@[simp] theorem dyadicTerminalFiniteNet_dist
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (m j : ℕ) :
    (dyadicTerminalFiniteNet (T := T) hT hradiusScale m j).dist =
      fun s t => dist s t := by
  unfold dyadicTerminalFiniteNet
  by_cases hj : j < m
  · simp [hj]
  · simp [hj]

/-- Before the terminal level, the wrapper net has the total-bounded dyadic
radius.
@isnad1 id=eq.3h4v.s6.76865471bb1e from=translated src=- shape=78a0f9ec vocab=ef99b57f
-/
@[simp] theorem dyadicTerminalFiniteNet_radius_of_lt
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) {m j : ℕ}
    (hj : j < m) :
    (dyadicTerminalFiniteNet (T := T) hT hradiusScale m j).radius =
      dyadicChainingNetRadius radiusScale j := by
  unfold dyadicTerminalFiniteNet
  simp [hj]

/-- At the terminal level, the wrapper net is exact.
@isnad1 id=eq.2h4v.s6.3e02ec394b14 from=translated src=- shape=208e10b4 vocab=955cbe8f
-/
@[simp] theorem dyadicTerminalFiniteNet_projection_terminal
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (m : ℕ) (t : T) :
    (dyadicTerminalFiniteNet (T := T) hT hradiusScale m m).projection t = t := by
  unfold dyadicTerminalFiniteNet
  simp [FiniteNet.projection]

/-- Every radius in the finite terminal wrapper is bounded by the scheduled
dyadic radius at that level.
@isnad1 id=le.2h4v.s6.d958b11fb3ea from=translated src=- shape=5ff1afa1 vocab=5a5757a6
-/
theorem dyadicTerminalFiniteNet_radius_le
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (m j : ℕ) :
    (dyadicTerminalFiniteNet (T := T) hT hradiusScale m j).radius ≤
      dyadicChainingNetRadius radiusScale j := by
  by_cases hj : j < m
  · simp [dyadicTerminalFiniteNet_radius_of_lt (T := T) hT hradiusScale hj]
  · have hnonneg : 0 ≤ dyadicChainingNetRadius radiusScale j :=
      (dyadicChainingNetRadius_pos hradiusScale j).le
    unfold dyadicTerminalFiniteNet
    simpa [hj] using hnonneg

/-- Adjacent radii in the finite terminal wrapper fit the geometric radius
budget used by the finite Dudley entropy-sum theorem.
@isnad1 id=le.3h4v.s7.d7ec227353c5 from=translated src=- shape=f226e0f8 vocab=7443f6c1
-/
theorem dyadicTerminalFiniteNet_pair_radius_le
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (m : ℕ)
    {j : ℕ} (_hj : j ∈ Finset.range m) :
    (dyadicTerminalFiniteNet (T := T) hT hradiusScale m j).radius +
      (dyadicTerminalFiniteNet (T := T) hT hradiusScale m (j + 1)).radius ≤
      radiusScale / (2 : ℝ) ^ j := by
  have hleft :=
    dyadicTerminalFiniteNet_radius_le (T := T) hT hradiusScale m j
  have hright :=
    dyadicTerminalFiniteNet_radius_le (T := T) hT hradiusScale m (j + 1)
  calc
    (dyadicTerminalFiniteNet (T := T) hT hradiusScale m j).radius +
      (dyadicTerminalFiniteNet (T := T) hT hradiusScale m (j + 1)).radius
        ≤ dyadicChainingNetRadius radiusScale j +
            dyadicChainingNetRadius radiusScale (j + 1) :=
          add_le_add hleft hright
    _ ≤ radiusScale / (2 : ℝ) ^ j :=
          dyadicChainingNetRadius_pair_sum_le
            (radiusScale := radiusScale) hradiusScale.le j

/-- Adjacent radii in the finite terminal wrapper are positive before the
terminal scale.
@isnad1 id=lt.3h4v.s7.d411914425d9 from=translated src=- shape=230c635d vocab=1320e239
-/
theorem dyadicTerminalFiniteNet_pair_radius_pos
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (m : ℕ)
    {j : ℕ} (hj : j ∈ Finset.range m) :
    0 <
      (dyadicTerminalFiniteNet (T := T) hT hradiusScale m j).radius +
      (dyadicTerminalFiniteNet (T := T) hT hradiusScale m (j + 1)).radius := by
  have hj_lt : j < m := by simpa using hj
  have hleft :
      (dyadicTerminalFiniteNet (T := T) hT hradiusScale m j).radius =
        dyadicChainingNetRadius radiusScale j :=
    dyadicTerminalFiniteNet_radius_of_lt
      (T := T) hT hradiusScale hj_lt
  have hleft_pos : 0 <
      (dyadicTerminalFiniteNet (T := T) hT hradiusScale m j).radius := by
    rw [hleft]
    exact dyadicChainingNetRadius_pos hradiusScale j
  have hright_nonneg : 0 ≤
      (dyadicTerminalFiniteNet (T := T) hT hradiusScale m (j + 1)).radius :=
    (dyadicTerminalFiniteNet (T := T) hT hradiusScale m (j + 1)).radius_nonneg
  linarith

/-- Product of adjacent covering numbers in the finite terminal dyadic wrapper.

This is the finite entropy quantity used by the total-bounded dyadic wrapper.
It records the actual chosen finite covers; no minimal covering-number claim is
made. -/
def dyadicTerminalCoverCount
    [PseudoMetricSpace T] [Fintype T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (m j : ℕ) : ℕ :=
  (dyadicTerminalFiniteNet
    (T := T) hT hradiusScale m j).coveringNumber *
  (dyadicTerminalFiniteNet
    (T := T) hT hradiusScale m (j + 1)).coveringNumber

end

end FormalSLT.Covering.TotalBoundedDudley
