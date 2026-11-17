import Tengoku.ClosureResidueP3Lean.P3.Basic
import Tengoku.Seed.Combinatorics.SimpleGraph.Connectivity.Finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

open scoped BigOperators

namespace P3

section GraphIncidence

variable {V : Type*} [DecidableEq V]

/-- Vertex-coordinate space used for the graph-incidence theorem.-/
abbrev GraphVertexSpace (V : Type*) := V → ℂ

/-- Standard coordinate vector at a vertex.-/
def vertexDelta (v : V) : GraphVertexSpace V :=
  fun x => if x = v then 1 else 0

/--
@isnad1 id=eq.0h3v.s5.86a4415dca47 from=translated src=- shape=82af96ed vocab=89d9a8a4
-/
@[simp]
theorem vertexDelta_apply (v x : V) :
    vertexDelta (V := V) v x = if x = v then 1 else 0 := by
  rfl

/--
@isnad1 id=eq.0h2v.s4.d93ef30f6cc7 from=translated src=- shape=980d5fe1 vocab=fd56e610
-/
@[simp]
theorem vertexDelta_self (v : V) :
    vertexDelta (V := V) v v = 1 := by
  simp [vertexDelta]

/--
@isnad1 id=eq.1h3v.s4.894eb9f08f18 from=translated src=- shape=fb1c1c0d vocab=fd56e610
-/
theorem vertexDelta_apply_of_ne {v x : V} (h : x ≠ v) :
    vertexDelta (V := V) v x = 0 := by
  simp [vertexDelta, h]

/-- Oriented incidence vector associated with an ordered pair of vertices.-/
def edgeDifference (u v : V) : GraphVertexSpace V :=
  vertexDelta (V := V) u - vertexDelta (V := V) v

/--
@isnad1 id=eq.0h4v.s6.767609038989 from=translated src=- shape=8893b798 vocab=09773dcb
-/
@[simp]
theorem edgeDifference_apply (u v x : V) :
    edgeDifference (V := V) u v x =
      (if x = u then 1 else 0) - (if x = v then 1 else 0) := by
  rfl

/--
@isnad1 id=eq.0h2v.s4.11314d0d0f7f from=translated src=- shape=61ee8d7b vocab=8dc79670
-/
@[simp]
theorem edgeDifference_self (u : V) :
    edgeDifference (V := V) u u = 0 := by
  ext x
  simp [edgeDifference]

/--
@isnad1 id=eq.0h3v.s5.e46c1fc3b00f from=translated src=- shape=902aba12 vocab=7a04f9a7
-/
theorem edgeDifference_swap (u v : V) :
    edgeDifference (V := V) v u =
      - edgeDifference (V := V) u v := by
  ext x
  simp [edgeDifference]

/-- The graph incidence space:
the complex span of the oriented differences `δ_u - δ_v` over graph edges.

Orientation is immaterial because swapping the endpoints negates the vector.-/
def incidenceSpace (G : SimpleGraph V) :
    Submodule ℂ (GraphVertexSpace V) :=
  Submodule.span ℂ
    {x | ∃ u v : V, G.Adj u v ∧ edgeDifference (V := V) u v = x}

/--
@isnad1 id=mem.1h4v.s6.e0b4888c062e from=translated src=- shape=189b6da0 vocab=a3ea01ff
-/
theorem edgeDifference_mem_incidenceSpace
    (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    edgeDifference (V := V) u v ∈ incidenceSpace (V := V) G := by
  apply Submodule.subset_span
  exact ⟨u, v, huv, rfl⟩

variable [Fintype V]

/-- The traceless / zero-total-sum vertex sector.-/
def graphZeroSumSpace :
    Submodule ℂ (GraphVertexSpace V) where
  carrier := {x | ∑ v : V, x v = 0}
  zero_mem' := by
    simp
  add_mem' := by
    intro x y hx hy
    change (∑ v : V, (x + y) v) = 0
    change (∑ v : V, x v) = 0 at hx
    change (∑ v : V, y v) = 0 at hy
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, hx, hy, add_zero]
  smul_mem' := by
    intro c x hx
    change (∑ v : V, (c • x) v) = 0
    change (∑ v : V, x v) = 0 at hx
    simp only [Pi.smul_apply]
    change (∑ v : V, c * x v) = 0
    rw [← Finset.mul_sum, hx, mul_zero]

omit [DecidableEq V] in
/--
@isnad1 id=iff.0h2v.s6.72beba26f502 from=translated src=- shape=7f0e42b5 vocab=26c2ce46
-/
@[simp]
theorem mem_graphZeroSumSpace (x : GraphVertexSpace V) :
    x ∈ graphZeroSumSpace (V := V) ↔ ∑ v : V, x v = 0 := by
  rfl

/-- Every edge-incidence vector has zero total sum.
@isnad1 id=mem.0h3v.s6.068607356b5c from=translated src=- shape=121ae3f9 vocab=6e351e44
-/
theorem edgeDifference_mem_graphZeroSumSpace (u v : V) :
    edgeDifference (V := V) u v ∈ graphZeroSumSpace (V := V) := by
  rw [mem_graphZeroSumSpace]
  simp [edgeDifference, vertexDelta, Finset.sum_sub_distrib]

/-- The graph incidence space always lies in the traceless vertex sector.
@isnad1 id=le.0h2v.s6.e96a6eb40558 from=translated src=- shape=3bc679bb vocab=e67302d2
-/
theorem incidenceSpace_le_graphZeroSumSpace (G : SimpleGraph V) :
    incidenceSpace (V := V) G ≤ graphZeroSumSpace (V := V) := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with ⟨u, v, huv, rfl⟩
  exact edgeDifference_mem_graphZeroSumSpace (V := V) u v

/-! ## Reachability and telescoping incidence differences -/

-- Vertex differences telescope.
omit [Fintype V] in
/--
@isnad1 id=eq.0h4v.s5.1326435b67d4 from=translated src=- shape=48eee5a0 vocab=a04c1ae3
-/
theorem edgeDifference_trans
    (u v w : V) :
    edgeDifference (V := V) u w =
      edgeDifference (V := V) u v +
        edgeDifference (V := V) v w := by
  ext x
  simp [edgeDifference, vertexDelta]

-- If two vertices are reachable in `G`, their coordinate difference lies
-- in the graph incidence space. This is the path-telescoping lemma.
omit [Fintype V] in
/--
@isnad1 id=mem.1h4v.s6.1ba4c94a8cdf from=translated src=- shape=189b6da0 vocab=79499fed
-/
theorem edgeDifference_mem_incidenceSpace_of_reachable
    (G : SimpleGraph V) {u v : V} (huv : G.Reachable u v) :
    edgeDifference (V := V) u v ∈ incidenceSpace (V := V) G := by
  have hrt : Relation.ReflTransGen G.Adj u v :=
    (SimpleGraph.reachable_iff_reflTransGen (G := G) u v).mp huv
  refine Relation.ReflTransGen.trans_induction_on
    (motive := fun {a b} _ =>
      edgeDifference (V := V) a b ∈ incidenceSpace (V := V) G)
    hrt ?_ ?_ ?_
  · intro a
    rw [edgeDifference_self]
    exact Submodule.zero_mem _
  · intro a b hab
    exact edgeDifference_mem_incidenceSpace (V := V) G hab
  · intro a b c hab hbc ihab ihbc
    rw [edgeDifference_trans]
    exact (incidenceSpace (V := V) G).add_mem ihab ihbc

-- Equal connected-component classes imply that the corresponding
-- coordinate difference lies in the incidence space.
omit [Fintype V] in
/--
@isnad1 id=mem.1h4v.s6.c19643d11721 from=translated src=- shape=09205395 vocab=9a0b6999
-/
theorem edgeDifference_mem_incidenceSpace_of_component_eq
    (G : SimpleGraph V) {u v : V}
    (hcomp : G.connectedComponentMk u = G.connectedComponentMk v) :
    edgeDifference (V := V) u v ∈ incidenceSpace (V := V) G := by
  apply edgeDifference_mem_incidenceSpace_of_reachable (V := V) G
  exact SimpleGraph.ConnectedComponent.exact hcomp

/-! ## Component-sum map -/

/-- Indicator of a connected component.  It is noncomputable only because
equality on the quotient `ConnectedComponent` is chosen classically.-/
noncomputable def componentIndicator
    (G : SimpleGraph V) (c : G.ConnectedComponent) (v : V) : ℂ := by
  classical
  exact if G.connectedComponentMk v = c then 1 else 0

omit [DecidableEq V] [Fintype V] in
/--
@isnad1 id=eq.0h3v.s4.d350513e9e71 from=translated src=- shape=5ff2b2df vocab=92151f70
-/
@[simp]
theorem componentIndicator_self
    (G : SimpleGraph V) (u : V) :
    componentIndicator (V := V) G (G.connectedComponentMk u) u = 1 := by
  classical
  simp [componentIndicator]

omit [DecidableEq V] [Fintype V] in
/--
@isnad1 id=eq.1h5v.s5.e220dd257096 from=translated src=- shape=0942ea19 vocab=6ea08396
-/
theorem componentIndicator_eq_of_mk_eq
    (G : SimpleGraph V) {u v : V}
    (h : G.connectedComponentMk u = G.connectedComponentMk v)
    (c : G.ConnectedComponent) :
    componentIndicator (V := V) G c u =
      componentIndicator (V := V) G c v := by
  classical
  simp [componentIndicator, h]

/-- Sum of vertex coordinates separately on each connected component.-/
noncomputable def componentSum (G : SimpleGraph V) :
    GraphVertexSpace V →ₗ[ℂ] (G.ConnectedComponent → ℂ) := by
  classical
  refine
    { toFun := fun x c =>
        ∑ v : V, componentIndicator (V := V) G c v * x v
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    ext c
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  · intro a x
    ext c
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    ring

omit [DecidableEq V] in
/--
@isnad1 id=eq.0h4v.s7.a57a81460f9e from=translated src=- shape=a82a2d0c vocab=8c5ada97
-/
@[simp]
theorem componentSum_apply
    (G : SimpleGraph V) (x : GraphVertexSpace V)
    (c : G.ConnectedComponent) :
    componentSum (V := V) G x c =
      ∑ v : V, componentIndicator (V := V) G c v * x v := by
  rfl

/-- A coordinate basis vector contributes exactly the indicator of its
connected component.
@isnad1 id=eq.0h4v.s7.7c024a0af0f8 from=translated src=- shape=c1d96c66 vocab=82aca8a3
-/
theorem componentSum_vertexDelta
    (G : SimpleGraph V) (u : V) (c : G.ConnectedComponent) :
    componentSum (V := V) G (vertexDelta (V := V) u) c =
      componentIndicator (V := V) G c u := by
  classical
  rw [componentSum_apply]
  simp [vertexDelta]

/-- Edge differences have zero component sum because adjacent endpoints lie
in the same connected component.
@isnad1 id=eq.1h4v.s7.39f9c52722a4 from=translated src=- shape=285c7e0d vocab=7b7a2dab
-/
theorem componentSum_edgeDifference
    (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    componentSum (V := V) G (edgeDifference (V := V) u v) = 0 := by
  rw [edgeDifference, LinearMap.map_sub]
  ext c
  rw [Pi.sub_apply, Pi.zero_apply,
      componentSum_vertexDelta, componentSum_vertexDelta]
  have hcomp :
      G.connectedComponentMk u = G.connectedComponentMk v :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj huv
  rw [componentIndicator_eq_of_mk_eq (V := V) G hcomp c]
  exact sub_self _

/-- Every graph-incidence vector has zero sum on every connected component.
@isnad1 id=le.0h2v.s7.1d46eda8e51b from=translated src=- shape=3f5a7ecb vocab=318b2dc2
-/
theorem incidenceSpace_le_componentSum_ker
    (G : SimpleGraph V) :
    incidenceSpace (V := V) G ≤
      (componentSum (V := V) G).ker := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with ⟨u, v, huv, rfl⟩
  change componentSum (V := V) G
      (edgeDifference (V := V) u v) = 0
  exact componentSum_edgeDifference (V := V) G huv

/-! ## Component representatives and surjectivity -/

/-- A chosen representative vertex of a connected component.-/
noncomputable def componentRep
    (G : SimpleGraph V) (c : G.ConnectedComponent) : V :=
  Quot.out c

omit [DecidableEq V] [Fintype V] in
/--
@isnad1 id=eq.0h3v.s4.a5f5c78c542a from=translated src=- shape=a5bc72c5 vocab=af23ec63
-/
@[simp]
theorem connectedComponentMk_componentRep
    (G : SimpleGraph V) (c : G.ConnectedComponent) :
    G.connectedComponentMk (componentRep (V := V) G c) = c := by
  change Quot.mk G.Reachable (Quot.out c) = c
  exact Quot.out_eq c

-- A representative vertex belongs to the component it represents.
omit [DecidableEq V] [Fintype V] in
/--
@isnad1 id=eq.0h3v.s4.a5f5c78c542a from=translated src=- shape=a5bc72c5 vocab=af23ec63
-/
theorem componentRep_same_component
    (G : SimpleGraph V) (c : G.ConnectedComponent) :
    G.connectedComponentMk (componentRep (V := V) G c) = c :=
  connectedComponentMk_componentRep (V := V) G c

/-- Component sum of the delta-vector at a chosen representative is the
component indicator evaluated at that representative.
@isnad1 id=eq.0h4v.s7.cdb08de6f71f from=translated src=- shape=659d6485 vocab=9eee69c8
-/
theorem componentSum_vertexDelta_componentRep
    (G : SimpleGraph V) (c c' : G.ConnectedComponent) :
    componentSum (V := V) G
        (vertexDelta (V := V) (componentRep (V := V) G c)) c' =
      componentIndicator (V := V) G c'
        (componentRep (V := V) G c) := by
  exact componentSum_vertexDelta (V := V) G
    (componentRep (V := V) G c) c'

/-- The component-sum map is surjective.
@isnad1 id=surjecti.0h2v.s7.b9d9ecefc20c from=translated src=- shape=69f47b3d vocab=880a72d0
-/
theorem componentSum_surjective
    (G : SimpleGraph V) :
    Function.Surjective (componentSum (V := V) G) := by
  classical
  intro y
  let x : GraphVertexSpace V :=
    ∑ c : G.ConnectedComponent,
      y c • vertexDelta (V := V) (componentRep (V := V) G c)
  refine ⟨x, ?_⟩
  ext c
  rw [show x =
      ∑ c' : G.ConnectedComponent,
        y c' • vertexDelta (V := V) (componentRep (V := V) G c') by rfl]
  rw [map_sum]
  simp_rw [LinearMap.map_smul]
  simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [componentSum_vertexDelta_componentRep (V := V)]
  simp [componentIndicator, connectedComponentMk_componentRep]

/-- Hence the range of the component-sum map is the whole component
coordinate space.
@isnad1 id=eq.0h2v.s7.9c878d02bd7b from=translated src=- shape=635c689d vocab=bdbd69eb
-/
theorem componentSum_range_eq_top
    (G : SimpleGraph V) :
    LinearMap.range (componentSum (V := V) G) = ⊤ := by
  exact LinearMap.range_eq_top.mpr (componentSum_surjective (V := V) G)

/-- Number of connected components, written without choosing a particular
`Fintype` instance on the quotient.-/
def componentCount (G : SimpleGraph V) : ℕ :=
  Nat.card G.ConnectedComponent

/-! ## Rank--nullity for the component-sum map -/

-- The source vertex-coordinate space has complex dimension `|V|`.
omit [DecidableEq V] in
/--
@isnad1 id=eq.0h1v.s5.683c385c6ce2 from=translated src=- shape=2a7f0613 vocab=eebaec34
-/
theorem finrank_graphVertexSpace :
    Module.finrank ℂ (GraphVertexSpace V) = Fintype.card V := by
  simp [GraphVertexSpace]

-- The target component-coordinate space has complex dimension equal to the
-- number of connected components. The statement uses `Nat.card`, so it does
-- not depend on which `Fintype` instance Lean chooses for the quotient.
omit [DecidableEq V] in
/--
@isnad1 id=eq.0h2v.s5.9db7482e913e from=translated src=- shape=6ad95750 vocab=f301bb22
-/
theorem finrank_componentSpace
    (G : SimpleGraph V) :
    Module.finrank ℂ (G.ConnectedComponent → ℂ) =
      componentCount (V := V) G := by
  rw [Module.finrank_pi]
  simp [componentCount]

/-- Since `componentSum` is surjective, its range has dimension `c(G)`.
@isnad1 id=eq.0h2v.s8.879f9446c2fc from=translated src=- shape=794c66dd vocab=b8a0a603
-/
theorem finrank_componentSum_range
    (G : SimpleGraph V) :
    Module.finrank ℂ ↥(LinearMap.range (componentSum (V := V) G)) =
      componentCount (V := V) G := by
  rw [componentSum_range_eq_top (V := V) G]
  simpa using finrank_componentSpace (V := V) G

/-- Rank--nullity for the component-sum map:
the componentwise zero-sum space has dimension `|V| - c(G)`.
@isnad1 id=eq.0h2v.s8.b909b65ae260 from=translated src=- shape=81fa3f52 vocab=934aecda
-/
theorem finrank_componentSum_ker
    (G : SimpleGraph V) :
    Module.finrank ℂ ↥((componentSum (V := V) G).ker) =
      Fintype.card V - componentCount (V := V) G := by
  have h :=
    LinearMap.finrank_range_add_finrank_ker
      (componentSum (V := V) G)
  rw [finrank_componentSum_range (V := V) G,
      finrank_graphVertexSpace (V := V)] at h
  exact Nat.eq_sub_of_add_eq' h

/-! ## Reverse inclusion and the incidence-space identification -/

-- If `x` lies in the kernel of the component-sum map, then its
-- component-indicator weighted sum vanishes on every connected component.
omit [DecidableEq V] in
/--
@isnad1 id=eq.1h4v.s7.35057c88cc2a from=translated src=- shape=a6656d63 vocab=90f8c9c8
-/
theorem componentCoefficient_eq_zero_of_mem_ker
    (G : SimpleGraph V) (x : GraphVertexSpace V)
    (hx : x ∈ (componentSum (V := V) G).ker)
    (c : G.ConnectedComponent) :
    (∑ v : V, componentIndicator (V := V) G c v * x v) = 0 := by
  change componentSum (V := V) G x = 0 at hx
  have hc := congrFun hx c
  rw [Pi.zero_apply, componentSum_apply] at hc
  exact hc

/-- The standard coordinate vectors resolve every vertex vector.
@isnad1 id=eq.0h2v.s5.18da6eae1949 from=translated src=- shape=a3dc2c97 vocab=b3e48999
-/
theorem sum_smul_vertexDelta
    (x : GraphVertexSpace V) :
    (∑ v : V, x v • vertexDelta (V := V) v) = x := by
  classical
  ext u
  simp [vertexDelta]

/-- The representative correction vanishes on the kernel of `componentSum`.
@isnad1 id=eq.1h3v.s7.a1ddab00f932 from=translated src=- shape=0ea1718d vocab=92b33fff
-/
theorem representativeCorrection_eq_zero_of_mem_ker
    (G : SimpleGraph V) (x : GraphVertexSpace V)
    (hx : x ∈ (componentSum (V := V) G).ker) :
    (∑ v : V,
      x v • vertexDelta (V := V)
        (componentRep (V := V) G (G.connectedComponentMk v))) = 0 := by
  classical
  ext u
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    vertexDelta_apply, Pi.zero_apply]
  by_cases hu :
      componentRep (V := V) G (G.connectedComponentMk u) = u
  · have hiff (v : V) :
        u = componentRep (V := V) G (G.connectedComponentMk v) ↔
          G.connectedComponentMk v = G.connectedComponentMk u := by
      constructor
      · intro h
        have hmk := congrArg G.connectedComponentMk h
        have hrep :
            G.connectedComponentMk
                (componentRep (V := V) G (G.connectedComponentMk v)) =
              G.connectedComponentMk v :=
          connectedComponentMk_componentRep
            (V := V) G (G.connectedComponentMk v)
        exact (hmk.trans hrep).symm
      · intro h
        have hrep :=
          congrArg (componentRep (V := V) G) h
        calc
          u = componentRep (V := V) G (G.connectedComponentMk u) := hu.symm
          _ = componentRep (V := V) G (G.connectedComponentMk v) := hrep.symm
    have hc :=
      componentCoefficient_eq_zero_of_mem_ker
        (V := V) G x hx (G.connectedComponentMk u)
    simpa [componentIndicator, hiff, mul_comm] using hc
  · apply Finset.sum_eq_zero
    intro v hv
    have hne :
        u ≠ componentRep (V := V) G (G.connectedComponentMk v) := by
      intro h
      have hmk := congrArg G.connectedComponentMk h
      have hcomp :
          G.connectedComponentMk u = G.connectedComponentMk v := by
        exact hmk.trans
          (connectedComponentMk_componentRep
            (V := V) G (G.connectedComponentMk v))
      have hrep :=
        congrArg (componentRep (V := V) G) hcomp
      apply hu
      calc
        componentRep (V := V) G (G.connectedComponentMk u) =
            componentRep (V := V) G (G.connectedComponentMk v) := hrep
        _ = u := h.symm
    simp [hne]

/-- Canonical sum of componentwise vertex differences.-/
def representativeDifference
    (G : SimpleGraph V) (x : GraphVertexSpace V) :
    GraphVertexSpace V :=
  ∑ v : V,
    x v • edgeDifference (V := V) v
      (componentRep (V := V) G (G.connectedComponentMk v))

/-- Every canonical representative difference belongs to the graph incidence
space, by the telescoping lemma inside each connected component.
@isnad1 id=mem.0h3v.s6.38800eb264f7 from=translated src=- shape=c5933ed7 vocab=74af9343
-/
theorem representativeDifference_mem_incidenceSpace
    (G : SimpleGraph V) (x : GraphVertexSpace V) :
    representativeDifference (V := V) G x ∈
      incidenceSpace (V := V) G := by
  classical
  apply Submodule.sum_mem
  intro v hv
  apply (incidenceSpace (V := V) G).smul_mem
  apply edgeDifference_mem_incidenceSpace_of_component_eq (V := V) G
  rw [connectedComponentMk_componentRep
    (V := V) G (G.connectedComponentMk v)]

/-- On the kernel of the component-sum map, the canonical representative
difference reconstructs the original vector.
@isnad1 id=eq.1h3v.s7.151ae6d1a623 from=translated src=- shape=361132bc vocab=7c4514c4
-/
theorem representativeDifference_eq_of_mem_ker
    (G : SimpleGraph V) (x : GraphVertexSpace V)
    (hx : x ∈ (componentSum (V := V) G).ker) :
    representativeDifference (V := V) G x = x := by
  classical
  unfold representativeDifference
  simp_rw [edgeDifference, smul_sub]
  rw [Finset.sum_sub_distrib]
  rw [sum_smul_vertexDelta (V := V) x]
  rw [representativeCorrection_eq_zero_of_mem_ker (V := V) G x hx]
  exact sub_zero x

/-- Reverse inclusion: every componentwise zero-sum vector is generated by
graph edge differences.
@isnad1 id=le.0h2v.s7.69c58606f83d from=translated src=- shape=6e33a26f vocab=318b2dc2
-/
theorem componentSum_ker_le_incidenceSpace
    (G : SimpleGraph V) :
    (componentSum (V := V) G).ker ≤ incidenceSpace (V := V) G := by
  intro x hx
  have hmem :=
    representativeDifference_mem_incidenceSpace (V := V) G x
  rw [representativeDifference_eq_of_mem_ker (V := V) G x hx] at hmem
  exact hmem

/-- The graph incidence space is exactly the kernel of componentwise summation.
@isnad1 id=eq.0h2v.s6.e67cccc4bdf0 from=translated src=- shape=3f5a7ecb vocab=41c72a1d
-/
theorem incidenceSpace_eq_componentSum_ker
    (G : SimpleGraph V) :
    incidenceSpace (V := V) G =
      (componentSum (V := V) G).ker := by
  apply le_antisymm
  · exact incidenceSpace_le_componentSum_ker (V := V) G
  · exact componentSum_ker_le_incidenceSpace (V := V) G

/-- F-stage main theorem / Incidence Rank Theorem:
`dim_C B(G) = |V| - c(G)`.
@isnad1 id=eq.0h2v.s7.162466ecbc33 from=translated src=- shape=b0a9d0ce vocab=90b92f53
-/
theorem incidence_rank
    (G : SimpleGraph V) :
    Module.finrank ℂ ↥(incidenceSpace (V := V) G) =
      Fintype.card V - componentCount (V := V) G := by
  rw [incidenceSpace_eq_componentSum_ker (V := V) G]
  exact finrank_componentSum_ker (V := V) G

end GraphIncidence

end P3
