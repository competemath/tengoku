import Tengoku.ClosureResidueP3Lean.P3.Filtration
import Tengoku.ClosureResidueP3Lean.P3.GraphIncidence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace P3

section Support

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Coordinate realization of the traceless diagonal sector inside the
ordinary vertex-coordinate space used by `GraphIncidence`.-/
def diagZeroCoordinates :
    DiagZero (V := V) →ₗ[ℂ] GraphVertexSpace V where
  toFun d := fun i => d.1.ofLp i
  map_add' d e := by
    ext i
    rfl
  map_smul' c d := by
    ext i
    rfl

omit [DecidableEq V] in
@[simp]
theorem diagZeroCoordinates_apply
    (d : DiagZero (V := V)) (i : V) :
    diagZeroCoordinates (V := V) d i = d.1.ofLp i := by
  rfl

/-- The coordinate realization of a residue subspace.-/
def residueCoordinateSpace
    (φ : Dynamics V) (k : ℕ) :
    Submodule ℂ (GraphVertexSpace V) :=
  (residue φ k).map (diagZeroCoordinates (V := V))

/-- A directed pair is active at depth `k` if some hidden flow has a nonzero
coordinate on that ordered pair.-/
def flowActive
    (φ : Dynamics V) (k : ℕ) (i j : V) : Prop :=
  i ≠ j ∧
    ∃ f : EdgeSpace V,
      f ∈ hiddenFlow φ k ∧
      edgeMatrix (V := V) f i j ≠ 0

/-- The undirected support graph `G_k` extracted from the hidden-flow space.
An unordered pair `{i,j}` is present whenever either orientation carries a
nonzero coordinate for some flow in `F_k`.-/
def supportGraph
    (φ : Dynamics V) (k : ℕ) : SimpleGraph V where
  Adj i j :=
    flowActive (V := V) φ k i j ∨
      flowActive (V := V) φ k j i
  symm := ⟨by
    intro i j hij
    rcases hij with hij | hji
    · exact Or.inr hij
    · exact Or.inl hji⟩
  loopless := ⟨by
    intro i hii
    rcases hii with hii | hii
    · exact hii.1 rfl
    · exact hii.1 rfl⟩

@[simp]
theorem supportGraph_adj
    (φ : Dynamics V) (k : ℕ) (i j : V) :
    (supportGraph (V := V) φ k).Adj i j ↔
      flowActive (V := V) φ k i j ∨
        flowActive (V := V) φ k j i := by
  rfl

/-- A nonzero directed coordinate of a hidden flow forces the underlying
undirected edge to occur in the support graph.-/
theorem supportGraph_adj_of_flow
    (φ : Dynamics V) (k : ℕ)
    (f : EdgeSpace V) (hf : f ∈ hiddenFlow φ k)
    {i j : V} (hij : i ≠ j)
    (hneq : edgeMatrix (V := V) f i j ≠ 0) :
    (supportGraph (V := V) φ k).Adj i j := by
  exact Or.inl ⟨hij, f, hf, hneq⟩

/-- Reversing the orientation gives the same undirected support edge.-/
theorem supportGraph_adj_of_flow_rev
    (φ : Dynamics V) (k : ℕ)
    (f : EdgeSpace V) (hf : f ∈ hiddenFlow φ k)
    {i j : V} (hij : i ≠ j)
    (hneq : edgeMatrix (V := V) f j i ≠ 0) :
    (supportGraph (V := V) φ k).Adj i j := by
  exact Or.inr ⟨Ne.symm hij, f, hf, hneq⟩

/-! ## G1: residue support lies in the graph-incidence space -/

/-- Along every nonzero coordinate of a hidden flow, the two endpoints lie
in the same connected component of the support graph.-/
theorem connectedComponentMk_eq_of_hiddenFlow_nonzero
    (φ : Dynamics V) (k : ℕ)
    (f : EdgeSpace V) (hf : f ∈ hiddenFlow φ k)
    {i j : V}
    (hneq : edgeMatrix (V := V) f i j ≠ 0) :
    (supportGraph (V := V) φ k).connectedComponentMk i =
      (supportGraph (V := V) φ k).connectedComponentMk j := by
  have hij : i ≠ j := by
    intro h
    subst j
    exact hneq (edgeMatrix_diag (V := V) f i)
  exact
    SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (supportGraph_adj_of_flow (V := V) φ k f hf hij hneq)

/-- Hence every component indicator of the support graph takes equal values
at the endpoints of a nonzero hidden-flow coordinate.-/
theorem componentIndicator_eq_of_hiddenFlow_nonzero
    (φ : Dynamics V) (k : ℕ)
    (f : EdgeSpace V) (hf : f ∈ hiddenFlow φ k)
    {i j : V}
    (hneq : edgeMatrix (V := V) f i j ≠ 0)
    (c : (supportGraph (V := V) φ k).ConnectedComponent) :
    componentIndicator (V := V) (supportGraph (V := V) φ k) c i =
      componentIndicator (V := V) (supportGraph (V := V) φ k) c j := by
  apply componentIndicator_eq_of_mk_eq
  exact connectedComponentMk_eq_of_hiddenFlow_nonzero
    (V := V) φ k f hf hneq

/-- The coordinate divergence of a hidden flow has zero sum on every
connected component of its support graph.-/
theorem componentSum_divergence_eq_zero
    (φ : Dynamics V) (k : ℕ)
    (f : EdgeSpace V) (hf : f ∈ hiddenFlow φ k) :
    componentSum (V := V) (supportGraph (V := V) φ k)
      (diagZeroCoordinates (V := V) (divergence (V := V) f)) = 0 := by
  ext c
  rw [componentSum_apply, Pi.zero_apply]
  simp_rw [diagZeroCoordinates_apply, divergence_apply]
  simp_rw [mul_sub, Finset.mul_sum]
  rw [Finset.sum_sub_distrib]

  have hswap :
      (∑ i : V, ∑ j : V,
        componentIndicator (V := V) (supportGraph (V := V) φ k) c i *
          edgeMatrix (V := V) f j i) =
      (∑ i : V, ∑ j : V,
        componentIndicator (V := V) (supportGraph (V := V) φ k) c j *
          edgeMatrix (V := V) f i j) := by
    exact
      (Finset.sum_comm :
        (∑ i : V, ∑ j : V,
          componentIndicator (V := V) (supportGraph (V := V) φ k) c i *
            edgeMatrix (V := V) f j i) =
        ∑ j : V, ∑ i : V,
          componentIndicator (V := V) (supportGraph (V := V) φ k) c i *
            edgeMatrix (V := V) f j i)

  have heq :
      (∑ i : V, ∑ j : V,
        componentIndicator (V := V) (supportGraph (V := V) φ k) c i *
          edgeMatrix (V := V) f i j) =
      (∑ i : V, ∑ j : V,
        componentIndicator (V := V) (supportGraph (V := V) φ k) c j *
          edgeMatrix (V := V) f i j) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hzero : edgeMatrix (V := V) f i j = 0
    · simp [hzero]
    · rw [componentIndicator_eq_of_hiddenFlow_nonzero
        (V := V) φ k f hf hzero c]

  rw [hswap, heq]
  exact sub_self _

/-- Coordinate divergence of every hidden flow belongs to the incidence space
of the support graph.-/
theorem divergence_mem_incidenceSpace
    (φ : Dynamics V) (k : ℕ)
    (f : EdgeSpace V) (hf : f ∈ hiddenFlow φ k) :
    diagZeroCoordinates (V := V) (divergence (V := V) f) ∈
      incidenceSpace (V := V) (supportGraph (V := V) φ k) := by
  rw [incidenceSpace_eq_componentSum_ker (V := V)]
  change componentSum (V := V) (supportGraph (V := V) φ k)
      (diagZeroCoordinates (V := V) (divergence (V := V) f)) = 0
  exact componentSum_divergence_eq_zero (V := V) φ k f hf

/-- G1 / Support inclusion:
the coordinate realization of the quadratic residue space lies in the
incidence space of the hidden-flow support graph.-/
theorem residueCoordinateSpace_le_incidenceSpace
    (φ : Dynamics V) (k : ℕ) :
    residueCoordinateSpace (V := V) φ k ≤
      incidenceSpace (V := V) (supportGraph (V := V) φ k) := by
  intro x hx
  rcases hx with ⟨r, hr, rfl⟩
  rw [residue_eq_map_divergence (V := V) φ k] at hr
  rcases hr with ⟨f, hf, rfl⟩
  exact divergence_mem_incidenceSpace (V := V) φ k f hf

end Support

end P3
