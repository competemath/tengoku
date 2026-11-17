import Tengoku.ClosureResidueP3Lean.P3.Coupling
import Tengoku.ClosureResidueP3Lean.P3.Stabilizer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace P3

section SaturatedStabilizer

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- H1 / Theorem 8.1, exposed under the dependency-map name:
at a graph-saturated depth, residue rank is controlled by support connectivity.-/
theorem residue_finrank_of_graphSaturated
    (φ : Dynamics V) (k : ℕ)
    (hsat : graphSaturated (V := V) φ k) :
    Module.finrank ℂ ↥(residue φ k) =
      Fintype.card V -
        componentCount (V := V) (supportGraph (V := V) φ k) :=
  finrank_residue_eq_card_sub_componentCount_of_graphSaturated
    (V := V) φ k hsat

/-- The number of connected components of a finite graph never exceeds the
number of vertices.  We derive this from the already-kernel-checked
component-sum rank--nullity computation.-/
theorem componentCount_le_card
    (G : SimpleGraph V) :
    componentCount (V := V) G ≤ Fintype.card V := by
  have h :=
    LinearMap.finrank_range_add_finrank_ker
      (componentSum (V := V) G)
  rw [finrank_componentSum_range (V := V) G,
      finrank_graphVertexSpace (V := V)] at h
  omega

/-- H2 / consecutive saturated depths:
CRP residue growth equals the drop in the number of connected components.-/
theorem residueGrowth_eq_component_drop
    (φ : Dynamics V) (k : ℕ)
    (hsat_k : graphSaturated (V := V) φ k)
    (hsat_succ : graphSaturated (V := V) φ (k + 1)) :
    residueGrowth φ (k + 1) =
      componentCount (V := V) (supportGraph (V := V) φ k) -
        componentCount (V := V) (supportGraph (V := V) φ (k + 1)) := by
  have hrank_k :=
    residue_finrank_of_graphSaturated
      (V := V) φ k hsat_k
  have hrank_succ :=
    residue_finrank_of_graphSaturated
      (V := V) φ (k + 1) hsat_succ
  have hgrowth := residueDim_add_growth (V := V) φ k
  change
    Module.finrank ℂ ↥(residue φ k) +
        residueGrowth φ (k + 1) =
      Module.finrank ℂ ↥(residue φ (k + 1)) at hgrowth
  rw [hrank_k, hrank_succ] at hgrowth
  have hk_bound :
      componentCount (V := V) (supportGraph (V := V) φ k) ≤
        Fintype.card V :=
    componentCount_le_card (V := V) (supportGraph (V := V) φ k)
  have hsucc_bound :
      componentCount (V := V) (supportGraph (V := V) φ (k + 1)) ≤
        Fintype.card V :=
    componentCount_le_card (V := V) (supportGraph (V := V) φ (k + 1))
  omega

/-! ## H3: saturated stabilizers are component-constant -/

/-- Traceless diagonal directions that are constant on every connected
component of a graph.-/
def componentConstant
    (G : SimpleGraph V) :
    Submodule ℂ (DiagZero (V := V)) where
  carrier :=
    {d | ∀ i j : V,
      G.connectedComponentMk i = G.connectedComponentMk j →
        d.1.ofLp i = d.1.ofLp j}
  zero_mem' := by
    intro i j hij
    simp
  add_mem' := by
    intro d e hd he i j hij
    simp [hd i j hij, he i j hij]
  smul_mem' := by
    intro c d hd i j hij
    simp [hd i j hij]

omit [DecidableEq V] in
@[simp]
theorem mem_componentConstant
    (G : SimpleGraph V) (d : DiagZero (V := V)) :
    d ∈ componentConstant (V := V) G ↔
      ∀ i j : V,
        G.connectedComponentMk i = G.connectedComponentMk j →
          d.1.ofLp i = d.1.ofLp j := by
  rfl

/-- Coordinate form of the Hermitian pairing with a traceless diagonal
direction.  It is conjugate-linear in the first coordinate argument.-/
def coordinatePairing
    (x : GraphVertexSpace V) (d : DiagZero (V := V)) : ℂ :=
  ∑ i : V, d.1.ofLp i * star (x i)

-- The native `DiagZero` inner product agrees with the coordinate pairing.
omit [DecidableEq V] in
theorem inner_eq_coordinatePairing
    (r d : DiagZero (V := V)) :
    inner ℂ r d =
      coordinatePairing (V := V)
        (diagZeroCoordinates (V := V) r) d := by
  rw [Submodule.coe_inner, PiLp.inner_apply]
  simp_rw [RCLike.inner_apply]
  rfl

/-- Pairing against an incidence generator is the endpoint difference.-/
theorem coordinatePairing_edgeDifference
    (d : DiagZero (V := V)) (i j : V) :
    coordinatePairing (V := V)
        (edgeDifference (V := V) i j) d =
      d.1.ofLp i - d.1.ofLp j := by
  classical
  simp [coordinatePairing, edgeDifference, vertexDelta,
    mul_sub, Finset.sum_sub_distrib]

/-- Zero set of coordinate pairing against a fixed diagonal direction.
Although the pairing is conjugate-linear in its first argument, its zero set
is still a complex submodule.-/
def coordinateAnnihilator
    (d : DiagZero (V := V)) :
    Submodule ℂ (GraphVertexSpace V) where
  carrier := {x | coordinatePairing (V := V) x d = 0}
  zero_mem' := by
    change coordinatePairing (V := V) (0 : GraphVertexSpace V) d = 0
    simp [coordinatePairing]
  add_mem' := by
    intro x y hx hy
    change coordinatePairing (V := V) (x + y) d = 0
    change coordinatePairing (V := V) x d = 0 at hx
    change coordinatePairing (V := V) y d = 0 at hy
    unfold coordinatePairing at hx hy ⊢
    change (∑ i : V, d.1.ofLp i * star (x i + y i)) = 0
    simp_rw [star_add, mul_add]
    rw [Finset.sum_add_distrib, hx, hy, add_zero]
  smul_mem' := by
    intro c x hx
    change coordinatePairing (V := V) (c • x) d = 0
    change coordinatePairing (V := V) x d = 0 at hx
    unfold coordinatePairing at hx ⊢
    change (∑ i : V, d.1.ofLp i * star (c * x i)) = 0
    simp_rw [star_mul]
    calc
      (∑ i : V, d.1.ofLp i * (star (x i) * star c)) =
          star c * (∑ i : V, d.1.ofLp i * star (x i)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = 0 := by rw [hx, mul_zero]

/-- If `d` is constant on graph components, every incidence vector pairs
trivially with `d`.-/
theorem incidenceSpace_le_coordinateAnnihilator_of_componentConstant
    (G : SimpleGraph V) (d : DiagZero (V := V))
    (hd : d ∈ componentConstant (V := V) G) :
    incidenceSpace (V := V) G ≤ coordinateAnnihilator (V := V) d := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with ⟨i, j, hij, rfl⟩
  change coordinatePairing (V := V)
      (edgeDifference (V := V) i j) d = 0
  rw [coordinatePairing_edgeDifference]
  have hcomp :
      G.connectedComponentMk i = G.connectedComponentMk j :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hij
  rw [(mem_componentConstant (V := V) G d).mp hd i j hcomp]
  exact sub_self _

/-- Under graph saturation, every stabilizer direction is constant on each
connected component of the support graph.-/
theorem stabilizer_le_componentConstant_of_graphSaturated
    (φ : Dynamics V) (k : ℕ)
    (hsat : graphSaturated (V := V) φ k) :
    stabilizer (V := V) φ k ≤
      componentConstant (V := V) (supportGraph (V := V) φ k) := by
  intro d hd
  rw [mem_componentConstant]
  intro i j hcomp
  have hdR : d ∈ residueOrthogonal (V := V) φ k := by
    rw [residueOrthogonal_eq_stabilizer (V := V) φ k]
    exact hd
  have hedge :
      edgeDifference (V := V) i j ∈
        incidenceSpace (V := V) (supportGraph (V := V) φ k) :=
    edgeDifference_mem_incidenceSpace_of_component_eq
      (V := V) (supportGraph (V := V) φ k) hcomp
  have hedgeR :
      edgeDifference (V := V) i j ∈
        residueCoordinateSpace (V := V) φ k := by
    rw [hsat]
    exact hedge
  rcases hedgeR with ⟨r, hr, hcoord⟩
  have hzero : inner ℂ r d = 0 :=
    (mem_residueOrthogonal (V := V) φ k d).mp hdR r hr
  rw [inner_eq_coordinatePairing (V := V) r d] at hzero
  rw [hcoord, coordinatePairing_edgeDifference] at hzero
  exact sub_eq_zero.mp hzero

/-- Conversely, at a graph-saturated depth every component-constant
traceless diagonal direction is a stabilizer.-/
theorem componentConstant_le_stabilizer_of_graphSaturated
    (φ : Dynamics V) (k : ℕ)
    (hsat : graphSaturated (V := V) φ k) :
    componentConstant (V := V) (supportGraph (V := V) φ k) ≤
      stabilizer (V := V) φ k := by
  intro d hd
  rw [← residueOrthogonal_eq_stabilizer (V := V) φ k]
  rw [mem_residueOrthogonal]
  intro r hr
  have hcoord :
      diagZeroCoordinates (V := V) r ∈
        residueCoordinateSpace (V := V) φ k :=
    ⟨r, hr, rfl⟩
  have hinc :
      diagZeroCoordinates (V := V) r ∈
        incidenceSpace (V := V) (supportGraph (V := V) φ k) := by
    rw [← hsat]
    exact hcoord
  have hann :=
    incidenceSpace_le_coordinateAnnihilator_of_componentConstant
      (V := V) (supportGraph (V := V) φ k) d hd hinc
  change coordinatePairing (V := V)
      (diagZeroCoordinates (V := V) r) d = 0 at hann
  rw [inner_eq_coordinatePairing (V := V) r d]
  exact hann

/-- H3: at a graph-saturated depth the silent stabilizer is exactly the
space of traceless diagonal functions constant on graph components.-/
theorem stabilizer_eq_componentConstant_of_graphSaturated
    (φ : Dynamics V) (k : ℕ)
    (hsat : graphSaturated (V := V) φ k) :
    stabilizer (V := V) φ k =
      componentConstant (V := V) (supportGraph (V := V) φ k) := by
  apply le_antisymm
  · exact stabilizer_le_componentConstant_of_graphSaturated
      (V := V) φ k hsat
  · exact componentConstant_le_stabilizer_of_graphSaturated
      (V := V) φ k hsat

/-! ## H4: dimension of the saturated silent stabilizer -/

/-- Sum of component values after expanding them back to all vertices.-/
def componentValueSum
    (G : SimpleGraph V) :
    (G.ConnectedComponent → ℂ) →ₗ[ℂ] ℂ where
  toFun a := ∑ v : V, a (G.connectedComponentMk v)
  map_add' a b := by
    simp [Finset.sum_add_distrib]
  map_smul' c a := by
    simp [Finset.mul_sum]

omit [DecidableEq V] in
@[simp]
theorem componentValueSum_apply
    (G : SimpleGraph V)
    (a : G.ConnectedComponent → ℂ) :
    componentValueSum (V := V) G a =
      ∑ v : V, a (G.connectedComponentMk v) := by
  rfl

-- When the vertex set is nonempty, the expanded component-value sum is
-- surjective.  A constant component value realizes any prescribed scalar.
omit [DecidableEq V] in
theorem componentValueSum_surjective
    [Nonempty V]
    (G : SimpleGraph V) :
    Function.Surjective (componentValueSum (V := V) G) := by
  intro z
  have hcard : (Fintype.card V : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card V ≠ 0)
  refine ⟨fun _ => z / (Fintype.card V : ℂ), ?_⟩
  change (∑ _v : V, z / (Fintype.card V : ℂ)) = z
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  field_simp [hcard]

-- The kernel of the expanded component-value sum has dimension `c(G)-1`.
omit [DecidableEq V] in
theorem finrank_componentValueSum_ker
    [Nonempty V]
    (G : SimpleGraph V) :
    Module.finrank ℂ ↥(LinearMap.ker (componentValueSum (V := V) G)) =
      componentCount (V := V) G - 1 := by
  have hrange :
      LinearMap.range (componentValueSum (V := V) G) = ⊤ :=
    LinearMap.range_eq_top.mpr
      (componentValueSum_surjective (V := V) G)
  have h :=
    LinearMap.finrank_range_add_finrank_ker
      (componentValueSum (V := V) G)
  rw [hrange, finrank_top, CommSemiring.finrank_self,
      finrank_componentSpace (V := V) G] at h
  exact Nat.eq_sub_of_add_eq' h

/-- Read a component-constant traceless diagonal direction by one value per
connected component.  Tracelessness places those component values in the
kernel of `componentValueSum`.-/
def componentConstantToKernel
    (G : SimpleGraph V) :
    ↥(componentConstant (V := V) G) →ₗ[ℂ]
      ↥(LinearMap.ker (componentValueSum (V := V) G)) where
  toFun d := by
    refine ⟨fun c => d.1.1.ofLp (componentRep (V := V) G c), ?_⟩
    change
      (∑ v : V,
        d.1.1.ofLp
          (componentRep (V := V) G (G.connectedComponentMk v))) = 0
    have hd :=
      (mem_componentConstant (V := V) G d.1).mp d.2
    calc
      (∑ v : V,
        d.1.1.ofLp
          (componentRep (V := V) G (G.connectedComponentMk v))) =
          ∑ v : V, d.1.1.ofLp v := by
            apply Finset.sum_congr rfl
            intro v hv
            exact
              hd
                (componentRep (V := V) G (G.connectedComponentMk v))
                v
                (connectedComponentMk_componentRep
                  (V := V) G (G.connectedComponentMk v))
      _ = 0 := by
        have hz := d.1.2
        change coordinateSum (V := V) d.1.1 = 0 at hz
        simpa [coordinateSum_apply] using hz
  map_add' d e := by
    apply Subtype.ext
    funext c
    rfl
  map_smul' c d := by
    apply Subtype.ext
    funext C
    rfl

omit [DecidableEq V] in
theorem componentConstantToKernel_injective
    (G : SimpleGraph V) :
    Function.Injective (componentConstantToKernel (V := V) G) := by
  intro d e hde
  apply Subtype.ext
  apply Subtype.ext
  apply (WithLp.linearEquiv 2 ℂ (V → ℂ)).injective
  ext v
  have hd :=
    (mem_componentConstant (V := V) G d.1).mp d.2
      (componentRep (V := V) G (G.connectedComponentMk v))
      v
      (connectedComponentMk_componentRep
        (V := V) G (G.connectedComponentMk v))
  have he :=
    (mem_componentConstant (V := V) G e.1).mp e.2
      (componentRep (V := V) G (G.connectedComponentMk v))
      v
      (connectedComponentMk_componentRep
        (V := V) G (G.connectedComponentMk v))
  have hc :
      d.1.1.ofLp
          (componentRep (V := V) G (G.connectedComponentMk v)) =
        e.1.1.ofLp
          (componentRep (V := V) G (G.connectedComponentMk v)) := by
    exact congrFun (congrArg Subtype.val hde) (G.connectedComponentMk v)
  exact hd.symm.trans (hc.trans he)

omit [DecidableEq V] in
theorem componentConstantToKernel_surjective
    (G : SimpleGraph V) :
    Function.Surjective (componentConstantToKernel (V := V) G) := by
  intro a
  let x : VertexSpace V :=
    WithLp.toLp 2 (fun v => a.1 (G.connectedComponentMk v))
  have hx0 : x ∈ DiagZero (V := V) := by
    change coordinateSum (V := V) x = 0
    rw [coordinateSum_apply]
    change (∑ v : V, a.1 (G.connectedComponentMk v)) = 0
    have ha := a.2
    change componentValueSum (V := V) G a.1 = 0 at ha
    exact ha
  let d0 : DiagZero (V := V) := ⟨x, hx0⟩
  have hd0 :
      d0 ∈ componentConstant (V := V) G := by
    rw [mem_componentConstant]
    intro i j hij
    change
      a.1 (G.connectedComponentMk i) =
        a.1 (G.connectedComponentMk j)
    rw [hij]
  let d : ↥(componentConstant (V := V) G) := ⟨d0, hd0⟩
  refine ⟨d, ?_⟩
  apply Subtype.ext
  funext c
  change
    a.1
        (G.connectedComponentMk
          (componentRep (V := V) G c)) =
      a.1 c
  rw [connectedComponentMk_componentRep (V := V) G c]

/-- Component-constant traceless directions are linearly equivalent to the
kernel of the expanded component-value sum.-/
noncomputable def componentConstantKernelEquiv
    (G : SimpleGraph V) :
    ↥(componentConstant (V := V) G) ≃ₗ[ℂ]
      ↥(LinearMap.ker (componentValueSum (V := V) G)) :=
  LinearEquiv.ofBijective
    (componentConstantToKernel (V := V) G)
    ⟨componentConstantToKernel_injective (V := V) G,
      componentConstantToKernel_surjective (V := V) G⟩

-- A traceless diagonal function constant on graph components has exactly
-- `c(G)-1` complex degrees of freedom.
omit [DecidableEq V] in
theorem finrank_componentConstant
    [Nonempty V]
    (G : SimpleGraph V) :
    Module.finrank ℂ ↥(componentConstant (V := V) G) =
      componentCount (V := V) G - 1 := by
  calc
    Module.finrank ℂ ↥(componentConstant (V := V) G) =
        Module.finrank ℂ
          ↥(LinearMap.ker (componentValueSum (V := V) G)) :=
      (componentConstantKernelEquiv (V := V) G).finrank_eq
    _ = componentCount (V := V) G - 1 :=
      finrank_componentValueSum_ker (V := V) G

/-- H4 / saturated stabilizer dimension:
at a graph-saturated depth, the silent stabilizer has dimension `c(G_k)-1`.-/
theorem silent_finrank_of_graphSaturated
    [Nonempty V]
    (φ : Dynamics V) (k : ℕ)
    (hsat : graphSaturated (V := V) φ k) :
    Module.finrank ℂ ↥(stabilizer (V := V) φ k) =
      componentCount (V := V) (supportGraph (V := V) φ k) - 1 := by
  rw [stabilizer_eq_componentConstant_of_graphSaturated
    (V := V) φ k hsat]
  exact
    finrank_componentConstant
      (V := V) (supportGraph (V := V) φ k)

end SaturatedStabilizer

end P3
