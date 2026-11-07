/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Tengoku.Tnlean.TNLean.PEPS.InsertionRealization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The unrestricted physical-to-virtual recovery is false without positive bonds

This file is a checked counterexample. The statement of
`physical_to_virtual_insertion` is false once the positive-bond hypothesis is
dropped: a zero-dimensional edge incident to an endpoint empties the edge
boundary configuration, so the resonate hypothesis holds vacuously while the
recovery conclusion remains a genuine constraint that fails for a nontrivial
right-endpoint operator.

The explicit witness is the graph on three vertices with the distinguished edge
of bond dimension one and a second edge of bond dimension zero at the left
endpoint. `physical_to_virtual_insertion_statement_false` refutes a concrete
instance of the hypothesis-free statement;
`physical_to_virtual_insertion` itself carries the restored hypothesis that
every bond dimension is positive.

Source: arXiv:1804.04964, local source `paper_normal.tex`, lines 250 and
254--255: the recovery lemma is stated for injective three-site tensor networks
with a vector space assigned to the edge. The positivity hypothesis makes this
nonzero virtual edge space explicit in the formal statement. The same missing
hypothesis was identified for the edge-blocked three-site injectivity
(issue #1366).
-/

namespace TNLean
namespace PEPS
namespace PhysicalToVirtualCounterexample

open scoped BigOperators

abbrev V3 := Fin 3

def adj3 (a b : V3) : Prop :=
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0)

instance : DecidableRel adj3 := by unfold adj3; infer_instance

def g3 : SimpleGraph V3 where
  Adj := adj3
  symm := ⟨by
    intro a b h
    unfold adj3 at *
    fin_cases a <;> fin_cases b <;> simp_all⟩
  loopless := ⟨by intro a; unfold adj3; fin_cases a <;> simp⟩

instance : DecidableRel g3.Adj := by
  change DecidableRel adj3
  infer_instance

def e3 : Edge g3 := ⟨(0, 1), by constructor <;> decide⟩
def f3 : Edge g3 := ⟨(0, 2), by constructor <;> decide⟩

/--
@isnad1 id=ne.0h0v.s3.30c039eeb0cc from=translated src=- shape=9094f7d5 vocab=50f7d715
-/
theorem f3_ne_e3 : f3 ≠ e3 := by decide

/-- bond dimension: 1 on e (distinguished), 0 on f (the extra zero bond at u).-/
def bd : Edge g3 → ℕ := fun g => if g = e3 then 1 else 0

/--
@isnad1 id=eq.0h0v.s3.bceeb78646a0 from=translated src=- shape=b0ae1d2b vocab=e646be4b
-/
theorem bd_e3 : bd e3 = 1 := by simp [bd]
/--
@isnad1 id=eq.0h0v.s3.450c8c225231 from=translated src=- shape=b0ae1d2b vocab=b78ed432
-/
theorem bd_f3 : bd f3 = 0 := by simp [bd, f3_ne_e3]

/-- The tensor: d = 2. Right endpoint (vertex 1) outputs e_0 = ![1,0] on its
single config; other vertices output 0 (their config spaces are empty anyway).-/
def a3 : Tensor g3 2 where
  bondDim := bd
  component v :=
    match v with
    | 0 => fun _ _ => 0
    | 1 => fun _ => ![1, 0]
    | 2 => fun _ _ => 0

/--
@isnad1 id=eq.0h0v.s4.51191da0e576 from=translated src=- shape=abc65a57 vocab=c01df8af
-/
theorem a3_bond_dim_e3 : a3.bondDim e3 = 1 := bd_e3
/--
@isnad1 id=eq.0h0v.s4.25a4c9a54d6d from=translated src=- shape=abc65a57 vocab=796cc15f
-/
theorem a3_bond_dim_f3 : a3.bondDim f3 = 0 := bd_f3

/--
@isnad1 id=eq.0h0v.s6.b1d773b9326c from=translated src=- shape=adb3796a vocab=53df69e6
-/
theorem e3_left : e3.1.1 = (0 : V3) := rfl
/--
@isnad1 id=eq.0h0v.s6.3b974d5198c1 from=translated src=- shape=cf20fa0d vocab=53df69e6
-/
theorem e3_right : e3.1.2 = (1 : V3) := rfl

/-- f3 as an incident edge of vertex 0.-/
def f3incident : IncidentEdge g3 (0 : V3) := ⟨f3, Or.inl rfl⟩

/-- Left endpoint local config is empty (incident edge f3 has bond 0).-/
instance : IsEmpty (LocalVirtualConfig a3 (0 : V3)) := by
  refine ⟨fun c => ?_⟩
  have h := c f3incident
  rw [show a3.bondDim f3incident.1 = 0 from a3_bond_dim_f3] at h
  exact h.elim0

/-- f3 is an other-incident edge of vertex 0 relative to the distinguished edge.-/
def f3other : OtherIncidentEdge (G := g3) (0 : V3) (edgeLeftIncident (G := g3) e3) :=
  ⟨f3incident, fun h => f3_ne_e3 (congrArg (fun ie => ie.1) h)⟩

/-- Left residual config is empty (it includes the f3-coordinate of bond 0).-/
instance : IsEmpty (ResidualLocalConfig a3 (edgeLeftIncident (G := g3) e3)) := by
  refine ⟨fun c => ?_⟩
  have h := c f3other
  rw [show a3.bondDim f3other.1.1 = 0 from a3_bond_dim_f3] at h
  exact h.elim0

/-- Hence the edge-middle boundary label is empty.-/
instance : IsEmpty (EdgeMiddleBoundaryLabel (G := g3) a3 e3) :=
  Prod.isEmpty_left

/-- The only incident edge of vertex 1 is the distinguished edge e3.
@isnad1 id=eq.0h1v.s7.3215ca7efa9d from=translated src=- shape=f8e4b3f5 vocab=08171cf4
-/
theorem incident_one_eq (ie : IncidentEdge g3 (1 : V3)) : ie.1 = e3 := by
  revert ie; decide

/-- Every incident-edge bond at vertex 1 has dimension 1.
@isnad1 id=eq.0h1v.s7.f9a02c29985e from=translated src=- shape=295f0b70 vocab=e9719d7f
-/
theorem bond_dim_incident_one (ie : IncidentEdge g3 (1 : V3)) :
    a3.bondDim ie.1 = 1 := by
  rw [incident_one_eq ie]; exact a3_bond_dim_e3

/-- The right endpoint local config type has exactly one element.
@isnad1 id=eq.0h2v.s6.ead2f528a880 from=translated src=- shape=d831f4c5 vocab=996794c5
-/
theorem right_config_unique :
    ∀ a b : LocalVirtualConfig a3 (1 : V3), a = b := by
  intro a b
  funext ie
  have h1 : a3.bondDim ie.1 = 1 := bond_dim_incident_one ie
  have : Subsingleton (Fin (a3.bondDim ie.1)) := by rw [h1]; infer_instance
  apply Subsingleton.elim

/-- `a3.component 1 η = ![1,0]` for every (the unique) config `η`.
@isnad1 id=eq.0h1v.s6.980381dfc60b from=translated src=- shape=c01f1b1a vocab=e63c2660
-/
theorem a3_component_one (η : LocalVirtualConfig a3 (1 : V3)) :
    a3.component (1 : V3) η = ![1, 0] := rfl

/-- The right endpoint local tensor map applied to `c` evaluated at index 0
recovers `c` at the unique config.
@isnad1 id=eq.0h2v.s9.7fcc5c6f5c3a from=translated src=- shape=bff2cf8e vocab=1ee46f5f
-/
theorem local_tensor_map_one_apply_zero (c : LocalVirtualConfig a3 (1 : V3) → ℂ)
    (η₀ : LocalVirtualConfig a3 (1 : V3)) :
    localTensorMap a3 (1 : V3) c 0 = c η₀ := by
  classical
  simp only [localTensorMap, Fintype.linearCombination_apply]
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single η₀]
  · simp [a3_component_one]
  · intro b _ hb
    rw [right_config_unique b η₀] at hb
    exact absurd rfl hb
  · intro h; exact absurd (Finset.mem_univ η₀) h

/-- Right endpoint local tensor map is injective.
@isnad1 id=injectiv.0h0v.s9.85081260a005 from=translated src=- shape=25c4d787 vocab=6e05989c
-/
theorem right_injective : Function.Injective (localTensorMap a3 (1 : V3)) := by
  intro c c' h
  funext η
  have h0 := congrFun h 0
  rw [local_tensor_map_one_apply_zero c η, local_tensor_map_one_apply_zero c' η] at h0
  exact h0

/-- Left endpoint local tensor map is injective (its domain is empty).
@isnad1 id=injectiv.0h0v.s9.aceb9dbd5c8a from=translated src=- shape=25c4d787 vocab=6e05989c
-/
theorem left_injective : Function.Injective (localTensorMap a3 (0 : V3)) := by
  intro c c' _
  funext η
  exact (IsEmpty.false η).elim

/-- The blocked three-site object is injective.
@isnad1 id=edgebloc.0h0v.s4.0a67222c1c70 from=translated src=- shape=e008ef65 vocab=5e6cb19b
-/
theorem a3_edge_blocked_three_site_injective :
    EdgeBlockedThreeSiteInjective (G := g3) a3 e3 :=
  { left_injective := by
      have : e3.1.1 = (0 : V3) := e3_left
      rw [this]; exact left_injective
    middle_injective := linearIndependent_empty_type
    right_injective := by
      have : e3.1.2 = (1 : V3) := e3_right
      rw [this]; exact right_injective }

/-- The ordinary edge-boundary configuration type is empty (its left residual
field ranges over an empty type).-/
instance : IsEmpty (EdgeBoundaryConfig (G := g3) a3 e3) := by
  refine ⟨fun β => ?_⟩
  exact (IsEmpty.false β.leftResidual).elim

/-- The "bad" right physical operator: coordinate swap on `Fin 2 → ℂ`. It sends
`![1,0]` to `![0,1]`, which is not a scalar multiple of `![1,0]`.-/
def o2bad : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun x := ![x 1, x 0]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' c x := by funext i; fin_cases i <;> simp

/--
@isnad1 id=eq.0h0v.s8.59a825db5ff8 from=translated src=- shape=d587cc6f vocab=9a5b4660
-/
theorem o2bad_apply_e0 : o2bad (![1, 0] : Fin 2 → ℂ) = ![0, 1] := by
  funext i; fin_cases i <;> simp [o2bad]

/-- Everything in the image of the right endpoint local tensor map has a zero in
coordinate 1 (the image lies in the span of `![1,0]`).
@isnad1 id=eq.0h1v.s9.db1d8dfda76d from=translated src=- shape=75404ea4 vocab=1ee46f5f
-/
theorem local_tensor_map_one_apply_one (w : LocalVirtualConfig a3 (1 : V3) → ℂ) :
    localTensorMap a3 (1 : V3) w 1 = 0 := by
  classical
  simp only [localTensorMap, Fintype.linearCombination_apply]
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero ?_
  intro η _
  simp [a3_component_one]

/-- The right endpoint local config type is inhabited (assign 0 to every
incident-edge bond, each of which has dimension 1).-/
instance : Inhabited (LocalVirtualConfig a3 (1 : V3)) :=
  ⟨fun ie => ⟨0, by rw [bond_dim_incident_one ie]; exact Nat.one_pos⟩⟩

/-- The unique right-endpoint config.-/
def η₀ : LocalVirtualConfig a3 (1 : V3) := default

/-- The right endpoint local tensor map sends the single basis vector to `![1,0]`.
@isnad1 id=eq.0h0v.s10.a8aba9c437b8 from=translated src=- shape=15ba4b90 vocab=b9b9d685
-/
theorem local_tensor_map_one_single :
    localTensorMap a3 (1 : V3) (Pi.single η₀ (1 : ℂ)) = ![1, 0] := by
  rw [localTensorMap_apply_single]
  exact a3_component_one η₀

/-! ### The scope refutation -/

/-- The type of the original `physical_to_virtual_insertion` statement, generic
over the graph, vertex set, and physical dimension. This is a concrete finite
vertex-set instance of the signature of
`TNLean.PEPS.physical_to_virtual_insertion`.-/
def physicalToVirtualInsertionStatement : Prop :=
  ∀ {V : Type} [Fintype V] [LinearOrder V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {d : ℕ} (A : Tensor G d) (e : Edge G)
    (_ : EdgeBlockedThreeSiteInjective (G := G) A e)
    (O₁ O₂ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (_ : ∀ σ : V → Fin d,
      (∑ β : EdgeBoundaryConfig (G := G) A e,
        O₁ (A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β)) (σ e.1.1) *
          edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
          A.component e.1.2 (edgeRightLocalConfig (G := G) A e β) (σ e.1.2)) =
        ∑ β : EdgeBoundaryConfig (G := G) A e,
          A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β) (σ e.1.1) *
            edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
            O₂ (A.component e.1.2 (edgeRightLocalConfig (G := G) A e β)) (σ e.1.2)),
    ∃ M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ,
      (∀ c : LocalVirtualConfig A e.1.1 → ℂ,
        O₁ (localTensorMap A e.1.1 c) =
          localTensorMap A e.1.1
            (localIncidentMatrixOp A (edgeLeftIncident (G := G) e) M.transpose c)) ∧
        ∀ c : LocalVirtualConfig A e.1.2 → ℂ,
          O₂ (localTensorMap A e.1.2 c) =
            localTensorMap A e.1.2
              (localIncidentMatrixOp A (edgeRightIncident (G := G) e) M c)

/-- The original `physical_to_virtual_insertion` statement is FALSE as written:
no proof of its signature can exist, because our explicit witness
`(g3, a3, e3, id, o2bad)` satisfies all of its hypotheses yet refutes its
conclusion.
@isnad1 id=not.0h0v.s1.3478195a61a9 from=translated src=- shape=49959d42 vocab=1473ee6d
-/
theorem physical_to_virtual_insertion_statement_false :
    ¬ physicalToVirtualInsertionStatement := by
  intro hThm
  -- Build the resonate hypothesis at our witness (both sides empty sums).
  have hEq : ∀ σ : V3 → Fin 2,
      (∑ β : EdgeBoundaryConfig (G := g3) a3 e3,
        (LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))
            (a3.component e3.1.1 (edgeLeftLocalConfig (G := g3) a3 e3 β)) (σ e3.1.1) *
          edgeOpenMiddleWeight (G := g3) a3 e3 σ β.leftResidual β.rightResidual *
          a3.component e3.1.2 (edgeRightLocalConfig (G := g3) a3 e3 β) (σ e3.1.2)) =
        ∑ β : EdgeBoundaryConfig (G := g3) a3 e3,
          a3.component e3.1.1 (edgeLeftLocalConfig (G := g3) a3 e3 β) (σ e3.1.1) *
            edgeOpenMiddleWeight (G := g3) a3 e3 σ β.leftResidual β.rightResidual *
            o2bad (a3.component e3.1.2 (edgeRightLocalConfig (G := g3) a3 e3 β)) (σ e3.1.2) := by
    intro σ
    rw [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_empty]
  obtain ⟨M, _, hRight⟩ :=
    hThm a3 e3 a3_edge_blocked_three_site_injective LinearMap.id o2bad hEq
  have hRight' : ∀ c : LocalVirtualConfig a3 (1 : V3) → ℂ,
      o2bad (localTensorMap a3 (1 : V3) c) =
        localTensorMap a3 (1 : V3)
          (localIncidentMatrixOp a3 (edgeRightIncident (G := g3) e3) M c) := hRight
  have hr := hRight' (Pi.single η₀ (1 : ℂ))
  rw [local_tensor_map_one_single] at hr
  have h1 := congrFun hr 1
  rw [o2bad_apply_e0] at h1
  have hzero := local_tensor_map_one_apply_one
    ((localIncidentMatrixOp a3 (edgeRightIncident (G := g3) e3) M) (Pi.single η₀ 1))
  have hone_zero : (1 : ℂ) = 0 := by
    calc
      1 = (![0, 1] : Fin 2 → ℂ) 1 := rfl
      _ = (localTensorMap a3 1
          ((localIncidentMatrixOp a3 (edgeRightIncident (G := g3) e3) M)
            (Pi.single η₀ 1))) 1 := h1
      _ = 0 := hzero
  exact one_ne_zero hone_zero

end PhysicalToVirtualCounterexample
end PEPS
end TNLean
