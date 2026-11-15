import Tengoku.FltAnthropic.Definitions.Def_LatticeTreeOrbital
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Tengoku.Seed.Combinatorics.SimpleGraph.Basic
import Tengoku.Seed.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
noncomputable section

open scoped MatrixGroups

namespace CerednikDrinfeld
namespace BruhatTits

open Mumford LT.LatticeTree

namespace _root_.CerednikDrinfeld.Mumford

variable {G : Type} [Group G] {W : Type} [MulAction G W] {𝒯 : SimpleGraph W}

instance GraphAction.subgroup (H : Subgroup G) [GraphAction G 𝒯] : GraphAction H 𝒯 :=
  ⟨fun h _ _ hadj => GraphAction.smul_adj (h : G) hadj⟩

theorem GraphAction.of_compHom {G' : Type} [Group G'] (φ : G' →* G) [GraphAction G 𝒯] :
    @GraphAction G' _ W (MulAction.compHom W φ) 𝒯 :=
  @GraphAction.mk G' _ W (MulAction.compHom W φ) 𝒯 fun g _ _ hadj => GraphAction.smul_adj (φ g) hadj

end _root_.CerednikDrinfeld.Mumford

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]

instance instMulActionGLVertex : MulAction (GL (Fin 2) K) (Vertex R K) where
  smul := Vertex.act
  one_smul := Vertex.act_one
  mul_smul := Vertex.act_mul

/--
@isnad1 id=eq.0h4v.s8.9dc4396541f9 from=translated src=- shape=1744752f vocab=c578cedc
-/
theorem gl_smul_def (g : GL (Fin 2) K) (v : Vertex R K) : g • v = Vertex.act g v := rfl

/--
@isnad1 id=eq.1h4v.s8.857ad3983d6e from=translated src=- shape=2049ebc5 vocab=2b31ad4c
-/
@[simp] theorem gl_smul_mk (g : GL (Fin 2) K) (L : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) :
    g • Vertex.mk R K L hL = Vertex.mk R K (latticeMap g L) (hL.map g) := rfl

variable (R K) in

def vertPermHom : GL (Fin 2) K →* Equiv.Perm (Vertex R K) := MulAction.toPermHom (GL (Fin 2) K) (Vertex R K)

/--
@isnad1 id=eq.0h4v.s9.d58d4d2ca94c from=translated src=- shape=35a2241d vocab=1105bdaf
-/
@[simp] theorem vertPermHom_apply (g : GL (Fin 2) K) (x : Vertex R K) : vertPermHom R K g x = g • x := rfl

/--
@isnad1 id=eq.0h2v.s8.692bf2ddcd9d from=translated src=- shape=45ea4f37 vocab=1899a957
-/
theorem scalar_eq_scalarGL (c : Kˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2) c = scalarGL c := by
  ext i j
  simp [Matrix.GeneralLinearGroup.coe_scalar, scalarGL_coe, Matrix.one_apply, Matrix.diagonal_apply]

/--
@isnad1 id=eq.0h4v.s9.d2a2444c1dbe from=translated src=- shape=052a0b2c vocab=5dfd689f
-/
theorem scalar_smul_vertex (c : Kˣ) (v : Vertex R K) : Matrix.GeneralLinearGroup.scalar (Fin 2) c • v = v := by
  rw [scalar_eq_scalarGL]
  exact isFixedVertex_scalarGL c v

/--
@isnad1 id=mem.0h3v.s9.5f6a7c2f1dc7 from=translated src=- shape=ef5324e3 vocab=5034e0b7
-/
theorem scalar_mem_ker_vertPermHom (c : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c ∈ (vertPermHom R K).ker := by
  rw [MonoidHom.mem_ker]
  ext x
  simp [scalar_smul_vertex]

instance instMulActionPGLVertex : MulAction (Matrix.ProjGenLinGroup (Fin 2) K) (Vertex R K) :=
  Matrix.ProjGenLinGroup.mulActionOfGL fun c v => scalar_smul_vertex c v

/--
@isnad1 id=eq.0h4v.s10.e56b225a074d from=translated src=- shape=65678452 vocab=158ad538
-/
@[simp] theorem pgl_mk_smul (g : GL (Fin 2) K) (v : Vertex R K) : Matrix.ProjGenLinGroup.mk g • v = g • v := rfl

variable [IsFractionRing R K]

/--
@isnad1 id=adjacent.1h5v.s8.144bd40e19f2 from=translated src=- shape=830439d5 vocab=17de187f
-/
theorem adjacentLattice_latticeMap (g : GL (Fin 2) K) {L L' : Submodule R (Fin 2 → K)}
    (h : AdjacentLattice L L') : AdjacentLattice (latticeMap g L) (latticeMap g L') := by
  obtain ⟨ϖ, hϖ, h₁, h₂⟩ := h
  refine ⟨ϖ, hϖ, ?_, (latticeMap_lt_latticeMap_iff g).2 h₂⟩
  rw [← latticeMap_mul, scalarGL_mul_comm, latticeMap_mul]
  exact (latticeMap_lt_latticeMap_iff g).2 h₁

variable (R K) in

def VertRel (x y : Vertex R K) : Prop :=
  ∃ (L L' : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) (hL' : IsFullLattice L'),
    Vertex.mk R K L hL = x ∧ Vertex.mk R K L' hL' = y ∧ AdjacentLattice L L'

variable (R K) in

def tree : SimpleGraph (Vertex R K) := SimpleGraph.fromRel (VertRel R K)

/--
@isnad1 id=iff.0h4v.s6.1b50bbb09cd7 from=translated src=- shape=2bdede00 vocab=ffb06881
-/
theorem tree_adj_iff (x y : Vertex R K) :
    (tree R K).Adj x y ↔ x ≠ y ∧ (VertRel R K x y ∨ VertRel R K y x) :=
  SimpleGraph.fromRel_adj _ _ _

/--
@isnad1 id=vertrel.1h5v.s9.5aac2fe306d0 from=translated src=- shape=04851c6a vocab=e75a47e2
-/
theorem VertRel.gl_smul (g : GL (Fin 2) K) {x y : Vertex R K} (h : VertRel R K x y) :
    VertRel R K (g • x) (g • y) := by
  obtain ⟨L, L', hL, hL', rfl, rfl, hLL'⟩ := h
  exact ⟨latticeMap g L, latticeMap g L', hL.map g, hL'.map g, rfl, rfl, adjacentLattice_latticeMap g hLL'⟩

/--
@isnad1 id=graphact.0h2v.s7.306425e47832 from=translated src=- shape=b080b699 vocab=71ac2c7b
-/
instance instGraphActionGLTree : GraphAction (GL (Fin 2) K) (tree R K) where
  smul_adj g {x y} h := by
    rw [tree_adj_iff] at h ⊢
    refine ⟨fun hxy => h.1 (MulAction.injective g hxy), ?_⟩
    exact h.2.imp (VertRel.gl_smul g) (VertRel.gl_smul g)

/--
@isnad1 id=graphact.0h2v.s6.25ee570e55e5 from=translated src=- shape=b080b699 vocab=c875842a
-/
instance instGraphActionPGLTree : GraphAction (Matrix.ProjGenLinGroup (Fin 2) K) (tree R K) where
  smul_adj q {x y} h := by
    induction q using Matrix.ProjGenLinGroup.induction_on with | mk g => ?_
    rw [pgl_mk_smul, pgl_mk_smul]
    exact GraphAction.smul_adj g h

end BruhatTits
end CerednikDrinfeld
end
