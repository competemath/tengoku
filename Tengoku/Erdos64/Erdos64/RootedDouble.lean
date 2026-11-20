import Tengoku.Erdos64.Erdos64.RootedBranches

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- The root is shared by two tagged copies of the nonroot vertices.-/
abbrev RootedDoubleVertex (V : Type u) (r : V) :=
  Option (Bool × {v : V // v ≠ r})

/-- The vertex projection from the rooted double to the original graph.-/
def rootedDoubleProjection {V : Type u} {r : V} :
    RootedDoubleVertex V r → V
  | none => r
  | some (_, v) => v.1

/-- Two rooted-double vertices lie in the same copy, unless one is the shared
root.-/
def rootedDoubleCompatible {V : Type u} {r : V} :
    RootedDoubleVertex V r → RootedDoubleVertex V r → Prop
  | none, _ => True
  | _, none => True
  | some (b, _), some (b', _) => b = b'

/-- The simple graph obtained by gluing two copies of `G` at `r`.-/
def rootedDoubleGraph {V : Type u} (G : SimpleGraph V) (r : V) :
    SimpleGraph (RootedDoubleVertex V r) where
  Adj x y := G.Adj (rootedDoubleProjection x) (rootedDoubleProjection y) ∧
    rootedDoubleCompatible x y
  symm := ⟨fun x y h => by
    refine ⟨G.adj_symm h.1, ?_⟩
    cases x <;> cases y <;> simp_all [rootedDoubleCompatible]⟩
  loopless := ⟨fun x h => G.irrefl h.1⟩

noncomputable instance rootedDoubleGraph_decidableRel
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    [DecidableRel G.Adj] {r : V} :
    DecidableRel (rootedDoubleGraph G r).Adj := by
  classical
  intro x y
  infer_instance

/-- Projection is a graph homomorphism. It is intentionally not asserted to be
injective, since the two copies share all projected nonroot vertices.-/
def rootedDoubleProjectionHom {V : Type u} {G : SimpleGraph V} {r : V} :
    rootedDoubleGraph G r →g G where
  toFun := rootedDoubleProjection
  map_rel' := by
    intro x y h
    exact h.1

/-- The Boolean-tagged copy embedding of the induced nonroot graph.-/
def rootedDoubleCopyEmbedding {V : Type u} {G : SimpleGraph V} {r : V} (b : Bool) :
    (G.induce {v : V | v ≠ r}) ↪g rootedDoubleGraph G r where
  toFun v := some (b, v)
  inj' := by
    intro v w h
    have h' : (b, v) = (b, w) := Option.some.inj h
    exact congrArg Prod.snd h'
  map_rel_iff' := by
    intro v w
    change (G.Adj v.1 w.1 ∧ b = b) ↔ G.Adj v.1 w.1
    simp

@[simp] theorem rootedDoubleCopyEmbedding_apply
    {V : Type u} {G : SimpleGraph V} {r : V} (b : Bool)
    (v : {v : V // v ≠ r}) :
    rootedDoubleCopyEmbedding (G := G) b v = some (b, v) :=
  rfl

/-- The rooted double has `2 * s - 1` vertices when the original graph has
`s` vertices.-/
theorem rootedDouble_card
    {V : Type u} [Fintype V] [DecidableEq V] {r : V} :
    Fintype.card (RootedDoubleVertex V r) = 2 * Fintype.card V - 1 := by
  classical
  have hcard : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨r⟩
  simp [RootedDoubleVertex, Fintype.card_subtype_compl]
  omega

/-- The projection preserves every walk length.-/
theorem rootedDouble_projection_length
    {V : Type u} {G : SimpleGraph V} {r : V}
    {x y : RootedDoubleVertex V r}
    (p : (rootedDoubleGraph G r).Walk x y) :
    (p.map rootedDoubleProjectionHom).length = p.length := by
  simp

/-- A conditional projection lemma requiring global injectivity. If there is
any nonroot vertex, its two tagged copies have the same projection, so this
premise fails. This is therefore not a usable cycle-projection route for a
nontrivial rooted double. `rootedDouble_cycle_projection` in
`RootedDoubleProjection.lean` uses injectivity on the cycle support instead.-/
theorem rootedDouble_projection_cycle_of_injective
    {V : Type u} {G : SimpleGraph V} {r : V}
    {x : RootedDoubleVertex V r}
    (p : (rootedDoubleGraph G r).Walk x x)
    (hp : p.IsCycle)
    (hinj : Function.Injective
      (rootedDoubleProjectionHom (G := G) : RootedDoubleVertex V r → V)) :
    (p.map rootedDoubleProjectionHom).IsCycle := by
  exact hp.map hinj

/-- A support-local injectivity contract is enough for projection of a path;
the caller must provide the support injectivity because the collapse map is not
globally injective.-/
theorem rootedDouble_projection_path_of_support_injective
    {V : Type u} {G : SimpleGraph V} {r : V}
    {x y : RootedDoubleVertex V r}
    (p : (rootedDoubleGraph G r).Walk x y)
    (hp : p.IsPath)
    (hinj : Set.InjOn rootedDoubleProjection {v | v ∈ p.support}) :
    (p.map rootedDoubleProjectionHom).IsPath := by
  rw [SimpleGraph.Walk.isPath_def]
  rw [SimpleGraph.Walk.support_map]
  exact List.Nodup.map_on hinj hp.support_nodup

/-- Historical localization interface: return the supplied assertion that
every nonroot support vertex carries the displayed copy tag. This theorem
does not derive localization. `rootedDouble_cycle_common_tag` in
`RootedDoubleTagLocalization.lean` derives a common tag for every simple cycle.-/
theorem rootedDouble_cycle_localization_of
    {V : Type u} {G : SimpleGraph V} {r : V}
    {x : RootedDoubleVertex V r}
    (p : (rootedDoubleGraph G r).Walk x x)
    (hp : p.IsCycle) (b : Bool)
    (hcopy : ∀ z, z ∈ p.support → z ≠ none →
      ∃ v, z = some (b, v)) :
    ∀ z, z ∈ p.support → z ≠ none →
      ∃ v, z = some (b, v) :=
  hcopy

/-- Convert a supplied neighbor equivalence into nonroot degree preservation.
`rootedDouble_nonroot_degree_preservation` in `RootedDoubleNonroot.lean`
constructs the equivalence and discharges this condition.-/
theorem rootedDouble_nonroot_degree_preservation_of_neighborEquiv
    {V : Type u} {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] {r : V}
    (b : Bool) (v : {v : V // v ≠ r})
    (e : (rootedDoubleGraph G r).neighborSet (some (b, v)) ≃
      G.neighborSet v.1) :
    (rootedDoubleGraph G r).degree (some (b, v)) = G.degree v.1 :=
  by
    rw [← SimpleGraph.card_neighborSet_eq_degree,
      ← SimpleGraph.card_neighborSet_eq_degree]
    exact Fintype.card_congr e

/-- Convert a supplied neighbor equivalence into root degree doubling.
`rootedDouble_root_degree_doubling` in `RootedDoubleNeighbors.lean`
constructs the equivalence and discharges this condition.-/
theorem rootedDouble_root_degree_doubling_of_neighborEquiv
    {V : Type u} {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] {r : V}
    (e : (rootedDoubleGraph G r).neighborSet none ≃
      Bool × G.neighborSet r) :
    (rootedDoubleGraph G r).degree none = 2 * G.degree r :=
  by
    rw [← SimpleGraph.card_neighborSet_eq_degree,
      ← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_congr e,
      Fintype.card_prod, Fintype.card_bool]

end Erdos64
