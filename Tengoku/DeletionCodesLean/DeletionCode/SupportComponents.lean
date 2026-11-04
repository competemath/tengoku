import Tengoku.DeletionCodesLean.DeletionCode.RootSelection
import Tengoku.Seed.Logic.Equiv.Defs
import Tengoku.Seed.Data.Fintype.Card

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms path_connected` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms bubble_vertices_connected` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms graph_connected_owners` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms connected_iff_graph_connected` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms componentEquiv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms component_card_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms graph_component_root_subword` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Components of actual consecutive-window de Bruijn paths.

Vertices are the (L-1)-bit substrings of the family's finite word paths.
An edge is a consecutive pair of those vertices coming from a valid L-window;
it is not a clique on a bubble's vertices. If a bubble's two paths have the
same initial vertex, family connectedness agrees with connectedness of their
representatives in this graph. SignedSupport identifies this edge union with
the nonzero signed-spectrum supports of manuscript rules.
-/

namespace DeletionCode.SupportComponents

open Windows RootSelection

abbrev Vertex (L : ℕ) := Fin (L - 1) → Bool

/-- The actual vertex at a specified offset on a word path.-/
def vertex {B : Type*} (F : Family B) (L : ℕ) (b : B) (side : Bool)
    (i : ℕ) : Vertex L :=
  fun q => F.path b side (i + q.val)

/-- A vertex belongs to a bubble if it occurs on either of its finite paths.-/
def HasVertex {B : Type*} (F : Family B) (L : ℕ) (b : B) (v : Vertex L) : Prop :=
  ∃ side i, i ≤ F.extra b side + 1 ∧ v = vertex F L b side i

/-- Directed edges are precisely the consecutive vertices of valid L-windows.-/
def Edge {B : Type*} (F : Family B) (L : ℕ) (u v : Vertex L) : Prop :=
  ∃ b side i, i ≤ F.extra b side ∧
    u = vertex F L b side i ∧ v = vertex F L b side (i + 1)

/-- Undirected connectedness in the union of these actual path edges.-/
def GraphConnected {B : Type*} (F : Family B) (L : ℕ) : Vertex L → Vertex L → Prop :=
  Relation.EqvGen (Edge F L)

def representative {B : Type*} (F : Family B) (L : ℕ) (b : B) : Vertex L :=
  vertex F L b false 0

/--
@isnad1 id=iff.0h9v.s5.fb3dbf82d8e9 from=translated src=- shape=d1564d83 vocab=aaf176eb
-/
theorem vertex_eq_iff_agree {B : Type*} (F : Family B) (L : ℕ)
    (a b : B) (sa sb : Bool) (i j : ℕ) :
    vertex F L a sa i = vertex F L b sb j ↔
      Agree (F.path a sa) i (F.path b sb) j (L - 1) := by
  constructor
  · intro h q hq
    exact congrFun h ⟨q, hq⟩
  · intro h
    funext q
    exact h q.val q.isLt

/-- A path's first vertex reaches every one of its vertices via its own edges.
@isnad1 id=graphcon.1h6v.s5.ace5d04f9df1 from=translated src=- shape=0b1e9c4d vocab=a1ac35c1
-/
theorem path_connected {B : Type*} (F : Family B) (L : ℕ)
    (b : B) (side : Bool) (i : ℕ) (hi : i ≤ F.extra b side + 1) :
    GraphConnected F L (vertex F L b side 0) (vertex F L b side i) := by
  induction i with
  | zero => exact Relation.EqvGen.refl _
  | succ i ih =>
    have hprev := ih (by omega)
    have he : Edge F L (vertex F L b side i) (vertex F L b side (i + 1)) :=
      ⟨b, side, i, by omega, rfl, rfl⟩
    exact Relation.EqvGen.trans _ _ _ hprev (Relation.EqvGen.rel _ _ he)

/-- Common initial vertices connect both paths to the negative-first representative.
@isnad1 id=graphcon.2h6v.s6.5975981ef250 from=translated src=- shape=c74ecad8 vocab=a9c04da8
-/
theorem representative_connected {B : Type*} (F : Family B) (L : ℕ)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0)
    (b : B) (side : Bool) (i : ℕ) (hi : i ≤ F.extra b side + 1) :
    GraphConnected F L (representative F L b) (vertex F L b side i) := by
  cases side with
  | false => exact path_connected F L b false i hi
  | true =>
    change GraphConnected F L (vertex F L b false 0) (vertex F L b true i)
    rw [hstart b]
    exact path_connected F L b true i hi

/-- All vertices of one bubble are internally connected by its actual path edges.
@isnad1 id=graphcon.3h6v.s5.33cf22a9a57f from=translated src=- shape=78fa8002 vocab=89207e59
-/
theorem bubble_vertices_connected {B : Type*} (F : Family B) (L : ℕ)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0)
    (b : B) (u v : Vertex L) (hu : HasVertex F L b u) (hv : HasVertex F L b v) :
    GraphConnected F L u v := by
  obtain ⟨su, i, hi, rfl⟩ := hu
  obtain ⟨sv, j, hj, rfl⟩ := hv
  exact Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ (representative_connected F L hstart b su i hi))
    (representative_connected F L hstart b sv j hj)

/-- Two owners of the same concrete vertex are adjacent in the family.
@isnad1 id=adjacent.3h6v.s5.8fb0dc69b855 from=translated src=- shape=42e9688a vocab=bc40570a
-/
theorem same_vertex_adjacent {B : Type*} (F : Family B) (L : ℕ) (hL : 1 ≤ L)
    (a b : B) (v : Vertex L) (ha : HasVertex F L a v) (hb : HasVertex F L b v) :
    F.Adjacent L a b := by
  obtain ⟨sa, i, hi, hai⟩ := ha
  obtain ⟨sb, j, hj, hbj⟩ := hb
  refine ⟨sa, sb, i, j, hi, hj, by omega, by omega, ?_⟩
  exact (vertex_eq_iff_agree F L a b sa sb i j).mp (hai.symm.trans hbj)

/--
@isnad1 id=ex.1h5v.s5.f010f08d4d33 from=translated src=- shape=3287df12 vocab=1a03af78
-/
theorem edge_owners {B : Type*} (F : Family B) (L : ℕ)
    {u v : Vertex L} (h : Edge F L u v) :
    ∃ b, HasVertex F L b u ∧ HasVertex F L b v := by
  obtain ⟨b, side, i, hi, hu, hv⟩ := h
  exact ⟨b, ⟨side, i, by omega, hu⟩, ⟨side, i + 1, by omega, hv⟩⟩

/-- Graph connectedness preserves membership in the vertex union.
@isnad1 id=iff.1h5v.s5.5cf00f0e3aab from=translated src=- shape=40a8f845 vocab=74a29b46
-/
theorem supported_iff {B : Type*} (F : Family B) (L : ℕ)
    {u v : Vertex L} (h : GraphConnected F L u v) :
    (∃ b, HasVertex F L b u) ↔ (∃ b, HasVertex F L b v) := by
  induction h with
  | rel u v he =>
    obtain ⟨b, hu, hv⟩ := edge_owners F L he
    exact ⟨fun _ => ⟨b, hv⟩, fun _ => ⟨b, hu⟩⟩
  | refl u => exact Iff.rfl
  | symm u v h ih => exact ih.symm
  | trans u v w huv hvw ihu ihv => exact ihu.trans ihv

/-- A path in the consecutive-window graph joins the families owning its endpoints.
@isnad1 id=connecte.4h7v.s5.3af617f6d409 from=translated src=- shape=c9724054 vocab=cf726775
-/
theorem graph_connected_owners {B : Type*} (F : Family B) (L : ℕ) (hL : 1 ≤ L)
    {u v : Vertex L} (h : GraphConnected F L u v) :
    ∀ a b, HasVertex F L a u → HasVertex F L b v → F.Connected L a b := by
  induction h with
  | rel u v he =>
    intro a b ha hb
    obtain ⟨c, hcU, hcV⟩ := edge_owners F L he
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.rel _ _ (same_vertex_adjacent F L hL a c u ha hcU))
      (Relation.EqvGen.rel _ _ (same_vertex_adjacent F L hL c b v hcV hb))
  | refl u =>
    intro a b ha hb
    exact Relation.EqvGen.rel _ _ (same_vertex_adjacent F L hL a b u ha hb)
  | symm u v h ih =>
    intro a b ha hb
    exact Relation.EqvGen.symm _ _ (ih b a hb ha)
  | trans u v w huv hvw ihu ihv =>
    intro a b ha hb
    obtain ⟨c, hc⟩ := (supported_iff F L huv).mp ⟨a, ha⟩
    exact Relation.EqvGen.trans _ _ _ (ihu a c ha hc) (ihv c b hc hb)

/-- Sharing a true vertex joins the representatives using each bubble's path edges.
@isnad1 id=graphcon.2h5v.s5.955bc8fa6e6b from=translated src=- shape=bcacbe72 vocab=82dcdf59
-/
theorem adjacent_representatives_connected {B : Type*} (F : Family B) (L : ℕ)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0)
    {a b : B} (h : F.Adjacent L a b) :
    GraphConnected F L (representative F L a) (representative F L b) := by
  obtain ⟨sa, sb, i, j, hi, hj, _, _, hagree⟩ := h
  have heq := (vertex_eq_iff_agree F L a b sa sb i j).mpr hagree
  have ha := representative_connected F L hstart a sa i hi
  have hb := representative_connected F L hstart b sb j hj
  rw [heq] at ha
  exact Relation.EqvGen.trans _ _ _ ha (Relation.EqvGen.symm _ _ hb)

/-- Family components equal components of the actual consecutive-window edge union.
@isnad1 id=iff.2h5v.s6.27e0aa7eb42a from=translated src=- shape=6e1421db vocab=a0afb4b7
-/
theorem connected_iff_graph_connected {B : Type*} (F : Family B) (L : ℕ)
    (hL : 1 ≤ L)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0)
    (a b : B) :
    F.Connected L a b ↔
      GraphConnected F L (representative F L a) (representative F L b) := by
  constructor
  · intro h
    induction h with
    | rel a b hab => exact adjacent_representatives_connected F L hstart hab
    | refl a => exact Relation.EqvGen.refl _
    | symm a b h ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c hab hbc ihab ihbc => exact Relation.EqvGen.trans _ _ _ ihab ihbc
  · intro h
    exact graph_connected_owners F L hL h a b
      ⟨false, 0, by omega, rfl⟩ ⟨false, 0, by omega, rfl⟩

/-- The setoid of actual path-family components.-/
def componentSetoid {B : Type*} (F : Family B) (L : ℕ) : Setoid B where
  r := F.Connected L
  iseqv := ⟨fun b => Relation.EqvGen.refl b,
    fun h => Relation.EqvGen.symm _ _ h,
    fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂⟩

/-- Only vertices present on the family's paths enter the support graph.-/
def SupportedVertex {B : Type*} (F : Family B) (L : ℕ) :=
  {v : Vertex L // ∃ b, HasVertex F L b v}

/-- Graph components restricted to the actual vertex union, excluding isolated outsiders.-/
def supportedGraphSetoid {B : Type*} (F : Family B) (L : ℕ) :
    Setoid (SupportedVertex F L) where
  r := fun u v => GraphConnected F L u.val v.val
  iseqv := ⟨fun v => Relation.EqvGen.refl v.val,
    fun h => Relation.EqvGen.symm _ _ h,
    fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂⟩

abbrev Components {B : Type*} (F : Family B) (L : ℕ) :=
  Quotient (componentSetoid F L)

abbrev GraphComponents {B : Type*} (F : Family B) (L : ℕ) :=
  Quotient (supportedGraphSetoid F L)

def supportedRepresentative {B : Type*} (F : Family B) (L : ℕ) (b : B) :
    SupportedVertex F L :=
  ⟨representative F L b, b, false, 0, by omega, rfl⟩

/-- Sending a bubble to its first negative vertex induces a map of component quotients.-/
def componentMap {B : Type*} (F : Family B) (L : ℕ) (hL : 1 ≤ L)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0) :
    Components F L → GraphComponents F L :=
  Quotient.map (supportedRepresentative F L) (fun a b hab =>
    (connected_iff_graph_connected F L hL hstart a b).mp hab)

/--
@isnad1 id=injectiv.2h3v.s5.963342d28e6e from=translated src=- shape=d91fc904 vocab=5438632d
-/
theorem componentMap_injective {B : Type*} (F : Family B) (L : ℕ) (hL : 1 ≤ L)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0) :
    Function.Injective (componentMap F L hL hstart) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro a b h
  apply Quotient.sound
  apply (connected_iff_graph_connected F L hL hstart a b).mpr
  exact Quotient.exact h

/--
@isnad1 id=surjecti.2h3v.s5.2e89512295bc from=translated src=- shape=d91fc904 vocab=eb3ed9e0
-/
theorem componentMap_surjective {B : Type*} (F : Family B) (L : ℕ) (hL : 1 ≤ L)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0) :
    Function.Surjective (componentMap F L hL hstart) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro v
  obtain ⟨b, side, i, hi, hv⟩ := v.property
  refine ⟨Quotient.mk (componentSetoid F L) b, ?_⟩
  apply Quotient.sound
  change GraphConnected F L (representative F L b) v.val
  rw [hv]
  exact representative_connected F L hstart b side i hi

/-- The family and actual supported graph have exactly the same components.-/
noncomputable def componentEquiv {B : Type*} (F : Family B) (L : ℕ) (hL : 1 ≤ L)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0) :
    Components F L ≃ GraphComponents F L :=
  Equiv.ofBijective (componentMap F L hL hstart)
    ⟨componentMap_injective F L hL hstart, componentMap_surjective F L hL hstart⟩

/-- Consequently any finite cardinality representations give the same component count.
@isnad1 id=eq.2h3v.s6.7cc5c20ca542 from=translated src=- shape=ede125d5 vocab=dab0f350
-/
theorem component_card_eq {B : Type*} (F : Family B) (L : ℕ) (hL : 1 ≤ L)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0)
    [Fintype (Components F L)] [Fintype (GraphComponents F L)] :
    Fintype.card (Components F L) = Fintype.card (GraphComponents F L) :=
  Fintype.card_congr (componentEquiv F L hL hstart)

/-- Every vertex in the actual support graph reaches a root whose full negative
word occurs contiguously in x. No extra isolated ambient vertices are asserted
to have roots.
@isnad1 id=ex.4h7v.s7.15bd206f18c4 from=translated src=- shape=810a9669 vocab=d2754431
-/
theorem graph_component_root_subword {B : Type*} (F : Family B)
    (x : Letters) (n k L : ℕ) (hx : KUnique x n k) (hk : k < L)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0)
    (hgen : F.Generating x n L) (v : SupportedVertex F L) :
    ∃ r a, GraphConnected F L v.val (representative F L r) ∧
      a + (L + F.extra r false) ≤ n ∧
      Agree x a (F.path r false) 0 (L + F.extra r false) := by
  obtain ⟨b, side, i, hi, hv⟩ := v.property
  obtain ⟨r, a, hr, ha, hagree⟩ := F.component_root_subword x n k L hx hk hgen b
  have hroot := (connected_iff_graph_connected F L (by omega) hstart r b).mp hr
  have hvb : GraphConnected F L v.val (representative F L b) := by
    rw [hv]
    exact Relation.EqvGen.symm _ _ (representative_connected F L hstart b side i hi)
  exact ⟨r, a, Relation.EqvGen.trans _ _ _ hvb (Relation.EqvGen.symm _ _ hroot),
    ha, hagree⟩

end DeletionCode.SupportComponents
