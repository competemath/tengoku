import Tengoku.Linearhadwiger.HadwigerLean.Woven.RedundantMenger
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Paired source vertices for mixed fans

Each auxiliary vertex is joined to two prescribed original sources.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} {a : ℕ}

abbrev PairedFanVertex (V : Type*) (a : ℕ) := V ⊕ Fin a

/-- Add one auxiliary vertex for each pair of prescribed source vertices.-/
def pairedFanGraph (G : SimpleGraph V) (source : Fin a × Fin 2 → V) :
    SimpleGraph (PairedFanVertex V a) where
  Adj x y := match x, y with
    | .inl u, .inl v => G.Adj u v
    | .inr i, .inl v => ∃ b, source (i,b) = v
    | .inl v, .inr i => ∃ b, source (i,b) = v
    | .inr _, .inr _ => False
  symm := by
    constructor
    intro x y h
    cases x with
    | inl u =>
      cases y with
      | inl v => exact h.symm
      | inr i => exact h
    | inr i =>
      cases y with
      | inl v => exact h
      | inr j => exact h
  loopless := by
    constructor
    intro x h
    cases x with
    | inl v => exact G.irrefl h
    | inr i => exact h

/-- The old graph is embedded as the left summand.-/
def pairedFanLeftEmbedding (G : SimpleGraph V)
    (source : Fin a × Fin 2 → V) :
    G ↪g pairedFanGraph G source where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := by
    intro u v
    rfl

/--
@isnad1 id=iff.0h6v.s5.2db582d056a9 from=translated src=- shape=3cdcf38b vocab=fc27ce22
-/
@[simp] theorem pairedFanGraph_left_adj
    (G : SimpleGraph V) (source : Fin a × Fin 2 → V) (u v : V) :
    (pairedFanGraph G source).Adj (.inl u) (.inl v) ↔ G.Adj u v :=
  Iff.rfl

/--
@isnad1 id=iff.0h6v.s6.7dcaa42436e8 from=translated src=- shape=6ea41069 vocab=f5176c7e
-/
@[simp] theorem pairedFanGraph_right_left_adj
    (G : SimpleGraph V) (source : Fin a × Fin 2 → V)
    (i : Fin a) (v : V) :
    (pairedFanGraph G source).Adj (.inr i) (.inl v) ↔
      ∃ b, source (i,b) = v :=
  Iff.rfl

/-- The two prescribed spokes of each auxiliary source.
@isnad1 id=adj.0h6v.s5.d0004242292d from=translated src=- shape=322a47b0 vocab=f5176c7e
-/
theorem pairedFanGraph_spoke
    (G : SimpleGraph V) (source : Fin a × Fin 2 → V)
    (i : Fin a) (b : Fin 2) :
    (pairedFanGraph G source).Adj (.inr i) (.inl (source (i,b))) :=
  ⟨b,rfl⟩

/-- Prepend one auxiliary spoke to an original path.-/
def pairedFanSpokePath (G : SimpleGraph V)
    (source : Fin a × Fin 2 → V) (i : Fin a) (b : Fin 2)
    {t : V} (p : G.Path (source (i,b)) t) :
    (pairedFanGraph G source).Path (.inr i) (.inl t) := by
  let q : (pairedFanGraph G source).Path (.inl (source (i,b))) (.inl t) :=
    p.mapEmbedding (pairedFanLeftEmbedding G source)
  have hnot : (Sum.inr i : PairedFanVertex V a) ∉
      (q : (pairedFanGraph G source).Walk
        (.inl (source (i,b))) (.inl t)).support := by
    simp [q, SimpleGraph.Walk.support_map, pairedFanLeftEmbedding]
  exact ⟨SimpleGraph.Walk.cons (pairedFanGraph_spoke G source i b) q.1,
    q.property.cons hnot⟩

/-- The synthetic start is the only auxiliary vertex of a spoke path.
@isnad1 id=eq.0h8v.s7.1a60ede74429 from=translated src=- shape=07761b67 vocab=d01eaebd
-/
theorem pairedFanSpokePath_support
    (G : SimpleGraph V) (source : Fin a × Fin 2 → V)
    (i : Fin a) (b : Fin 2) {t : V}
    (p : G.Path (source (i,b)) t) :
    pathVertexSet (pairedFanSpokePath G source i b p) =
      {(Sum.inr i : PairedFanVertex V a)} ∪
        Sum.inl '' pathVertexSet p := by
  ext x
  simp [pairedFanSpokePath, pathVertexSet, SimpleGraph.Walk.support_cons,
    SimpleGraph.Walk.support_map, pairedFanLeftEmbedding]

/-- Old vertices and new paired sources, as finite subsets of the enlarged graph.-/
noncomputable def pairedFanLeftSet [DecidableEq V] (A : Finset V) :
    Finset (PairedFanVertex V a) := by
  classical
  exact A.image Sum.inl

noncomputable def pairedFanRightSet [DecidableEq V] : Finset (PairedFanVertex V a) := by
  classical
  exact Finset.univ.image Sum.inr

/--
@isnad1 id=iff.0h4v.s5.995c1b9165fa from=translated src=- shape=1aac1249 vocab=515bd0e5
-/
@[simp] theorem mem_pairedFanLeftSet [DecidableEq V] (A : Finset V) (v : V) :
    (Sum.inl v : PairedFanVertex V a) ∈ pairedFanLeftSet A ↔ v ∈ A := by
  classical
  simp [pairedFanLeftSet]

/--
@isnad1 id=mem.0h3v.s5.ced65b829199 from=translated src=- shape=2f233498 vocab=51571958
-/
@[simp] theorem mem_pairedFanRightSet [DecidableEq V] (i : Fin a) :
    (Sum.inr i : PairedFanVertex V a) ∈ pairedFanRightSet := by
  classical
  simp [pairedFanRightSet]

/-- Recover an original vertex from the left finite set.-/
noncomputable def pairedFanLeftDecode [DecidableEq V]
    (A : Finset V) (x : pairedFanLeftSet (a := a) A) : A := by
  classical
  let h := Finset.mem_image.mp x.2
  exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩

/--
@isnad1 id=eq.0h4v.s6.c4178d78c137 from=translated src=- shape=bd9be7f8 vocab=904cee26
-/
theorem pairedFanLeftDecode_spec [DecidableEq V]
    (A : Finset V) (x : pairedFanLeftSet (a := a) A) :
    Sum.inl (pairedFanLeftDecode A x).1 = x.1 := by
  classical
  unfold pairedFanLeftDecode
  exact (Classical.choose_spec (Finset.mem_image.mp x.2)).2

/--
@isnad1 id=eq.0h4v.s6.41988c3a0c39 from=translated src=- shape=e571a58b vocab=910d8d6b
-/
@[simp] theorem pairedFanLeftDecode_encode [DecidableEq V]
    (A : Finset V) (v : A) :
    (pairedFanLeftDecode (a := a) A
      ⟨Sum.inl v.1, mem_pairedFanLeftSet A v.1 |>.2 v.2⟩).1 = v.1 := by
  exact Sum.inl_injective (pairedFanLeftDecode_spec A _)
/-- An embedded original path has exactly the embedded original support.
@isnad1 id=eq.0h7v.s7.cf3539aaa174 from=translated src=- shape=d75a42f9 vocab=c6558c96
-/
theorem pairedFanMapPath_support
    (G : SimpleGraph V) (source : Fin a × Fin 2 → V)
    {s t : V} (p : G.Path s t) :
    pathVertexSet (p.mapEmbedding (pairedFanLeftEmbedding G source)) =
      Sum.inl '' pathVertexSet p := by
  ext x
  simp [pathVertexSet, SimpleGraph.Walk.support_map, pairedFanLeftEmbedding]

/-- Recover the auxiliary pair index from the right finite set.-/
noncomputable def pairedFanRightDecode [DecidableEq V]
    (x : pairedFanRightSet (V := V) (a := a)) : Fin a := by
  classical
  let h := Finset.mem_image.mp x.2
  exact Classical.choose h

/--
@isnad1 id=eq.0h3v.s6.362a37b3430d from=translated src=- shape=94899899 vocab=8420d342
-/
theorem pairedFanRightDecode_spec [DecidableEq V]
    (x : pairedFanRightSet (V := V) (a := a)) :
    Sum.inr (pairedFanRightDecode x) = x.1 := by
  classical
  unfold pairedFanRightDecode
  exact (Classical.choose_spec (Finset.mem_image.mp x.2)).2

/--
@isnad1 id=eq.0h3v.s5.7307077d5f03 from=translated src=- shape=280b88a0 vocab=848d9b20
-/
@[simp] theorem pairedFanRightDecode_encode [DecidableEq V] (i : Fin a) :
    pairedFanRightDecode
      (⟨Sum.inr i, mem_pairedFanRightSet i⟩ :
        pairedFanRightSet (V := V) (a := a)) = i :=
  Sum.inr_injective (pairedFanRightDecode_spec _)

/--
@isnad1 id=eq.0h2v.s4.f4dcdc1ce644 from=translated src=- shape=1cd84954 vocab=1b00d631
-/
theorem pairedFanRightSet_card [Fintype V] [DecidableEq V] :
    (pairedFanRightSet (V := V) (a := a)).card = a := by
  classical
  unfold pairedFanRightSet
  rw [Finset.card_image_of_injective]
  · simp
  · exact Sum.inr_injective

/--
@isnad1 id=disjoint.0h3v.s5.449e05ab164e from=translated src=- shape=1e1e7afe vocab=350891b1
-/
theorem pairedFanLeftRight_disjoint [DecidableEq V] (A : Finset V) :
    Disjoint (pairedFanLeftSet (a := a) A)
      (pairedFanRightSet (V := V) (a := a)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hy
  cases hi

/-- Lift a path whose start is represented by a left-set vertex.-/
noncomputable def pairedFanLiftPath [DecidableEq V]
    (G : SimpleGraph V) (source : Fin a × Fin 2 → V)
    (A : Finset V) (x : pairedFanLeftSet (a := a) A)
    {t : V} (p : G.Path (pairedFanLeftDecode A x).1 t) :
    (pairedFanGraph G source).Path x.1 (.inl t) := by
  let q : (pairedFanGraph G source).Path
      (.inl (pairedFanLeftDecode A x).1) (.inl t) :=
    p.mapEmbedding (pairedFanLeftEmbedding G source)
  have hs : Sum.inl (pairedFanLeftDecode A x).1 = x.1 :=
    pairedFanLeftDecode_spec A x
  exact ⟨(q : (pairedFanGraph G source).Walk
    (.inl (pairedFanLeftDecode A x).1) (.inl t)).copy hs rfl,
    by simpa using q.property⟩

/--
@isnad1 id=eq.0h8v.s7.fec70ca30a6a from=translated src=- shape=2dd92fb0 vocab=4bdf1e18
-/
theorem pairedFanLiftPath_support [DecidableEq V]
    (G : SimpleGraph V) (source : Fin a × Fin 2 → V)
    (A : Finset V) (x : pairedFanLeftSet (a := a) A)
    {t : V} (p : G.Path (pairedFanLeftDecode A x).1 t) :
    pathVertexSet (pairedFanLiftPath G source A x p) =
      Sum.inl '' pathVertexSet p := by
  ext v
  simp [pairedFanLiftPath, pathVertexSet, SimpleGraph.Walk.support_copy,
    pairedFanMapPath_support, SimpleGraph.Walk.support_map, pairedFanLeftEmbedding]

/-- Decode both the old source and the duplicate-path index.-/
noncomputable def pairedFanSlotDecode [DecidableEq V]
    (A : Finset V) :
    pairedFanLeftSet (a := a) A × Fin 2 → A × Fin 2 :=
  fun slot => (pairedFanLeftDecode A slot.1, slot.2)

/--
@isnad1 id=injectiv.0h3v.s6.a76849aa0ff2 from=translated src=- shape=aa477478 vocab=5f704fc1
-/
theorem pairedFanSlotDecode_injective [DecidableEq V]
    (A : Finset V) : Function.Injective (pairedFanSlotDecode (a := a) A) := by
  intro x y h
  apply Prod.ext
  · apply Subtype.ext
    have hv := congrArg (fun slot : A × Fin 2 => slot.1.1) h
    have hx := pairedFanLeftDecode_spec A x.1
    have hy := pairedFanLeftDecode_spec A y.1
    exact hx.symm.trans (congrArg Sum.inl hv |>.trans hy)
  · exact congrArg (fun slot : A × Fin 2 => slot.2) h

noncomputable def pairedFanRightSlotDecode [DecidableEq V] :
    pairedFanRightSet (V := V) (a := a) × Fin 2 → Fin a × Fin 2 :=
  fun slot => (pairedFanRightDecode slot.1, slot.2)

/--
@isnad1 id=injectiv.0h2v.s5.ae929fe721d4 from=translated src=- shape=3a75beac vocab=db0dfa1c
-/
theorem pairedFanRightSlotDecode_injective [DecidableEq V] :
    Function.Injective (pairedFanRightSlotDecode (V := V) (a := a)) := by
  intro x y h
  apply Prod.ext
  · apply Subtype.ext
    have hv := congrArg (fun slot : Fin a × Fin 2 => slot.1) h
    have hx := pairedFanRightDecode_spec x.1
    have hy := pairedFanRightDecode_spec y.1
    exact hx.symm.trans (congrArg Sum.inr hv |>.trans hy)
  · exact congrArg (fun slot : Fin a × Fin 2 => slot.2) h

/-- A spoke path indexed by the right-source finite set.-/
noncomputable def pairedFanRightSpokePath [DecidableEq V]
    (G : SimpleGraph V) (source : Fin a × Fin 2 → V)
    (slot : pairedFanRightSet (V := V) (a := a) × Fin 2)
    {t : V} (p : G.Path (source (pairedFanRightSlotDecode slot)) t) :
    (pairedFanGraph G source).Path slot.1.1 (.inl t) := by
  let q := pairedFanSpokePath G source
    (pairedFanRightDecode slot.1) slot.2 p
  have hs : Sum.inr (pairedFanRightDecode slot.1) = slot.1.1 :=
    pairedFanRightDecode_spec slot.1
  exact ⟨(q : (pairedFanGraph G source).Walk _ _).copy hs rfl,
    by simpa using q.property⟩

/--
@isnad1 id=eq.0h7v.s8.7096e6665102 from=translated src=- shape=fb15fb9d vocab=9e775660
-/
theorem pairedFanRightSpokePath_support [DecidableEq V]
    (G : SimpleGraph V) (source : Fin a × Fin 2 → V)
    (slot : pairedFanRightSet (V := V) (a := a) × Fin 2)
    {t : V} (p : G.Path (source (pairedFanRightSlotDecode slot)) t) :
    pathVertexSet (pairedFanRightSpokePath G source slot p) =
      {slot.1.1} ∪ Sum.inl '' pathVertexSet p := by
  calc
    pathVertexSet (pairedFanRightSpokePath G source slot p) =
        pathVertexSet (pairedFanSpokePath G source
          (pairedFanRightDecode slot.1) slot.2 p) := by
      simp [pairedFanRightSpokePath, pathVertexSet,
        SimpleGraph.Walk.support_copy]
    _ = {(Sum.inr (pairedFanRightDecode slot.1) : PairedFanVertex V a)} ∪
        Sum.inl '' pathVertexSet p :=
      pairedFanSpokePath_support G source
        (pairedFanRightDecode slot.1) slot.2 p
    _ = {slot.1.1} ∪ Sum.inl '' pathVertexSet p := by
      rw [pairedFanRightDecode_spec]

/--
@isnad1 id=eq.0h3v.s4.b9bba78bc7d7 from=translated src=- shape=917fa2a3 vocab=724f7910
-/
theorem pairedFanLeftSet_card [Fintype V] [DecidableEq V] (A : Finset V) :
    (pairedFanLeftSet (a := a) A).card = A.card := by
  classical
  unfold pairedFanLeftSet
  rw [Finset.card_image_of_injective]
  exact Sum.inl_injective
end Woven
end HadwigerLean
