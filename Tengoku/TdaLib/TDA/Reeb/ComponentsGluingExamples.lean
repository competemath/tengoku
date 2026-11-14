import Tengoku.TdaLib.TDA.Reeb.ComponentsGluing
import Tengoku.TdaLib.TDA.Reeb.ComponentsCoverExamples
import Tengoku.TdaLib.TDA.Reeb.ComponentsExamples

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Component gluing fixtures

Regression fixtures for `TDA.Reeb.ComponentsGluing`:

* two overlapping intervals, `twoOpens` from `TDA.Reeb.ComponentsCoverExamples`: the classes of
  `0` and `1` are related through overlap steps, and the colimit form over `ℝ`;
* a disjoint cover of `ℝ \ {0}` by `(-∞, 0)` and `(0, ∞)`: the classes of `-1` and `1` differ,
  so gluing makes no false identification;
* the empty cover, which forces the empty value, and gluing along it over `⊥`;
* the empty open with a nonempty cover;
* duplicate indices: `⊤` twice;
* a `Sort`-indexed cover, reindexed explicitly through `PLift`;
* naturality at the collapse `boolToUnit` of `TDA.Reeb.ComponentsExamples`: the glue of a
  pulled-back family factors through the collapse and identifies two distinct classes.
-/

open CategoryTheory Limits TDA.Topology

namespace TDA.Reeb.Examples

open Set

-- `twoOpens` and `twoOpens_cover` are reused from `TDA.Reeb.ComponentsCoverExamples`.

/-- Two overlapping intervals: the class of `0` over `(-∞, 2/3)` and the class of `1` over
`(1/3, ∞)` are related through overlap steps.
@isnad1 id=eqvgen.0h0v.s9.36fa4cd0f59c from=translated src=- shape=4a199e66 vocab=b8ecc8c0
-/
theorem twoOpens_classes_related :
    Relation.EqvGen (overlapRel (componentFunctor (ContinuousMap.id ℝ)) twoOpens)
      ⟨false, ZerothHomotopy.mk ⟨0, show (0 : ℝ) < 2 / 3 by norm_num⟩⟩
      ⟨true, ZerothHomotopy.mk ⟨1, show (1 / 3 : ℝ) < 1 by norm_num⟩⟩ := by
  refine (componentFunctor_map_eq_iff_eqvGen (ContinuousMap.id ℝ) twoOpens
    (fun _ => le_top) twoOpens_cover _ _).1 ?_
  simp only [componentFunctor_map_mk]
  exact ZerothHomotopy.sound
    { toFun := fun s => ⟨(s : ℝ), TopologicalSpace.Opens.mem_top _⟩
      continuous_toFun := continuous_subtype_val.subtype_mk _
      source' := rfl
      target' := rfl }

/-- Two overlapping intervals: the colimit form over `W = ℝ`.
@isnad1 id=nonempty.0h0v.s8.a3698b18bca5 from=translated src=- shape=f3d6f57a vocab=df9ed385
-/
theorem twoOpens_isColimit :
    Nonempty (IsColimit ((componentFunctor (ContinuousMap.id ℝ)).mapCocone
      (coverCocone twoOpens (W := ⊤) (fun _ => le_top)))) :=
  componentFunctor_isColimit_coverCocone _ twoOpens _ twoOpens_cover

/-- `(-∞, 0)` and `(0, ∞)`: a disjoint cover of the disconnected `ℝ \ {0}`.-/
def negPos : Bool → TopologicalSpace.Opens ℝ
  | false => ⟨Iio 0, isOpen_Iio⟩
  | true => ⟨Ioi 0, isOpen_Ioi⟩

/--
@isnad1 id=eq.1h2v.s8.75bdd5e81041 from=translated src=- shape=c78993be vocab=06f9c93f
-/
theorem negPos_overlapRel_fst {p q : Σ b, (componentFunctor (ContinuousMap.id ℝ)).obj (negPos b)}
    (h : overlapRel (componentFunctor (ContinuousMap.id ℝ)) negPos p q) : p.1 = q.1 := by
  obtain ⟨c, -, -⟩ := h
  induction c using ZerothHomotopy.rec with
  | mk z =>
    obtain ⟨z, hz⟩ := z
    rw [TopologicalSpace.Opens.mem_inf] at hz
    obtain ⟨hp, hq⟩ := hz
    rcases p with ⟨_ | _, _⟩ <;> rcases q with ⟨_ | _, _⟩
    · rfl
    · exact absurd (lt_trans (show (0 : ℝ) < z from hq) (show z < 0 from hp)) (lt_irrefl _)
    · exact absurd (lt_trans (show (0 : ℝ) < z from hp) (show z < 0 from hq)) (lt_irrefl _)
    · rfl

/-- Disjoint cover: no false identification. The classes of `-1` and `1` over `ℝ \ {0}` differ,
proved through the gluing kernel (the overlap relation never changes the member).
@isnad1 id=ne.0h0v.s11.adbb9ca27275 from=translated src=- shape=599b452f vocab=0564c87b
-/
theorem negPos_classes_ne :
    (componentFunctor (ContinuousMap.id ℝ)).map (homOfLE (le_iSup negPos false))
        (ZerothHomotopy.mk ⟨-1, show (-1 : ℝ) < 0 by norm_num⟩) ≠
      (componentFunctor (ContinuousMap.id ℝ)).map (homOfLE (le_iSup negPos true))
        (ZerothHomotopy.mk ⟨1, show (0 : ℝ) < 1 by norm_num⟩) := by
  intro h
  have hR := (componentFunctor_map_eq_iff_eqvGen (ContinuousMap.id ℝ) negPos
    (le_iSup negPos) le_rfl _ _).1 h
  have key : ∀ p q, Relation.EqvGen (overlapRel (componentFunctor (ContinuousMap.id ℝ)) negPos)
      p q → p.1 = q.1 := by
    intro p q hpq
    induction hpq with
    | rel _ _ h => exact negPos_overlapRel_fst h
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact Bool.false_ne_true (key _ _ hR)

/-- Empty cover: it forces the empty value over the covered open.
@isnad1 id=isempty.1h5v.s6.90033dd15b55 from=translated src=- shape=ed7961df vocab=2498c18c
-/
theorem emptyCover_isEmpty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    {W : TopologicalSpace.Opens Y} (U : Empty → TopologicalSpace.Opens Y)
    (hcov : W ≤ ⨆ i, U i) : IsEmpty ((componentFunctor f).obj W) :=
  ⟨fun x => by
    obtain ⟨i, -, -⟩ := componentFunctor_exists_map_eq f U (fun i => i.elim) hcov x
    exact i.elim⟩

/-- Empty cover of the empty open: gluing holds (the unique map out of the empty value).
@isnad1 id=existsun.0h6v.s9.a6afb4ff306c from=translated src=- shape=59bd5378 vocab=07ad08cb
-/
theorem emptyCover_existsUnique_glue {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {A : Sort*} (U : Empty → TopologicalSpace.Opens Y)
    (a : ∀ i, (componentFunctor f).obj (U i) → A) :
    ∃! g : (componentFunctor f).obj ⊥ → A,
      ∀ i (e : (componentFunctor f).obj (U i)),
        g ((componentFunctor f).map (homOfLE (i.elim : U i ≤ ⊥)) e) = a i e :=
  componentFunctor_existsUnique_glue f U (fun i => i.elim) bot_le a (fun i => i.elim)

/-- Empty open with a nonempty cover: colimit form over `W = ⊥`.
@isnad1 id=nonempty.0h3v.s8.70ad62207339 from=translated src=- shape=e5defab0 vocab=4a5f39d4
-/
theorem bot_isColimit {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    Nonempty (IsColimit ((componentFunctor f).mapCocone
      (coverCocone (fun _ : Unit => (⊥ : TopologicalSpace.Opens Y)) (W := ⊥) (fun _ => le_rfl)))) :=
  componentFunctor_isColimit_coverCocone f _ _ bot_le

/-- Duplicate indices: the same open twice; local classes of one point are related.
@isnad1 id=eqvgen.0h0v.s11.fbdee7bf1643 from=translated src=- shape=f82d01a0 vocab=1d90e9ec
-/
theorem dupCover_related :
    Relation.EqvGen
      (overlapRel (componentFunctor (ContinuousMap.id ℝ)) (fun _ : Bool => ⊤))
      ⟨false, ZerothHomotopy.mk ⟨0, trivial⟩⟩ ⟨true, ZerothHomotopy.mk ⟨0, trivial⟩⟩ :=
  .rel _ _ (overlapRel_mk _ (fun _ : Bool => ⊤) 0 trivial trivial)

/--
@isnad1 id=nonempty.0h0v.s9.9dfa5bd3b650 from=translated src=- shape=793899fc vocab=1c67ab93
-/
theorem dupCover_isColimit :
    Nonempty (IsColimit ((componentFunctor (ContinuousMap.id ℝ)).mapCocone
      (Pairwise.cocone (fun _ : Bool => (⊤ : TopologicalSpace.Opens ℝ))))) :=
  componentFunctor_isPairwiseCosheaf _ _

/-- `Sort`-indexed covers reindex explicitly through `PLift`, with no smallness assumption.
@isnad1 id=existsun.3h8v.s10.e0702dd6e829 from=translated src=- shape=2bed4db6 vocab=cd303851
-/
theorem existsUnique_glue_sort {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {κ : Sort*} (f : C(X, Y)) {W : TopologicalSpace.Opens Y} (U : κ → TopologicalSpace.Opens Y)
    (hU : ∀ i, U i ≤ W) (hcov : W ≤ ⨆ i, U i) {A : Sort*}
    (a : ∀ i, (componentFunctor f).obj (U i) → A)
    (ha : ∀ i j (c : (componentFunctor f).obj (U i ⊓ U j)),
      a i ((componentFunctor f).map (homOfLE inf_le_left) c) =
        a j ((componentFunctor f).map (homOfLE inf_le_right) c)) :
    ∃! g : (componentFunctor f).obj W → A,
      ∀ i (e : (componentFunctor f).obj (U i)),
        g ((componentFunctor f).map (homOfLE (hU i)) e) = a i e := by
  obtain ⟨g, hg, huniq⟩ := componentFunctor_existsUnique_glue f (fun i : PLift κ => U i.down)
    (fun i => hU i.down) (by rwa [iSup_plift_down]) (fun i => a i.down)
    (fun i j c => ha i.down j.down c)
  exact ⟨g, fun i e => hg ⟨i⟩ e, fun g' hg' => huniq g' fun i e => hg' i.down e⟩

/-- The `Unit` base covered twice by `⊤`.
@isnad1 id=le.0h0v.s7.2ddcff2941cd from=translated src=- shape=ec18269c vocab=56ba8525
-/
theorem unitCover_cover : (⊤ : TopologicalSpace.Opens Unit) ≤ ⨆ _ : Bool, ⊤ :=
  le_iSup_of_le false le_rfl

/-- Naturality under a continuous commuting map, at the collapse `Bool → Unit` over the constant
base map (`collapseNatTrans`): for any compatible family over `C_{id}` on a cover of `Unit`, the
glue of the pulled-back family over `C_{boolToUnit}` factors through the collapse, so it identifies
the classes of `false` and `true`, which are distinct (`boolClass_false_ne_true`).
@isnad1 id=and.2h4v.s12.4f796d720863 from=translated src=- shape=48614e81 vocab=a31c0894
-/
theorem collapse_glue_identifies {A : Sort*}
    (a : ∀ _ : Bool, (componentFunctor (ContinuousMap.id Unit)).obj ⊤ → A)
    (G : (componentFunctor (ContinuousMap.id Unit)).obj ⊤ → A)
    (hG : ∀ i (e : (componentFunctor (ContinuousMap.id Unit)).obj ⊤),
      G ((componentFunctor (ContinuousMap.id Unit)).map (homOfLE le_top) e) = a i e)
    (G' : (componentFunctor boolToUnit).obj ⊤ → A)
    (hG' : ∀ i (e : (componentFunctor boolToUnit).obj ⊤),
      G' ((componentFunctor boolToUnit).map (homOfLE le_top) e) = a i (collapseNatTrans.app ⊤ e)) :
    G' = G ∘ collapseNatTrans.app ⊤ ∧ G' (boolClass false) = G' (boolClass true) := by
  have h := componentFunctor_glue_natTrans (f := boolToUnit) (g := ContinuousMap.id Unit)
    (ContinuousMap.const Bool ()) (fun _ => rfl) (fun _ : Bool => ⊤) (fun _ => le_top)
    unitCover_cover a G hG G' hG'
  refine ⟨h, ?_⟩
  rw [h]
  exact congrArg G collapseNatTrans_identifies

end TDA.Reeb.Examples
