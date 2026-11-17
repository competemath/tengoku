import Tengoku.StringDiagramsLean.StringDiagrams.Horizontal
import Tengoku.StringDiagramsLean.StringDiagrams.Monoidal
import Tengoku.Seed.CategoryTheory.Bicategory.Strict.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Presented 2-categories as bicategories

For a signature with arbitrary regions, the presented category `P.Presented` of a
presentation is the category of 1-cells and 2-cells of a 2-category whose 0-cells are the
regions. This file makes the horizontal structure explicit.

* On morphisms of the presented category, right whiskering `f ⊗ 1_b` is `Presentation.wRAt`
  (for objects starting in a fixed region `r`) and left whiskering `1_a ⊗ g` is
  `Presentation.wL` (from `StringDiagrams.Monoidal`, which makes no assumption on regions);
  both are induced by `Presentation.whisk`. Under composability hypotheses they are
  functorial, linear, strictly associative and unital, and they send classes of diagrams to
  classes of the diagrams `Diagram.rwhisker`, `Diagram.lwhisker`
  (`Presentation.wRAt_diag`, `Presentation.wL_diag_of_composable`). They satisfy the
  interchange law up to the Koszul sign on classes of diagrams
  (`Presentation.wRAt_diag_comp_wL_diag`) and on arbitrary morphisms for even signatures
  (`Presentation.wRAt_comp_wL`). The horizontal composite is `Presentation.hcomp`.
* For even signatures (`Signature.IsEven`), `P.Bicat` is a strict bicategory in the sense of
  Mathlib (`Bicategory`, `Bicategory.Strict`): its objects are the regions, its 1-morphisms
  from `l` to `m` are the well-formed words starting in `l` and ending in `m`
  (`Presentation.Bicat.Hom`), composed by concatenation, and its 2-morphisms from `a` to `b`
  are the morphisms `P.obj a.obj ⟶ P.obj b.obj` of the presented category. Associators and
  unitors are given by equalities of words.

For signatures with odd generators the interchange law holds only up to sign and no
bicategory is constructed.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}}

/-! ## Objects -/

namespace Obj

/-- The empty word in region `r`: the identity 1-cell of `r`.-/
def nil (r : S.Region) : Obj S := ⟨r, []⟩

/--
@isnad1 id=eq.0h2v.s3.04e8ec609711 from=translated src=- shape=6ddf6d3e vocab=0218d56e
-/
@[simp] theorem nil_start (r : S.Region) : (nil r).start = r := rfl
/--
@isnad1 id=eq.0h2v.s4.548d8628f9c9 from=translated src=- shape=0ef80e3b vocab=7c73255b
-/
@[simp] theorem nil_word (r : S.Region) : (nil r).word = ([] : List S.Colour) := rfl

/--
@isnad1 id=wf.0h2v.s3.a083d3bb9dd3 from=translated src=- shape=20553ef8 vocab=0c983a78
-/
theorem nil_wf (r : S.Region) : (nil r).WF := trivial

/--
@isnad1 id=eq.1h4v.s5.d1cf50950ed6 from=translated src=- shape=6034d998 vocab=2dac3c56
-/
theorem tensor_eq_whisker_nil_of_start {a : Obj S} (b : Obj S) {r : S.Region}
    (h : a.start = r) : a.tensor b = a.whisker (nil r) b.word := by
  ext
  · exact h
  · simp [tensor, whisker, nil]

/--
@isnad1 id=eq.1h3v.s4.43c2930b87e1 from=translated src=- shape=4385bebe vocab=1dc0c5a5
-/
theorem nil_tensor {b : Obj S} {r : S.Region} (h : b.start = r) : (nil r).tensor b = b := by
  ext
  · exact h.symm
  · simp [tensor, nil]

/--
@isnad1 id=eq.0h3v.s4.9aa923bdcd5d from=translated src=- shape=19a1a498 vocab=38701a6a
-/
theorem tensor_nil (a : Obj S) (r : S.Region) : a.tensor (nil r) = a := by
  ext
  · rfl
  · simp [tensor, nil]

variable {a b c : Obj S}

/--
@isnad1 id=composab.2h4v.s4.95021ba1c916 from=translated src=- shape=788af35b vocab=0a441bcc
-/
theorem Composable.tensor_left (hab : a.Composable b) (hbc : b.Composable c) :
    (a.tensor b).Composable c :=
  ⟨hab.wf_tensor, by rw [hab.endR_tensor]; exact hbc.endR_eq, hbc.right_wf⟩

/--
@isnad1 id=composab.2h4v.s4.80bdfe51035d from=translated src=- shape=d9719cd7 vocab=0a441bcc
-/
theorem Composable.tensor_right (hab : a.Composable b) (hbc : b.Composable c) :
    a.Composable (b.tensor c) :=
  ⟨hab.left_wf, hab.endR_eq, hbc.wf_tensor⟩

/--
@isnad1 id=composab.2h3v.s4.db9bd4675062 from=translated src=- shape=f065889a vocab=9be44187
-/
theorem Composable.nil_left (hb : b.WF) {r : S.Region} (h : b.start = r) :
    (nil r).Composable b :=
  ⟨trivial, h.symm, hb⟩

/--
@isnad1 id=composab.2h3v.s4.6e0b4a283e7e from=translated src=- shape=d5cc5b9a vocab=2b86a806
-/
theorem Composable.nil_right (ha : a.WF) {r : S.Region} (h : a.endR = r) :
    a.Composable (nil r) :=
  ⟨ha, h, trivial⟩

end Obj

/-! ## Whiskering in the presented category -/

namespace Presentation

variable {R : Type w} [CommRing R] (P : Presentation.{w, v} S R)

variable {a a' a'' b b' b'' c c' : Obj S} {r s : S.Region}

/-- Right whiskering `f ⊗ 1_b` in the presented category, for objects `a`, `a'` starting in
the region `r` (it is `0` unless `a` can be whiskered by `b`).-/
def wRAt (r : S.Region) (f : P.obj a ⟶ P.obj a') (b : Obj S) (ha : a.start = r)
    (ha' : a'.start = r) : P.obj (a.tensor b) ⟶ P.obj (a'.tensor b) :=
  eqToHom (congrArg P.obj (Obj.tensor_eq_whisker_nil_of_start b ha)) ≫
    P.whisk f (Obj.nil r) b.word ≫
      eqToHom (congrArg P.obj (Obj.tensor_eq_whisker_nil_of_start b ha').symm)

section Linear

variable (ha : a.start = r) (ha' : a'.start = r) (ha'' : a''.start = r)

/--
@isnad1 id=eq.3h10v.s8.a2f380f70bb5 from=translated src=- shape=374fb4fc vocab=a0350da7
-/
theorem wRAt_comp (f : P.obj a ⟶ P.obj a') (f' : P.obj a' ⟶ P.obj a'') (b : Obj S) :
    P.wRAt r (f ≫ f') b ha ha'' = P.wRAt r f b ha ha' ≫ P.wRAt r f' b ha' ha'' := by
  simp [wRAt, whisk_comp]

/--
@isnad1 id=eq.2h9v.s10.483f58d1fc51 from=translated src=- shape=5e645ba7 vocab=f62fc34d
-/
theorem wRAt_add (f f' : P.obj a ⟶ P.obj a') (b : Obj S) :
    P.wRAt r (f + f') b ha ha' = P.wRAt r f b ha ha' + P.wRAt r f' b ha ha' := by
  simp [wRAt, whisk_add]

/--
@isnad1 id=eq.2h9v.s11.a7c3b5c0a9c9 from=translated src=- shape=be726aaa vocab=fe15ba47
-/
theorem wRAt_smul (x : R) (f : P.obj a ⟶ P.obj a') (b : Obj S) :
    P.wRAt r (x • f) b ha ha' = x • P.wRAt r f b ha ha' := by
  simp [wRAt, whisk_smul]

/--
@isnad1 id=eq.2h7v.s8.bd65ce17239a from=translated src=- shape=a077058b vocab=bcc5ee24
-/
theorem wRAt_zero (b : Obj S) : P.wRAt r (0 : P.obj a ⟶ P.obj a') b ha ha' = 0 := by
  simp [wRAt, whisk_zero]

/--
@isnad1 id=eq.2h6v.s7.a35b52099c02 from=translated src=- shape=85632a45 vocab=cb533aac
-/
theorem wRAt_id (b : Obj S) (hb : S.ok a.endR b.word) :
    P.wRAt r (𝟙 (P.obj a)) b ha ha = 𝟙 _ := by
  have hw : a.WhiskerOK (Obj.nil r) b.word := ⟨trivial, ha.symm, hb⟩
  simp [wRAt, P.whisk_id a _ _ hw]

end Linear

/--
@isnad1 id=eq.4h7v.s7.47e9af564f7b from=translated src=- shape=e46dbbe7 vocab=83d7fb0a
-/
theorem wRAt_eqToHom (h : P.obj a = P.obj a') (b : Obj S) (hb : S.ok a.endR b.word)
    (ha : a.start = r) (ha' : a'.start = r) :
    P.wRAt r (eqToHom h) b ha ha' = eqToHom (by rw [P.obj_injective h]) := by
  obtain rfl := P.obj_injective h
  simp [P.wRAt_id ha b hb]

/-- The class of `f ⊗ 1_b`.
@isnad1 id=eq.3h8v.s7.819c843a5f39 from=translated src=- shape=5445d5c0 vocab=5e4924e1
-/
theorem wRAt_diag (f : a ⟶ a') (b : Obj S) (h : a.Composable b) (ha : a.start = r)
    (ha' : a'.start = r) : P.wRAt r (P.diag f) b ha ha' = P.diag (Diagram.rwhisker f b h) := by
  have hw : a.WhiskerOK (Obj.nil r) b.word := ⟨trivial, ha.symm, h.ok_endR⟩
  rw [wRAt, P.whisk_diag f _ _ hw]
  simp only [P.eqToHom_obj, ← P.diag_comp]
  apply P.diag_eq_of_layers_eq
  simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_whisker,
    Diagram.layers_rwhisker, List.nil_append, List.append_nil]
  exact List.map_congr_left fun L hL =>
    Layer.ext (by show r = L.start; rw [(Diagram.chain f).start_of_mem hL, ha]) (List.nil_append _)
      rfl rfl

/--
@isnad1 id=eq.1h5v.s7.52fadea057cb from=translated src=- shape=7f7147d4 vocab=ad14f0c8
-/
theorem wL_id_of_composable (h : a.Composable b) : P.wL a (𝟙 (P.obj b)) = 𝟙 _ := by
  simp [wL, P.whisk_id b a [] ⟨h.left_wf, h.endR_eq, trivial⟩]

/--
@isnad1 id=eq.2h6v.s7.be5f09611251 from=translated src=- shape=d36b8b78 vocab=20552a35
-/
theorem wL_eqToHom_of_composable (h : P.obj b = P.obj b') (hab : a.Composable b) :
    P.wL a (eqToHom h) = eqToHom (by rw [P.obj_injective h]) := by
  obtain rfl := P.obj_injective h
  simp [P.wL_id_of_composable hab]

/-- The class of `1_a ⊗ g`.
@isnad1 id=eq.1h7v.s7.bee5929c8e72 from=translated src=- shape=047d6afc vocab=6392655f
-/
theorem wL_diag_of_composable (a : Obj S) (g : b ⟶ b') (h : a.Composable b) :
    P.wL a (P.diag g) = P.diag (Diagram.lwhisker a g h) := by
  rw [wL, P.whisk_diag g a [] ⟨h.left_wf, h.endR_eq, trivial⟩]
  simp only [P.eqToHom_obj, ← P.diag_comp]
  apply P.diag_eq_of_layers_eq
  simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_lwhisker,
    List.nil_append, List.append_nil]
  exact List.map_congr_left fun L _ => Layer.ext rfl rfl rfl (List.append_nil _)

/-! ### Associativity and units -/

set_option backward.isDefEq.respectTransparency false in
/-- Left whiskering by a composite.
@isnad1 id=eq.2h8v.s8.48f5b524affd from=translated src=- shape=a8c5b8b5 vocab=f74f7820
-/
theorem wL_tensor (hab : a.Composable b) (hbc : b.Composable c) (g : P.obj c ⟶ P.obj c') :
    P.wL (a.tensor b) g =
      eqToHom (congrArg P.obj (Obj.tensor_assoc a b c)) ≫ P.wL a (P.wL b g) ≫
        eqToHom (congrArg P.obj (Obj.tensor_assoc a b c')).symm := by
  induction g using P.hom_induction with
  | diag d =>
    rw [P.wL_diag_of_composable _ d (hab.tensor_left hbc), P.wL_diag_of_composable _ d hbc,
      P.wL_diag_of_composable _ _ (hab.tensor_right hbc)]
    simp only [P.eqToHom_obj, ← P.diag_comp]
    apply P.diag_eq_of_layers_eq
    simp [Layer.wl, Obj.tensor]
  | zero => simp [wL_zero]
  | add f g hf hg => simp only [wL_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | smul x f hf => simp only [wL_smul, Linear.smul_comp, Linear.comp_smul, hf]

set_option backward.isDefEq.respectTransparency false in
/-- Right whiskering by a composite.
@isnad1 id=eq.4h9v.s8.8f326d86daa0 from=translated src=- shape=08d75ca0 vocab=51f2e45a
-/
theorem wRAt_tensor (hab : a.Composable b) (hbc : b.Composable c) (f : P.obj a ⟶ P.obj a')
    (ha : a.start = r) (ha' : a'.start = r) :
    P.wRAt r f (b.tensor c) ha ha' =
      eqToHom (congrArg P.obj (Obj.tensor_assoc a b c)).symm ≫
        P.wRAt r (P.wRAt r f b ha ha') c ha ha' ≫
          eqToHom (congrArg P.obj (Obj.tensor_assoc a' b c)) := by
  induction f using P.hom_induction with
  | diag d =>
    have h₁ : (a.tensor b).Composable c := hab.tensor_left hbc
    rw [P.wRAt_diag d _ hab, P.wRAt_diag _ c h₁, P.wRAt_diag d _ (hab.tensor_right hbc)]
    simp only [P.eqToHom_obj, ← P.diag_comp]
    apply P.diag_eq_of_layers_eq
    simp [Layer.wr, Obj.tensor]
  | zero => simp [wRAt_zero]
  | add f g hf hg => simp only [wRAt_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | smul x f hf => simp only [wRAt_smul, Linear.smul_comp, Linear.comp_smul, hf]

set_option backward.isDefEq.respectTransparency false in
/-- Right whiskering of a left whiskering.
@isnad1 id=eq.5h10v.s8.2d298c59471d from=translated src=- shape=75f36acd vocab=3673c67b
-/
theorem wRAt_wL (hab : a.Composable b) (hbc : b.Composable c) (g : P.obj b ⟶ P.obj b')
    (ha : a.start = r) (hb : b.start = s) (hb' : b'.start = s) :
    P.wRAt r (P.wL a g) c ha ha =
      eqToHom (congrArg P.obj (Obj.tensor_assoc a b c)) ≫ P.wL a (P.wRAt s g c hb hb') ≫
        eqToHom (congrArg P.obj (Obj.tensor_assoc a b' c)).symm := by
  induction g using P.hom_induction with
  | diag d =>
    rw [P.wL_diag_of_composable _ d hab, P.wRAt_diag _ c (hab.tensor_left hbc),
      P.wRAt_diag d c hbc, P.wL_diag_of_composable _ _ (hab.tensor_right hbc)]
    simp only [P.eqToHom_obj, ← P.diag_comp]
    apply P.diag_eq_of_layers_eq
    simp [Layer.wr, Layer.wl, Obj.tensor]
  | zero => simp [wRAt_zero, wL_zero]
  | add f g hf hg =>
    simp only [wRAt_add, wL_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | smul x f hf => simp only [wRAt_smul, wL_smul, Linear.smul_comp, Linear.comp_smul, hf]

/-- Left whiskering by an identity 1-cell.
@isnad1 id=eq.3h7v.s8.84ef9cbbd7d0 from=translated src=- shape=54e65f97 vocab=2c3bfc9d
-/
theorem wL_nil (g : P.obj b ⟶ P.obj b') (hb : b.WF) (hs : b.start = r) (hs' : b'.start = r) :
    P.wL (Obj.nil r) g =
      eqToHom (congrArg P.obj (Obj.nil_tensor hs)) ≫ g ≫
        eqToHom (congrArg P.obj (Obj.nil_tensor hs')).symm := by
  induction g using P.hom_induction with
  | diag d =>
    rw [P.wL_diag_of_composable _ d (Obj.Composable.nil_left hb hs)]
    simp only [P.eqToHom_obj, ← P.diag_comp]
    apply P.diag_eq_of_layers_eq
    simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_lwhisker,
      List.nil_append, List.append_nil]
    conv_rhs => rw [← List.map_id (Diagram.layers d)]
    exact List.map_congr_left fun L hL =>
      Layer.ext (by show r = L.start; rw [(Diagram.chain d).start_of_mem hL, hs])
        (List.nil_append _) rfl rfl
  | zero => simp [wL_zero]
  | add f g hf hg => simp only [wL_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | smul x f hf => simp only [wL_smul, Linear.smul_comp, Linear.comp_smul, hf]

/-- Right whiskering by an identity 1-cell.
@isnad1 id=eq.4h8v.s8.063a7df7bcd2 from=translated src=- shape=50ec71ab vocab=af187881
-/
theorem wRAt_nil (f : P.obj a ⟶ P.obj a') (ha : a.WF) (he : a.endR = s) (hr : a.start = r)
    (hr' : a'.start = r) :
    P.wRAt r f (Obj.nil s) hr hr' =
      eqToHom (congrArg P.obj (Obj.tensor_nil a s)) ≫ f ≫
        eqToHom (congrArg P.obj (Obj.tensor_nil a' s)).symm := by
  induction f using P.hom_induction with
  | diag d =>
    rw [P.wRAt_diag d _ (Obj.Composable.nil_right ha he)]
    simp only [P.eqToHom_obj, ← P.diag_comp]
    apply P.diag_eq_of_layers_eq
    simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_rwhisker,
      List.nil_append, List.append_nil, Obj.nil_word]
    conv_rhs => rw [← List.map_id (Diagram.layers d)]
    exact List.map_congr_left fun L _ => Layer.ext rfl rfl rfl (List.append_nil _)
  | zero => simp [wRAt_zero]
  | add f g hf hg => simp only [wRAt_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | smul x f hf => simp only [wRAt_smul, Linear.smul_comp, Linear.comp_smul, hf]

/-! ### The interchange law -/

/-- The interchange law on classes of diagrams, with the Koszul sign, for general regions.
@isnad1 id=eq.3h10v.s9.725a74a1aae8 from=translated src=- shape=bd48ceee vocab=ca6e939f
-/
theorem wRAt_diag_comp_wL_diag (h : a.Composable b) (f : a ⟶ a') (g : b ⟶ b')
    (ha : a.start = r) (ha' : a'.start = r) :
    P.wRAt r (P.diag f) b ha ha' ≫ P.wL a' (P.diag g) =
      ((-1 : ℤ) ^ (Diagram.oddCount f * Diagram.oddCount g)) •
        (P.wL a (P.diag g) ≫ P.wRAt r (P.diag f) b' ha ha') := by
  rw [P.wRAt_diag f b h, P.wL_diag_of_composable a' g (h.map_left f),
    P.wL_diag_of_composable a g h, P.wRAt_diag f b' (h.map_right g), ← P.diag_comp,
    ← P.diag_comp, P.diag_interchange_of_composable]

/-- The interchange law for arbitrary morphisms, for even signatures and general regions.
@isnad1 id=eq.3h10v.s8.8debafbd3efe from=translated src=- shape=be1e9921 vocab=22f3eb3e
-/
theorem wRAt_comp_wL [S.IsEven] (h : a.Composable b) (f : P.obj a ⟶ P.obj a')
    (g : P.obj b ⟶ P.obj b') (ha : a.start = r) (ha' : a'.start = r) :
    P.wRAt r f b ha ha' ≫ P.wL a' g = P.wL a g ≫ P.wRAt r f b' ha ha' := by
  induction f using P.hom_induction with
  | diag d =>
    induction g using P.hom_induction with
    | diag e =>
      rw [P.wRAt_diag_comp_wL_diag h d e, Diagram.oddCount_eq_zero, zero_mul, pow_zero,
        one_smul]
    | zero => simp [wL_zero]
    | add g g' hg hg' =>
      simp only [wL_add, Preadditive.add_comp, Preadditive.comp_add, hg, hg']
    | smul x g hg => simp only [wL_smul, Linear.smul_comp, Linear.comp_smul, hg]
  | zero => simp [wRAt_zero]
  | add f f' hf hf' => simp only [wRAt_add, Preadditive.add_comp, Preadditive.comp_add, hf, hf']
  | smul x f hf => simp only [wRAt_smul, Linear.smul_comp, Linear.comp_smul, hf]

/-! ### Horizontal composition -/

/-- The horizontal composite `f ⊗ g = (f ⊗ 1_b) ≫ (1_{a'} ⊗ g)` of `f : a ⟶ a'` and
`g : b ⟶ b'`, for `a`, `a'` starting in the region `r`.-/
def hcomp (r : S.Region) (f : P.obj a ⟶ P.obj a') (g : P.obj b ⟶ P.obj b') (ha : a.start = r)
    (ha' : a'.start = r) : P.obj (a.tensor b) ⟶ P.obj (a'.tensor b') :=
  P.wRAt r f b ha ha' ≫ P.wL a' g

/-- The class of the horizontal composite of two diagrams.
@isnad1 id=eq.3h10v.s7.ffee833e14d8 from=translated src=- shape=1ea9a130 vocab=80bdf31d
-/
theorem hcomp_diag (h : a.Composable b) (f : a ⟶ a') (g : b ⟶ b') (ha : a.start = r)
    (ha' : a'.start = r) :
    P.hcomp r (P.diag f) (P.diag g) ha ha' =
      P.diag (Diagram.rwhisker f b h ≫ Diagram.lwhisker a' g (h.map_left f)) := by
  rw [hcomp, P.wRAt_diag f b h, P.wL_diag_of_composable a' g (h.map_left f), P.diag_comp]

/-- Horizontal composition of identities.
@isnad1 id=eq.2h6v.s7.ba52b841f132 from=translated src=- shape=956cb76b vocab=62734707
-/
theorem hcomp_id (h : a.Composable b) (ha : a.start = r) :
    P.hcomp r (𝟙 (P.obj a)) (𝟙 (P.obj b)) ha ha = 𝟙 _ := by
  rw [hcomp, P.wRAt_id ha b h.ok_endR, P.wL_id_of_composable h, Category.comp_id]

/-- The other order of whiskering, for even signatures.
@isnad1 id=eq.3h10v.s8.08377c9dd3a0 from=translated src=- shape=795c8502 vocab=de006cdb
-/
theorem hcomp_eq [S.IsEven] (h : a.Composable b) (f : P.obj a ⟶ P.obj a')
    (g : P.obj b ⟶ P.obj b') (ha : a.start = r) (ha' : a'.start = r) :
    P.hcomp r f g ha ha' = P.wL a g ≫ P.wRAt r f b' ha ha' :=
  P.wRAt_comp_wL h f g ha ha'

/-- Functoriality of horizontal composition (the middle-four interchange law), for even
signatures.
@isnad1 id=eq.4h14v.s8.4685f067b970 from=translated src=- shape=ebcebf25 vocab=9ac39e78
-/
theorem hcomp_comp [S.IsEven] (h : a'.Composable b) (f : P.obj a ⟶ P.obj a')
    (f' : P.obj a' ⟶ P.obj a'') (g : P.obj b ⟶ P.obj b') (g' : P.obj b' ⟶ P.obj b'')
    (ha : a.start = r) (ha' : a'.start = r) (ha'' : a''.start = r) :
    P.hcomp r (f ≫ f') (g ≫ g') ha ha'' =
      P.hcomp r f g ha ha' ≫ P.hcomp r f' g' ha' ha'' := by
  simp only [hcomp, P.wRAt_comp ha ha' ha'', wL_comp, Category.assoc]
  rw [← Category.assoc (P.wRAt r f' b ha' ha''), P.wRAt_comp_wL h f' g ha' ha'',
    Category.assoc]

/-! ## The presented bicategory -/

/-- The objects of the 2-category presented by `P`: the regions.-/
@[ext]
structure Bicat (P : Presentation.{w, v} S R) : Type u₀ where
  /-- The underlying region.-/
  region : S.Region

namespace Bicat

variable {P} {l m n k j : P.Bicat}

/-- A 1-morphism from `l` to `m`: a well-formed word starting in `l` and ending in `m`.-/
@[ext]
structure Hom (l m : P.Bicat) : Type (max u₀ u₁) where
  /-- The underlying object of the free 2-category.-/
  obj : Obj S
  /-- The word starts in `l`.-/
  start_eq : obj.start = l.region
  /-- The word is well formed.-/
  wf : obj.WF
  /-- The word ends in `m`.-/
  endR_eq : obj.endR = m.region

/--
@isnad1 id=composab.0h8v.s6.935380e76694 from=translated src=- shape=25e4c986 vocab=7636eb63
-/
theorem Hom.composable (a : Hom l m) (b : Hom m n) : a.obj.Composable b.obj :=
  ⟨a.wf, a.endR_eq.trans b.start_eq.symm, b.wf⟩

/-- The identity 1-morphism of `l`: the empty word.-/
def Hom.id (l : P.Bicat) : Hom l l := ⟨Obj.nil l.region, rfl, trivial, rfl⟩

/-- Composition of 1-morphisms: concatenation of words.-/
def Hom.comp (a : Hom l m) (b : Hom m n) : Hom l n :=
  ⟨a.obj.tensor b.obj, a.start_eq, (a.composable b).wf_tensor,
    by rw [(a.composable b).endR_tensor, b.endR_eq]⟩

/--
@isnad1 id=eq.0h4v.s5.7a5303db53a1 from=translated src=- shape=7f79656c vocab=d319cb42
-/
@[simp] theorem Hom.id_obj (l : P.Bicat) : (Hom.id l).obj = Obj.nil l.region := rfl

/--
@isnad1 id=eq.0h8v.s6.d58a3c4bd1b2 from=translated src=- shape=327c482d vocab=e87d415a
-/
@[simp] theorem Hom.comp_obj (a : Hom l m) (b : Hom m n) :
    (a.comp b).obj = a.obj.tensor b.obj := rfl

instance : CategoryStruct P.Bicat where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

/-- The 2-morphisms between 1-morphisms `a b : l ⟶ m` are the morphisms
`P.obj a.obj ⟶ P.obj b.obj` of the presented category.-/
instance homCategory (l m : P.Bicat) : Category (Hom l m) where
  Hom a b := P.obj a.obj ⟶ P.obj b.obj
  id a := 𝟙 (P.obj a.obj)
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

/-- The invertible 2-morphism given by an equality of the underlying words.-/
def isoOfEq {a b : Hom l m} (e : a.obj = b.obj) : a ≅ b where
  hom := (eqToHom (congrArg P.obj e) : P.obj a.obj ⟶ P.obj b.obj)
  inv := (eqToHom (congrArg P.obj e.symm) : P.obj b.obj ⟶ P.obj a.obj)
  hom_inv_id :=
    (eqToHom_trans (congrArg P.obj e) (congrArg P.obj e.symm)).trans (eqToHom_refl _ _)
  inv_hom_id :=
    (eqToHom_trans (congrArg P.obj e.symm) (congrArg P.obj e)).trans (eqToHom_refl _ _)

/--
@isnad1 id=eq.2h7v.s6.5e31d5629c34 from=translated src=- shape=ebbf3c7d vocab=a53d728d
-/
theorem isoOfEq_eq_eqToIso {a b : Hom l m} (e : a.obj = b.obj) (e' : a = b) :
    isoOfEq e = eqToIso e' := by
  subst e'
  apply Iso.ext
  exact eqToHom_refl (P.obj a.obj) (congrArg P.obj e)

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h12v.s10.d5ad9ebeb4bd from=translated src=- shape=6d270b69 vocab=53c43a3d
-/
theorem pentagon_aux (a : Hom l m) (b : Hom m n) (c : Hom n k) (d : Hom k j) :
    P.wRAt l.region (eqToHom (congrArg P.obj (Obj.tensor_assoc a.obj b.obj c.obj))) d.obj
        a.start_eq a.start_eq ≫
      eqToHom (congrArg P.obj (Obj.tensor_assoc a.obj (b.obj.tensor c.obj) d.obj)) ≫
        P.wL a.obj (eqToHom (congrArg P.obj (Obj.tensor_assoc b.obj c.obj d.obj))) =
      eqToHom (congrArg P.obj (Obj.tensor_assoc (a.obj.tensor b.obj) c.obj d.obj)) ≫
        eqToHom (congrArg P.obj (Obj.tensor_assoc a.obj b.obj (c.obj.tensor d.obj))) := by
  rw [P.wRAt_eqToHom _ _ (((a.comp b).comp c).composable d).ok_endR,
    P.wL_eqToHom_of_composable _ (a.composable ((b.comp c).comp d))]
  simp

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h8v.s9.5c6459d6453d from=translated src=- shape=7bd717c4 vocab=62c55f9d
-/
theorem triangle_aux (a : Hom l m) (b : Hom m n) :
    eqToHom (congrArg P.obj (Obj.tensor_assoc a.obj (Obj.nil m.region) b.obj)) ≫
        P.wL a.obj (eqToHom (congrArg P.obj (Obj.nil_tensor b.start_eq))) =
      P.wRAt l.region (eqToHom (congrArg P.obj (Obj.tensor_nil a.obj m.region))) b.obj
        a.start_eq a.start_eq := by
  rw [P.wRAt_eqToHom _ _ ((a.comp (Hom.id m)).composable b).ok_endR,
    P.wL_eqToHom_of_composable _ (a.composable ((Hom.id m).comp b))]
  simp

end Bicat

/-- For an even signature, the regions, well-formed words and morphisms of the presented
category form a bicategory.-/
instance instBicategory [S.IsEven] : Bicategory P.Bicat where
  homCategory := Bicat.homCategory
  whiskerLeft a _ _ θ := P.wL (Bicat.Hom.obj a) θ
  whiskerRight {l _ _} {a a'} η b :=
    P.wRAt l.region η (Bicat.Hom.obj b) (Bicat.Hom.start_eq a) (Bicat.Hom.start_eq a')
  associator a b c :=
    Bicat.isoOfEq (Obj.tensor_assoc (Bicat.Hom.obj a) (Bicat.Hom.obj b) (Bicat.Hom.obj c))
  leftUnitor a := Bicat.isoOfEq (Obj.nil_tensor (Bicat.Hom.start_eq a))
  rightUnitor {_ m} a := Bicat.isoOfEq (Obj.tensor_nil (Bicat.Hom.obj a) m.region)
  whiskerLeft_id a b := P.wL_id_of_composable (Bicat.Hom.composable a b)
  whiskerLeft_comp a _ _ _ η θ := P.wL_comp (Bicat.Hom.obj a) η θ
  id_whiskerLeft {_ _} {a b} η :=
    P.wL_nil η (Bicat.Hom.wf a) (Bicat.Hom.start_eq a) (Bicat.Hom.start_eq b)
  comp_whiskerLeft a b _ _ η :=
    P.wL_tensor (Bicat.Hom.composable a b) (Bicat.Hom.composable b _) η
  id_whiskerRight a b :=
    P.wRAt_id (Bicat.Hom.start_eq a) (Bicat.Hom.obj b) (Bicat.Hom.composable a b).ok_endR
  comp_whiskerRight η θ c := P.wRAt_comp _ _ _ η θ (Bicat.Hom.obj c)
  whiskerRight_id {_ _} {a a'} η :=
    P.wRAt_nil η (Bicat.Hom.wf a) (Bicat.Hom.endR_eq a) (Bicat.Hom.start_eq a)
      (Bicat.Hom.start_eq a')
  whiskerRight_comp {_ _ _ _} {a _} η b c :=
    P.wRAt_tensor (Bicat.Hom.composable a b) (Bicat.Hom.composable b c) η _ _
  whisker_assoc {_ _ _ _} a {b b'} η c :=
    P.wRAt_wL (Bicat.Hom.composable a b) (Bicat.Hom.composable b c) η (Bicat.Hom.start_eq a)
      (Bicat.Hom.start_eq b) (Bicat.Hom.start_eq b')
  whisker_exchange {_ _ _} {a a'} {b _} η θ :=
    (P.wRAt_comp_wL (Bicat.Hom.composable a b) η θ (Bicat.Hom.start_eq a)
      (Bicat.Hom.start_eq a')).symm
  pentagon a b c d := Bicat.pentagon_aux a b c d
  triangle a b := Bicat.triangle_aux a b

/-- The presented bicategory is strict: associators and unitors are equalities of words.
@isnad1 id=strict.0h3v.s4.2b9f6bb9a50b from=translated src=- shape=c62fd019 vocab=f0b5a298
-/
instance instBicategoryStrict [S.IsEven] : Bicategory.Strict P.Bicat where
  id_comp a := Bicat.Hom.ext (Obj.nil_tensor (Bicat.Hom.start_eq a))
  comp_id _ := Bicat.Hom.ext (Obj.tensor_nil _ _)
  assoc _ _ _ := Bicat.Hom.ext (Obj.tensor_assoc _ _ _)
  leftUnitor_eqToIso _ := Bicat.isoOfEq_eq_eqToIso _ _
  rightUnitor_eqToIso _ := Bicat.isoOfEq_eq_eqToIso _ _
  associator_eqToIso _ _ _ := Bicat.isoOfEq_eq_eqToIso _ _

section BicatAPI

open Bicategory

variable [S.IsEven] {l m n : P.Bicat}

/--
@isnad1 id=eq.0h10v.s8.cde47a9fae3b from=translated src=- shape=47e35f53 vocab=8e5a5022
-/
theorem Bicat.whiskerLeft_eq (a : l ⟶ m) {b b' : m ⟶ n} (θ : b ⟶ b') :
    a ◁ θ = P.wL (Bicat.Hom.obj a) θ := rfl

/--
@isnad1 id=eq.0h10v.s8.8cee940ceedb from=translated src=- shape=98cab5dd vocab=99e0dcfa
-/
theorem Bicat.whiskerRight_eq {a a' : l ⟶ m} (η : a ⟶ a') (b : m ⟶ n) :
    η ▷ b = P.wRAt l.region η (Bicat.Hom.obj b) (Bicat.Hom.start_eq a) (Bicat.Hom.start_eq a') :=
  rfl

end BicatAPI

end Presentation

end StringDiagrams

end
