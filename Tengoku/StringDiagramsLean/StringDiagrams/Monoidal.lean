import Tengoku.StringDiagramsLean.StringDiagrams.Interchange
import Tengoku.StringDiagramsLean.StringDiagrams.Generation
import Tengoku.Seed.CategoryTheory.Monoidal.Linear

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Presented categories of even monoidal signatures are monoidal

For a monoidal signature (a single region: `[Subsingleton S.Region]`, with the region chosen
by `[Inhabited S.Region]`), the presented category `P.Presented` of any presentation `P`
carries a strict monoidal structure in the sense of Mathlib (`MonoidalCategory`) as soon as
all generators are even (`Signature.IsEven`):

* on objects, `P.obj a ⊗ P.obj b = P.obj (a.tensor b)` (`Presentation.obj_tensor`, by `rfl`),
  and the unit is the empty word (`Obj.unit`);
* whiskering is `Presentation.whisk`, retyped along the identifications
  `a.tensor b = a.whisker Obj.unit b.word` and `a.tensor b = b.whisker a []`;
* the associator and the unitors are `eqToIso`s of equalities of objects
  (`Presentation.associator_eq`, `Presentation.leftUnitor_eq`,
  `Presentation.rightUnitor_eq`): the structure is strict.

The interchange law `whisker_exchange` for arbitrary morphisms is
`Presentation.diag_interchange_diagrams` (whose Koszul sign is `1` for even signatures),
extended bilinearly with `Presentation.hom_induction`. For signatures with odd generators the
interchange law holds only up to sign, and `P.Presented` is a monoidal supercategory rather
than a monoidal category; no such structure is constructed here.

The tensor product is `R`-bilinear (`MonoidalPreadditive`, `MonoidalLinear R`).

All constructions are first made for objects of the form `P.obj a` with `a : Obj S`
(`Presentation.wR`, `Presentation.wL`); the fields of the monoidal structure are then
instances of these lemmas, up to definitional unfolding.

## Main definitions and results

* `Signature.IsEven`: every generator is even.
* `Obj.unit`, `Obj.tensor_assoc`, `Obj.unit_tensor`, `Obj.tensor_unit`.
* `Presentation.instMonoidalCategory`, `Presentation.instMonoidalPreadditive`,
  `Presentation.instMonoidalLinear`.
* `Presentation.obj_tensor`, `Presentation.obj_unit`.
* `Presentation.diag_whiskerRight`, `Presentation.diag_whiskerLeft`: the classes of the
  diagrams `Diagram.whiskerR f b` and `Diagram.whiskerL a g` are `P.diag f ▷ P.obj b` and
  `P.obj a ◁ P.diag g`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory

universe w v u₀ u₁ u₂

/-- A signature is *even* if all its generators are even. The interchange law then holds
without signs.-/
class Signature.IsEven (S : Signature.{u₀, u₁, u₂}) : Prop where
  odd_eq_false : ∀ g : S.Gen, S.odd g = false

variable {S : Signature.{u₀, u₁, u₂}}

/--
@isnad1 id=eq.0h4v.s5.ba2a0e699e7e from=translated src=- shape=19b9e4f8 vocab=19adeb1d
-/
theorem Diagram.oddCount_eq_zero [S.IsEven] {a b : Obj S} (f : a ⟶ b) :
    Diagram.oddCount f = 0 := by
  simp [Diagram.oddCount, Diagram.oddCountList, Signature.IsEven.odd_eq_false]

/-! ## Objects -/

namespace Obj

/-- The empty word at the chosen region: the unit object.-/
def unit [Inhabited S.Region] : Obj S := ⟨default, []⟩

/--
@isnad1 id=eq.0h1v.s4.e3ff2dd56b1a from=translated src=- shape=c916f898 vocab=13639d2b
-/
@[simp] theorem unit_start [Inhabited S.Region] : (unit : Obj S).start = default := rfl
/--
@isnad1 id=eq.0h1v.s4.e43ec1a08803 from=translated src=- shape=5ac7235a vocab=e08f558e
-/
@[simp] theorem unit_word [Inhabited S.Region] : (unit : Obj S).word = [] := rfl

/--
@isnad1 id=eq.0h4v.s4.2b1fae5384d7 from=translated src=- shape=d4b6ca91 vocab=6311f46c
-/
theorem tensor_assoc (a b c : Obj S) : (a.tensor b).tensor c = a.tensor (b.tensor c) := by
  ext <;> simp [tensor]

/--
@isnad1 id=eq.0h2v.s4.7b8567e829c4 from=translated src=- shape=25e84c07 vocab=c6097142
-/
theorem unit_tensor [Subsingleton S.Region] [Inhabited S.Region] (a : Obj S) :
    unit.tensor a = a :=
  Obj.ext (Subsingleton.elim _ _) (by simp [tensor])

/--
@isnad1 id=eq.0h2v.s4.fa14fbabf403 from=translated src=- shape=d3179dbf vocab=9dc15c32
-/
theorem tensor_unit [Inhabited S.Region] (a : Obj S) : a.tensor unit = a := by
  ext <;> simp [tensor]

/-- Right whiskering by `b` is tensoring with `b` on the right.
@isnad1 id=eq.0h3v.s5.62d2bdcdb634 from=translated src=- shape=d71d56f3 vocab=d70bd7c7
-/
theorem tensor_eq_whisker_unit [Subsingleton S.Region] [Inhabited S.Region] (a b : Obj S) :
    a.tensor b = a.whisker unit b.word :=
  Obj.ext (Subsingleton.elim _ _) (by simp [tensor])

/-- Left whiskering by `a` is tensoring with `a` on the left.
@isnad1 id=eq.0h3v.s4.7b7eba95bb3d from=translated src=- shape=55d073e2 vocab=c5390f3f
-/
theorem tensor_eq_whisker_nil (a b : Obj S) : a.tensor b = b.whisker a [] := by
  ext <;> simp [tensor]

end Obj

namespace Presentation

variable {R : Type w} [CommRing R] (P : Presentation.{w, v} S R)

/-! ## Generalities on objects and `eqToHom` -/

/-- The object of the free 2-category underlying an object of the presented category.-/
def toObj (X : P.Presented) : Obj S := X.as

/--
@isnad1 id=eq.0h4v.s4.40e2d813472d from=translated src=- shape=b8192555 vocab=f72fc3f3
-/
@[simp] theorem toObj_obj (a : Obj S) : P.toObj (P.obj a) = a := rfl

/--
@isnad1 id=eq.0h4v.s5.78b49c343452 from=translated src=- shape=150855a7 vocab=8d3fd4b0
-/
@[simp] theorem obj_toObj (X : P.Presented) : P.obj (P.toObj X) = X := rfl

/--
@isnad1 id=injectiv.0h3v.s4.2dd57c12b05b from=translated src=- shape=fb0474a7 vocab=e5ec3331
-/
theorem obj_injective : Function.Injective P.obj := fun _ _ h => congrArg P.toObj h

/--
@isnad1 id=iff.0h5v.s5.fe500c975237 from=translated src=- shape=9a2726fa vocab=ce93955e
-/
@[simp] theorem obj_inj {a b : Obj S} : P.obj a = P.obj b ↔ a = b := P.obj_injective.eq_iff

/--
@isnad1 id=eq.1h5v.s7.ee4f9cdd357b from=translated src=- shape=80be8126 vocab=5296001a
-/
theorem diag_eqToHom {a b : Obj S} (h : a = b) :
    P.diag (eqToHom h) = eqToHom (congrArg P.obj h) := by
  subst h; simp

/-- Every `eqToHom` between objects `P.obj a` is the class of a (retyped) empty diagram.
@isnad1 id=eq.1h5v.s7.659a885df0e4 from=translated src=- shape=a01e5310 vocab=51115ad5
-/
theorem eqToHom_obj {a b : Obj S} (h : P.obj a = P.obj b) :
    eqToHom h = P.diag (eqToHom (P.obj_injective h)) := by
  rw [diag_eqToHom]

/--
@isnad1 id=eq.2h8v.s8.209b529489b0 from=translated src=- shape=aa9393f4 vocab=0d34bb94
-/
theorem diag_cast {a b a' b' : Obj S} (f : a ⟶ b) (ha : a = a') (hb : b = b') :
    P.diag (Diagram.cast f ha hb) =
      eqToHom (congrArg P.obj ha.symm) ≫ P.diag f ≫ eqToHom (congrArg P.obj hb) := by
  subst ha hb; simp

/-- Two diagrams with the same layers have the same class, up to retyping.
@isnad1 id=eq.3h9v.s8.f8db06c07169 from=translated src=- shape=5d4b3f02 vocab=957c4e7f
-/
theorem diag_eq_of_layers_eq' {a b a' b' : Obj S} (f : a ⟶ b) (g : a' ⟶ b') (ha : a = a')
    (hb : b = b') (h : Diagram.layers f = Diagram.layers g) :
    P.diag f = eqToHom (congrArg P.obj ha) ≫ P.diag g ≫ eqToHom (congrArg P.obj hb.symm) := by
  subst ha hb; simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact P.diag_eq_of_layers_eq h

/-! ## Whiskering by objects, for objects of the form `P.obj a` -/

/-- Left whiskering `1_a ⊗ g`.-/
def wL (a : Obj S) {b b' : Obj S} (g : P.obj b ⟶ P.obj b') :
    P.obj (a.tensor b) ⟶ P.obj (a.tensor b') :=
  eqToHom (congrArg P.obj (Obj.tensor_eq_whisker_nil a b)) ≫ P.whisk g a [] ≫
    eqToHom (congrArg P.obj (Obj.tensor_eq_whisker_nil a b').symm)

/-- Right whiskering `f ⊗ 1_b`.-/
def wR [Subsingleton S.Region] [Inhabited S.Region] {a a' : Obj S} (f : P.obj a ⟶ P.obj a')
    (b : Obj S) : P.obj (a.tensor b) ⟶ P.obj (a'.tensor b) :=
  eqToHom (congrArg P.obj (Obj.tensor_eq_whisker_unit a b)) ≫ P.whisk f Obj.unit b.word ≫
    eqToHom (congrArg P.obj (Obj.tensor_eq_whisker_unit a' b).symm)

variable {a a' a'' b b' b'' c c' : Obj S}

section Linear

/--
@isnad1 id=eq.0h9v.s8.3b582a065192 from=translated src=- shape=2834e7f5 vocab=d9521f0f
-/
theorem wL_comp (a : Obj S) (g : P.obj b ⟶ P.obj b') (g' : P.obj b' ⟶ P.obj b'') :
    P.wL a (g ≫ g') = P.wL a g ≫ P.wL a g' := by
  simp [wL, whisk_comp]

/--
@isnad1 id=eq.0h8v.s10.084533485755 from=translated src=- shape=6a35fc30 vocab=fb329ea7
-/
theorem wL_add (a : Obj S) (g g' : P.obj b ⟶ P.obj b') :
    P.wL a (g + g') = P.wL a g + P.wL a g' := by
  simp [wL, whisk_add]

/--
@isnad1 id=eq.0h8v.s11.f5c32b0473d7 from=translated src=- shape=5a6c0b05 vocab=e8e061c2
-/
theorem wL_smul (a : Obj S) (r : R) (g : P.obj b ⟶ P.obj b') :
    P.wL a (r • g) = r • P.wL a g := by
  simp [wL, whisk_smul]

/--
@isnad1 id=eq.0h6v.s8.af3d8f66c459 from=translated src=- shape=a6e4c3b7 vocab=428966ab
-/
theorem wL_zero (a : Obj S) : P.wL a (0 : P.obj b ⟶ P.obj b') = 0 := by
  simp [wL, whisk_zero]

variable [Subsingleton S.Region] [Inhabited S.Region]

/--
@isnad1 id=eq.0h9v.s8.8c1ac5f20334 from=translated src=- shape=20770468 vocab=00a1b388
-/
theorem wR_comp (f : P.obj a ⟶ P.obj a') (f' : P.obj a' ⟶ P.obj a'') (b : Obj S) :
    P.wR (f ≫ f') b = P.wR f b ≫ P.wR f' b := by
  simp [wR, whisk_comp]

/--
@isnad1 id=eq.0h8v.s10.72cbffffb3fe from=translated src=- shape=efd6a230 vocab=0574837c
-/
theorem wR_add (f f' : P.obj a ⟶ P.obj a') (b : Obj S) :
    P.wR (f + f') b = P.wR f b + P.wR f' b := by
  simp [wR, whisk_add]

/--
@isnad1 id=eq.0h8v.s11.1763df6fd51c from=translated src=- shape=96b22cdc vocab=d7830488
-/
theorem wR_smul (r : R) (f : P.obj a ⟶ P.obj a') (b : Obj S) :
    P.wR (r • f) b = r • P.wR f b := by
  simp [wR, whisk_smul]

/--
@isnad1 id=eq.0h6v.s8.165e4cf18270 from=translated src=- shape=0d63093b vocab=7a3dd289
-/
theorem wR_zero (b : Obj S) : P.wR (0 : P.obj a ⟶ P.obj a') b = 0 := by
  simp [wR, whisk_zero]

end Linear

section Whiskering

variable [Subsingleton S.Region]

/--
@isnad1 id=eq.0h7v.s7.ce28d6edc11c from=translated src=- shape=44434cdc vocab=98a7804f
-/
theorem wL_diag (a : Obj S) (g : b ⟶ b') : P.wL a (P.diag g) = P.diag (Diagram.whiskerL a g) := by
  rw [wL, P.whisk_diag g _ _ (Obj.whiskerOK_of_subsingleton _ _ _)]
  simp only [P.eqToHom_obj, ← P.diag_comp]
  apply P.diag_eq_of_layers_eq
  simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_whisker,
    Diagram.layers_whiskerL, List.nil_append, List.append_nil]
  exact List.map_congr_left fun L _ => Layer.ext rfl rfl rfl (List.append_nil _)

/--
@isnad1 id=eq.0h5v.s7.f0e056d25ecf from=translated src=- shape=e27c0162 vocab=3711b422
-/
theorem wL_id (a b : Obj S) : P.wL a (𝟙 (P.obj b)) = 𝟙 _ := by
  simp [wL, P.whisk_id b _ _ (Obj.whiskerOK_of_subsingleton _ _ _)]

/--
@isnad1 id=eq.1h6v.s7.c153a0236c7a from=translated src=- shape=5d9f4fb0 vocab=18c45f8f
-/
theorem wL_eqToHom (a : Obj S) (h : P.obj b = P.obj b') :
    P.wL a (eqToHom h) = eqToHom (by rw [P.obj_injective h]) := by
  obtain rfl := P.obj_injective h
  simp [wL_id]

/-- Associativity of left whiskering.
@isnad1 id=eq.0h8v.s8.61ff8a190dce from=translated src=- shape=45064faa vocab=d35825f5
-/
@[reassoc]
theorem wL_wL (a b : Obj S) (h : P.obj c ⟶ P.obj c') :
    P.wL (a.tensor b) h ≫ eqToHom (congrArg P.obj (Obj.tensor_assoc a b c')) =
      eqToHom (congrArg P.obj (Obj.tensor_assoc a b c)) ≫ P.wL a (P.wL b h) := by
  induction h using P.hom_induction with
  | diag d =>
    simp only [wL_diag, P.eqToHom_obj, ← P.diag_comp]
    apply P.diag_eq_of_layers_eq
    simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_whiskerL]
    simp [Layer.wl, Obj.tensor]
  | zero => simp [wL_zero]
  | add f g hf hg => simp only [wL_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | smul r f hf => simp only [wL_smul, Linear.smul_comp, Linear.comp_smul, hf]

variable [Inhabited S.Region]

/--
@isnad1 id=eq.0h7v.s7.61a211b8e5b8 from=translated src=- shape=d347a497 vocab=ef601a28
-/
theorem wR_diag (f : a ⟶ a') (b : Obj S) : P.wR (P.diag f) b = P.diag (Diagram.whiskerR f b) := by
  rw [wR, P.whisk_diag f _ _ (Obj.whiskerOK_of_subsingleton _ _ _)]
  simp only [P.eqToHom_obj, ← P.diag_comp]
  apply P.diag_eq_of_layers_eq
  simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_whisker,
    Diagram.layers_whiskerR, List.nil_append, List.append_nil]
  exact List.map_congr_left fun L _ =>
    Layer.ext (Subsingleton.elim _ _) (List.nil_append _) rfl rfl

/--
@isnad1 id=eq.0h5v.s7.f549035a688b from=translated src=- shape=1cf1e50c vocab=172541e2
-/
theorem wR_id (a b : Obj S) : P.wR (𝟙 (P.obj a)) b = 𝟙 _ := by
  simp [wR, P.whisk_id a _ _ (Obj.whiskerOK_of_subsingleton _ _ _)]

/--
@isnad1 id=eq.1h6v.s7.5ffb976e9552 from=translated src=- shape=a09b9eef vocab=a8d33662
-/
theorem wR_eqToHom (h : P.obj a = P.obj a') (b : Obj S) :
    P.wR (eqToHom h) b = eqToHom (by rw [P.obj_injective h]) := by
  obtain rfl := P.obj_injective h
  simp [wR_id]

/-- Associativity of right whiskering.
@isnad1 id=eq.0h8v.s8.c8f482da5d19 from=translated src=- shape=ff000c51 vocab=ff6fe74f
-/
@[reassoc]
theorem wR_wR (f : P.obj a ⟶ P.obj a') (b c : Obj S) :
    P.wR (P.wR f b) c ≫ eqToHom (congrArg P.obj (Obj.tensor_assoc a' b c)) =
      eqToHom (congrArg P.obj (Obj.tensor_assoc a b c)) ≫ P.wR f (b.tensor c) := by
  induction f using P.hom_induction with
  | diag d =>
    simp only [wR_diag, P.eqToHom_obj, ← P.diag_comp]
    apply P.diag_eq_of_layers_eq
    simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_whiskerR]
    simp [Layer.wr, Obj.tensor]
  | zero => simp [wR_zero]
  | add f g hf hg => simp only [wR_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | smul r f hf => simp only [wR_smul, Linear.smul_comp, Linear.comp_smul, hf]

/-- Right whiskering of a left whiskering (the middle associativity).
@isnad1 id=eq.0h8v.s8.605e97a9ae5f from=translated src=- shape=abbd05ba vocab=3558dba8
-/
@[reassoc]
theorem wL_wR (a : Obj S) (g : P.obj b ⟶ P.obj b') (c : Obj S) :
    P.wR (P.wL a g) c ≫ eqToHom (congrArg P.obj (Obj.tensor_assoc a b' c)) =
      eqToHom (congrArg P.obj (Obj.tensor_assoc a b c)) ≫ P.wL a (P.wR g c) := by
  induction g using P.hom_induction with
  | diag d =>
    simp only [wL_diag, wR_diag, P.eqToHom_obj, ← P.diag_comp]
    apply P.diag_eq_of_layers_eq
    simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_whiskerL,
      Diagram.layers_whiskerR]
    simp [Layer.wr, Layer.wl]
  | zero => simp [wR_zero, wL_zero]
  | add f g hf hg => simp only [wR_add, wL_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | smul r f hf => simp only [wR_smul, wL_smul, Linear.smul_comp, Linear.comp_smul, hf]

/-- Left whiskering by the unit object.
@isnad1 id=eq.0h6v.s8.6cf3b8d01288 from=translated src=- shape=3006710a vocab=d2b4b30a
-/
theorem unit_wL (g : P.obj b ⟶ P.obj b') :
    P.wL Obj.unit g ≫ eqToHom (congrArg P.obj (Obj.unit_tensor b')) =
      eqToHom (congrArg P.obj (Obj.unit_tensor b)) ≫ g := by
  induction g using P.hom_induction with
  | diag d =>
    simp only [wL_diag, P.eqToHom_obj, ← P.diag_comp]
    apply P.diag_eq_of_layers_eq
    simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_whiskerL,
      List.nil_append, List.append_nil]
    conv_rhs => rw [← List.map_id (Diagram.layers d)]
    exact List.map_congr_left fun L _ =>
      Layer.ext (Subsingleton.elim _ _) (List.nil_append _) rfl rfl
  | zero => simp [wL_zero]
  | add f g hf hg => simp only [wL_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | smul r f hf => simp only [wL_smul, Linear.smul_comp, Linear.comp_smul, hf]

/-- Right whiskering by the unit object.
@isnad1 id=eq.0h6v.s8.b0d381f8108a from=translated src=- shape=0322d9f5 vocab=09fea91d
-/
theorem wR_unit (f : P.obj a ⟶ P.obj a') :
    P.wR f Obj.unit ≫ eqToHom (congrArg P.obj (Obj.tensor_unit a')) =
      eqToHom (congrArg P.obj (Obj.tensor_unit a)) ≫ f := by
  induction f using P.hom_induction with
  | diag d =>
    simp only [wR_diag, P.eqToHom_obj, ← P.diag_comp]
    apply P.diag_eq_of_layers_eq
    simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_whiskerR,
      List.nil_append, List.append_nil]
    conv_rhs => rw [← List.map_id (Diagram.layers d)]
    exact List.map_congr_left fun L _ => Layer.ext rfl rfl rfl (List.append_nil _)
  | zero => simp [wR_zero]
  | add f g hf hg => simp only [wR_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | smul r f hf => simp only [wR_smul, Linear.smul_comp, Linear.comp_smul, hf]

/-- The interchange law for arbitrary morphisms, for even signatures.
@isnad1 id=eq.0h9v.s8.56cc6edc7d49 from=translated src=- shape=0341b202 vocab=c987ce67
-/
theorem wR_comp_wL [S.IsEven] (f : P.obj a ⟶ P.obj a') (g : P.obj b ⟶ P.obj b') :
    P.wR f b ≫ P.wL a' g = P.wL a g ≫ P.wR f b' := by
  induction f using P.hom_induction with
  | diag d =>
    induction g using P.hom_induction with
    | diag e =>
      rw [wR_diag, wR_diag, wL_diag, wL_diag, ← diag_comp, ← diag_comp,
        P.diag_interchange_diagrams, Diagram.oddCount_eq_zero, zero_mul, pow_zero, one_smul]
    | zero => simp [wL_zero]
    | add g g' hg hg' =>
      simp only [wL_add, Preadditive.add_comp, Preadditive.comp_add, hg, hg']
    | smul r g hg => simp only [wL_smul, Linear.smul_comp, Linear.comp_smul, hg]
  | zero => simp [wR_zero]
  | add f f' hf hf' => simp only [wR_add, Preadditive.add_comp, Preadditive.comp_add, hf, hf']
  | smul r f hf => simp only [wR_smul, Linear.smul_comp, Linear.comp_smul, hf]

/-! ### The axioms of a monoidal category, for objects of the form `P.obj a` -/

/--
@isnad1 id=eq.0h13v.s9.9ee6fe7d4977 from=translated src=- shape=78aa8198 vocab=c987ce67
-/
theorem tensor_comp_aux [S.IsEven] (f₁ : P.obj a ⟶ P.obj a') (g₁ : P.obj a' ⟶ P.obj a'')
    (f₂ : P.obj b ⟶ P.obj b') (g₂ : P.obj b' ⟶ P.obj b'') :
    P.wR (f₁ ≫ g₁) b ≫ P.wL a'' (f₂ ≫ g₂) =
      (P.wR f₁ b ≫ P.wL a' f₂) ≫ (P.wR g₁ b' ≫ P.wL a'' g₂) := by
  rw [wR_comp, wL_comp, Category.assoc, Category.assoc, ← Category.assoc (P.wR g₁ b),
    P.wR_comp_wL g₁ f₂, Category.assoc]

/--
@isnad1 id=eq.0h12v.s9.3e619e64a9a2 from=translated src=- shape=5db4ef58 vocab=3558dba8
-/
theorem associator_naturality_aux {a₁ a₂ a₃ b₁ b₂ b₃ : Obj S} (f₁ : P.obj a₁ ⟶ P.obj b₁)
    (f₂ : P.obj a₂ ⟶ P.obj b₂) (f₃ : P.obj a₃ ⟶ P.obj b₃) :
    (P.wR (P.wR f₁ a₂ ≫ P.wL b₁ f₂) a₃ ≫ P.wL (b₁.tensor b₂) f₃) ≫
        eqToHom (congrArg P.obj (Obj.tensor_assoc b₁ b₂ b₃)) =
      eqToHom (congrArg P.obj (Obj.tensor_assoc a₁ a₂ a₃)) ≫
        (P.wR f₁ (a₂.tensor a₃) ≫ P.wL b₁ (P.wR f₂ a₃ ≫ P.wL b₂ f₃)) := by
  simp only [wR_comp, wL_comp, Category.assoc]
  rw [P.wL_wL, P.wL_wR_assoc, P.wR_wR_assoc]

/--
@isnad1 id=eq.0h7v.s9.82dab78c27a5 from=translated src=- shape=f3cdc9b4 vocab=3558dba8
-/
theorem pentagon_aux (a b c d : Obj S) :
    P.wR (eqToHom (congrArg P.obj (Obj.tensor_assoc a b c))) d ≫
        eqToHom (congrArg P.obj (Obj.tensor_assoc a (b.tensor c) d)) ≫
          P.wL a (eqToHom (congrArg P.obj (Obj.tensor_assoc b c d))) =
      eqToHom (congrArg P.obj (Obj.tensor_assoc (a.tensor b) c d)) ≫
        eqToHom (congrArg P.obj (Obj.tensor_assoc a b (c.tensor d))) := by
  simp [wR_eqToHom, wL_eqToHom]

/--
@isnad1 id=eq.0h5v.s8.91248e96475a from=translated src=- shape=e6c52d99 vocab=9989a7a4
-/
theorem triangle_aux (a b : Obj S) :
    eqToHom (congrArg P.obj (Obj.tensor_assoc a Obj.unit b)) ≫
        P.wL a (eqToHom (congrArg P.obj (Obj.unit_tensor b))) =
      P.wR (eqToHom (congrArg P.obj (Obj.tensor_unit a))) b := by
  simp [wR_eqToHom, wL_eqToHom]

end Whiskering

/-! ## The monoidal structure -/

section Monoidal

variable [Subsingleton S.Region] [Inhabited S.Region]

instance instMonoidalCategoryStruct : MonoidalCategoryStruct P.Presented where
  tensorObj X Y := P.obj ((P.toObj X).tensor (P.toObj Y))
  whiskerLeft X {_ _} g := P.wL (P.toObj X) g
  whiskerRight f Y := P.wR f (P.toObj Y)
  tensorHom f g := P.wR f _ ≫ P.wL _ g
  tensorUnit := P.obj Obj.unit
  associator _ _ _ := eqToIso (congrArg P.obj (Obj.tensor_assoc _ _ _))
  leftUnitor _ := eqToIso (congrArg P.obj (Obj.unit_tensor _))
  rightUnitor _ := eqToIso (congrArg P.obj (Obj.tensor_unit _))

/--
@isnad1 id=eq.0h5v.s6.258c348b453e from=translated src=- shape=25d136fd vocab=3f672d44
-/
theorem obj_tensor (a b : Obj S) : P.obj a ⊗ P.obj b = P.obj (a.tensor b) := rfl

/--
@isnad1 id=eq.0h3v.s6.a694bf881c68 from=translated src=- shape=ade23c85 vocab=723c50ea
-/
theorem obj_unit : 𝟙_ P.Presented = P.obj Obj.unit := rfl

/--
@isnad1 id=eq.0h7v.s8.98abd5a0485c from=translated src=- shape=0f32377c vocab=5bc590bc
-/
theorem whiskerRight_eq {a a' : Obj S} (f : P.obj a ⟶ P.obj a') (b : Obj S) :
    f ▷ P.obj b = P.wR f b := rfl

/--
@isnad1 id=eq.0h7v.s7.da7a9a5466ae from=translated src=- shape=82bfeefd vocab=fae0f33a
-/
theorem whiskerLeft_eq (a : Obj S) {b b' : Obj S} (g : P.obj b ⟶ P.obj b') :
    P.obj a ◁ g = P.wL a g := rfl

/-- The class of `f ⊗ 1_b` is `P.diag f ▷ P.obj b`.
@isnad1 id=eq.0h7v.s7.2d0b144f8ecb from=translated src=- shape=e05490ab vocab=ce7d62c3
-/
@[simp] theorem diag_whiskerRight {a a' : Obj S} (f : a ⟶ a') (b : Obj S) :
    P.diag f ▷ P.obj b = P.diag (Diagram.whiskerR f b) := P.wR_diag f b

/-- The class of `1_a ⊗ g` is `P.obj a ◁ P.diag g`.
@isnad1 id=eq.0h7v.s7.3e5054d9a95d from=translated src=- shape=2d2bb073 vocab=cd86755a
-/
@[simp] theorem diag_whiskerLeft (a : Obj S) {b b' : Obj S} (g : b ⟶ b') :
    P.obj a ◁ P.diag g = P.diag (Diagram.whiskerL a g) := P.wL_diag a g

/-- The tensor product of objects is strictly associative.
@isnad1 id=eq.0h6v.s7.c032917616c1 from=translated src=- shape=b7acb0bf vocab=9afea923
-/
theorem tensor_assoc_obj (X Y Z : P.Presented) : (X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z) :=
  congrArg P.obj (Obj.tensor_assoc _ _ _)

/-- The unit is a strict left unit.
@isnad1 id=eq.0h4v.s6.2dffae228189 from=translated src=- shape=30770ac7 vocab=67894d48
-/
theorem unit_tensor_obj (X : P.Presented) : 𝟙_ P.Presented ⊗ X = X :=
  congrArg P.obj (Obj.unit_tensor _)

/-- The unit is a strict right unit.
@isnad1 id=eq.0h4v.s6.076d02745628 from=translated src=- shape=3399f840 vocab=67894d48
-/
theorem tensor_unit_obj (X : P.Presented) : X ⊗ 𝟙_ P.Presented = X :=
  congrArg P.obj (Obj.tensor_unit _)

/--
@isnad1 id=eq.0h6v.s8.28b8e1df9850 from=translated src=- shape=ea48ad42 vocab=99b1062d
-/
theorem associator_eq (X Y Z : P.Presented) : α_ X Y Z = eqToIso (P.tensor_assoc_obj X Y Z) :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.253472cc4f18 from=translated src=- shape=84df6de9 vocab=2b95fe33
-/
theorem leftUnitor_eq (X : P.Presented) : λ_ X = eqToIso (P.unit_tensor_obj X) := rfl

/--
@isnad1 id=eq.0h4v.s7.6f13241561a3 from=translated src=- shape=28a1573b vocab=c7253368
-/
theorem rightUnitor_eq (X : P.Presented) : ρ_ X = eqToIso (P.tensor_unit_obj X) := rfl

/--
@isnad1 id=eq.1h6v.s8.e0694cc4aea6 from=translated src=- shape=629fa53e vocab=d10a8968
-/
theorem whiskerRight_eqToHom {X X' : P.Presented} (h : X = X') (Y : P.Presented) :
    eqToHom h ▷ Y = eqToHom (congrArg (· ⊗ Y) h) := by
  subst h; exact P.wR_id (P.toObj X) (P.toObj Y)

/--
@isnad1 id=eq.1h6v.s8.8739b148de23 from=translated src=- shape=945f41ce vocab=7b7592ba
-/
theorem whiskerLeft_eqToHom (X : P.Presented) {Y Y' : P.Presented} (h : Y = Y') :
    X ◁ eqToHom h = eqToHom (congrArg (X ⊗ ·) h) := by
  subst h; exact P.wL_id (P.toObj X) (P.toObj Y)

variable [S.IsEven]

instance instMonoidalCategory : MonoidalCategory P.Presented where
  tensorHom_def _ _ := rfl
  id_tensorHom_id X Y := by
    change P.wR (𝟙 (P.obj (P.toObj X))) _ ≫ P.wL _ (𝟙 (P.obj (P.toObj Y))) = _
    rw [wR_id, wL_id, Category.comp_id]; rfl
  tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂} f₁ f₂ g₁ g₂ :=
    (P.tensor_comp_aux (a := P.toObj X₁) (a' := P.toObj Y₁) (a'' := P.toObj Z₁)
      (b := P.toObj X₂) (b' := P.toObj Y₂) (b'' := P.toObj Z₂) f₁ g₁ f₂ g₂).symm
  whiskerLeft_id X Y := P.wL_id (P.toObj X) (P.toObj Y)
  id_whiskerRight X Y := P.wR_id (P.toObj X) (P.toObj Y)
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ :=
    P.associator_naturality_aux (a₁ := P.toObj X₁) (a₂ := P.toObj X₂) (a₃ := P.toObj X₃)
      (b₁ := P.toObj Y₁) (b₂ := P.toObj Y₂) (b₃ := P.toObj Y₃) f₁ f₂ f₃
  leftUnitor_naturality {X Y} f := P.unit_wL (b := P.toObj X) (b' := P.toObj Y) f
  rightUnitor_naturality {X Y} f := P.wR_unit (a := P.toObj X) (a' := P.toObj Y) f
  pentagon W X Y Z := P.pentagon_aux (P.toObj W) (P.toObj X) (P.toObj Y) (P.toObj Z)
  triangle X Y := P.triangle_aux (P.toObj X) (P.toObj Y)

end Monoidal

end Presentation

end StringDiagrams

end
