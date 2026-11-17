import Tengoku.StringDiagramsLean.StringDiagrams.Presentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Interpretations and soundness

An *interpretation* of the free 2-category on a signature `S` in a category `D` assigns an
object of `D` to every object and a morphism to every well-formed layer
(`StringDiagrams.Interpretation`); it extends uniquely to a functor
(`Interpretation.functor`), computed on a diagram by composing the images of its layers.

If `D` is `R`-linear, such a functor extends linearly to linear combinations of diagrams
(`StringDiagrams.freeLift`, a universe-polymorphic version of `CategoryTheory.Free.lift`),
and it descends to the presented category of a presentation `P` as soon as it kills every
whiskered relation and every whiskered instance of the interchange law
(`Presentation.lift`, soundness). The descended functor is `R`-linear
(`Presentation.lift_linear`) and sends the class of a diagram to its image
(`Presentation.lift_diag`).

Faithfulness of an interpretation is a separate question, not addressed here.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w v u₀ u₁ u₂ w₁ w₂

variable {S : Signature.{u₀, u₁, u₂}}

/-! ## Interpretations by layers -/

/-- An interpretation of the free 2-category on `S` in a category `D`: images of objects and
of well-formed layers.-/
structure Interpretation (S : Signature.{u₀, u₁, u₂}) (D : Type w₁) [Category.{w₂} D] where
  /-- Image of an object.-/
  obj : Obj S → D
  /-- Image of a well-formed layer.-/
  layer : (L : Layer S) → L.Valid → (obj L.dom ⟶ obj L.cod)

namespace Interpretation

variable {D : Type w₁} [Category.{w₂} D] (I : Interpretation S D)

/-- The image of a chain of layers.-/
def mapChain : (a : Obj S) → (ls : List (Layer S)) → (b : Obj S) → Chain a ls b →
    (I.obj a ⟶ I.obj b)
  | _, [], _, h => eqToHom (congrArg I.obj h)
  | _, L :: ls, b, h => eqToHom (congrArg I.obj h.2.1.symm) ≫ I.layer L h.1 ≫
      mapChain L.cod ls b h.2.2

/--
@isnad1 id=eq.2h8v.s7.c297397ee200 from=translated src=- shape=880ff7b6 vocab=76e52a4c
-/
theorem mapChain_append {a b c : Obj S} {ls ms : List (Layer S)} (h₁ : Chain a ls b)
    (h₂ : Chain b ms c) :
    I.mapChain a (ls ++ ms) c (h₁.append h₂) = I.mapChain a ls b h₁ ≫ I.mapChain b ms c h₂ := by
  induction ls generalizing a with
  | nil => cases h₁; simp [mapChain]
  | cons L ls ih => simp only [List.cons_append, mapChain, Category.assoc, ← ih]

/-- The functor determined by an interpretation.-/
def functor : Obj S ⥤ D where
  obj := I.obj
  map f := I.mapChain _ (Diagram.layers f) _ (Diagram.chain f)
  map_id _ := by simp [mapChain]
  map_comp f g := I.mapChain_append (Diagram.chain f) (Diagram.chain g)

/--
@isnad1 id=eq.0h4v.s5.29b59ef6fdb6 from=translated src=- shape=374e0896 vocab=14b0eab2
-/
@[simp] theorem functor_obj (a : Obj S) : I.functor.obj a = I.obj a := rfl

/--
@isnad1 id=eq.0h6v.s6.4f99564973e5 from=translated src=- shape=1744d04d vocab=fa6f63c1
-/
theorem functor_map (f : a ⟶ b) :
    I.functor.map f = I.mapChain a (Diagram.layers f) b (Diagram.chain f) := rfl

/--
@isnad1 id=eq.3h6v.s7.4b30523b3579 from=translated src=- shape=67c62c38 vocab=539b2cde
-/
@[simp] theorem functor_map_layer (L : Layer S) (hv : L.Valid) {a b : Obj S} (ha : L.dom = a)
    (hb : L.cod = b) :
    I.functor.map (Diagram.layer L hv ha hb) =
      eqToHom (congrArg I.obj ha.symm) ≫ I.layer L hv ≫ eqToHom (congrArg I.obj hb) := rfl

/--
@isnad1 id=eq.1h4v.s6.53016472ac1f from=translated src=- shape=39ff8792 vocab=2d528b0b
-/
theorem functor_map_ofLayer (L : Layer S) (hv : L.Valid) :
    I.functor.map (Diagram.ofLayer L hv) = I.layer L hv := by
  show eqToHom (congrArg I.obj rfl) ≫ I.layer L hv ≫ eqToHom (congrArg I.obj rfl) = _
  simp

/-- The image of a diagram given by an explicit list of layers.
@isnad1 id=eq.1h7v.s7.fddade09d2bd from=translated src=- shape=e44cb236 vocab=221cd5ef
-/
theorem functor_map_mk_cons {a b : Obj S} (L : Layer S) (ls : List (Layer S))
    (h : Chain a (L :: ls) b) :
    I.functor.map (Diagram.mk (L :: ls) h) =
      eqToHom (congrArg I.obj h.2.1.symm) ≫ I.layer L h.1 ≫
        I.functor.map (Diagram.mk ls h.2.2) := rfl

/--
@isnad1 id=eq.1h5v.s6.a5bb5d99f901 from=translated src=- shape=8821bdf5 vocab=26994fd1
-/
theorem functor_map_mk_nil {a b : Obj S} (h : Chain a [] b) :
    I.functor.map (Diagram.mk [] h) = eqToHom (congrArg I.obj h) := rfl

end Interpretation

/-! ## Linear extension and descent -/

section Linear

variable (R : Type w) [CommRing R] {D : Type w₁} [Category.{w₂} D] [Preadditive D] [Linear R D]

open Preadditive Linear

variable {R}

namespace Presentation

variable (P : Presentation.{w, v} S R) (F : Obj S ⥤ D)

variable {P F}

end Presentation

end Linear

end StringDiagrams

end
