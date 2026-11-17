import Tengoku.StringDiagramsLean.StringDiagrams.Interpretation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Interpretations with index-dependent objects and index-preserving layers

Many interpretations send an object `a` to a member `X (κ a)` of a family of objects indexed by
some invariant `κ a` preserved by every layer (typically the number of strands), and a layer
`L` to an endomorphism `A L i` of `X i` at `i = κ L.dom`. The images of objects are then only
propositionally equal along a diagram, so the image of a diagram is a composite of layer
images interleaved with `eqToHom`s. This file removes those transports once and for all: after
transport to `X i`, the image of every diagram is the product in `End (X i)` of the
endomorphisms of its layers, and linear combinations of diagrams are evaluated linearly in
`End (X i)`. Unlike `StringDiagrams.LocalInterpretation`, no ambient module is needed: the
target is an arbitrary (linear) category.

## Main results

* `endList A i ls : End (X i)`: the product of the endomorphisms of a list of layers, the
  bottom layer acting first (`endList_cons : endList A i (L :: ls) = endList A i ls * A L i`).
* `Interpretation.map_transport`: **transport lemma** for an arbitrary interpretation `I` with
  `I.obj a = X (κ a)` whose layers are, after transport, the endomorphisms `A L (κ L.dom)`: the
  image of a diagram `f : a ⟶ b` with `κ a = κ b = i`, transported to `X i`, is
  `endList A i (layers f)`.
* `Interpretation.ofEnd κ X A hκ`: the interpretation with `obj a = X (κ a)` and layers
  `A L (κ L.dom)`, with `ofEnd_map_transport`.
* `linEnd`, `linEndW`: linear evaluation of linear combinations of diagrams in `End (X i)`
  (after whiskering by `u`, `v` for `linEndW`); `Interpretation.freeLift_map_transport`
  identifies them with the linear extension `freeLift`.
* `Interpretation.respects_of_linEndW`: **reduction of `Presentation.Respects` to linear
  evaluation**: the functor respects `P` as soon as `linEndW` kills every whiskered relation
  and every whiskered interchange relation; `linEndW_interchange_eq_zero` derives the
  interchange part from a Koszul-signed commutation of the endomorphisms of layers at disjoint
  positions.
* `Interpretation.lift_diag_transport`: the descended functor `P.lift` on the class of a
  diagram, transported to `X i`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w u₀ u₁ u₂ u₃ v₃ u₄

variable {S : Signature.{u₀, u₁, u₂}} {D : Type u₃} [Category.{v₃} D] {ι : Type u₄}
  {X : ι → D}

/-! ## Products of endomorphisms of layers -/

section EndList

variable (A : Layer S → ∀ i, End (X i))

/-- The product of the endomorphisms of a list of layers at index `i`; the first (bottom)
layer acts first.-/
def endList (i : ι) : List (Layer S) → End (X i)
  | [] => 1
  | L :: ls => endList i ls * A L i

/--
@isnad1 id=eq.0h6v.s6.457833194d42 from=translated src=- shape=ffb1f16f vocab=3efa0f75
-/
@[simp] theorem endList_nil (i : ι) : endList A i [] = 1 := rfl

/--
@isnad1 id=eq.0h8v.s6.ff904a852d38 from=translated src=- shape=4533b09d vocab=deafb3af
-/
@[simp] theorem endList_cons (i : ι) (L : Layer S) (ls : List (Layer S)) :
    endList A i (L :: ls) = endList A i ls * A L i := rfl

/-- A single layer: no trailing `1 *`. The priority makes `simp` prefer it to `endList_cons`.
@isnad1 id=eq.0h7v.s5.52a7c5ae2fa2 from=translated src=- shape=35fc0a4a vocab=3dedfe0c
-/
@[simp 1100] theorem endList_singleton (i : ι) (L : Layer S) : endList A i [L] = A L i :=
  one_mul _

/--
@isnad1 id=eq.0h8v.s7.48bc6b9323ef from=translated src=- shape=4fdfa837 vocab=b1469d65
-/
@[simp] theorem endList_append (i : ι) (ls ms : List (Layer S)) :
    endList A i (ls ++ ms) = endList A i ms * endList A i ls := by
  induction ls with
  | nil => rw [List.nil_append, endList_nil, mul_one]
  | cons L ls ih => rw [List.cons_append, endList_cons, ih, endList_cons, mul_assoc]

end EndList

/-! ## The transport lemma -/

/-- Along a chain of index-preserving layers the index is constant.
@isnad1 id=eq.2h6v.s5.d0b3984aac1d from=translated src=- shape=adf261f7 vocab=14508426
-/
theorem Chain.index_eq {κ : Obj S → ι} (hκ : ∀ L : Layer S, L.Valid → κ L.cod = κ L.dom) :
    ∀ {a b : Obj S} {ls : List (Layer S)}, Chain a ls b → κ b = κ a
  | _, _, [], h => by cases h; rfl
  | _, _, L :: _, ⟨hv, hd, hc⟩ => by rw [Chain.index_eq hκ hc, hκ L hv, hd]

/-- Diagrams of index-preserving layers preserve the index.
@isnad1 id=eq.1h6v.s5.2c5b7c4d0c72 from=translated src=- shape=e47b5f0b vocab=d6b51766
-/
theorem Diagram.index_eq {κ : Obj S → ι} (hκ : ∀ L : Layer S, L.Valid → κ L.cod = κ L.dom)
    {a b : Obj S} (f : a ⟶ b) : κ b = κ a :=
  Chain.index_eq hκ (Diagram.chain f)

namespace Interpretation

variable (I : Interpretation S D) {κ : Obj S → ι} {A : Layer S → ∀ i, End (X i)}
  (hobj : ∀ a, I.obj a = X (κ a)) (hκ : ∀ L : Layer S, L.Valid → κ L.cod = κ L.dom)

/-- The hypothesis of the transport lemma: after transport to `X (κ L.dom)`, the image of a
layer is `A L (κ L.dom)`.-/
def LayerTransport : Prop :=
  ∀ (L : Layer S) (hv : L.Valid),
    eqToHom (hobj L.dom).symm ≫ I.layer L hv ≫
      eqToHom ((hobj L.cod).trans (congrArg X (hκ L hv))) = A L (κ L.dom)

variable {I hobj hκ}

/-- **Transport lemma for chains of layers.**
@isnad1 id=eq.6h11v.s7.1aa23c10f7f4 from=translated src=- shape=30542aac vocab=b01568f6
-/
theorem mapChain_transport (hA : I.LayerTransport (A := A) hobj hκ) :
    ∀ {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b) {i : ι} (ha : κ a = i)
      (hb : κ b = i),
      eqToHom ((hobj a).trans (congrArg X ha)).symm ≫ I.mapChain a ls b h ≫
        eqToHom ((hobj b).trans (congrArg X hb)) = endList A i ls
  | a, b, [], h, i, ha, hb => by
    cases h
    simp [mapChain, End.one_def]
  | a, b, L :: ls, ⟨hv, hd, hc⟩, i, ha, hb => by
    subst ha hd
    have ih := mapChain_transport hA hc (hκ L hv) hb
    rw [endList_cons, End.mul_def, ← hA L hv, ← ih]
    simp [mapChain]

/-- **Transport lemma.** For an interpretation `I` with `I.obj a = X (κ a)` whose layers are,
after transport, the endomorphisms `A L (κ L.dom)`, the image of a diagram `f : a ⟶ b` with
`κ a = κ b = i`, transported to `X i`, is the product of the endomorphisms of its layers.
@isnad1 id=eq.5h11v.s7.0e6ad1177677 from=translated src=- shape=54cc7c5c vocab=7b114630
-/
theorem map_transport (hA : I.LayerTransport (A := A) hobj hκ) {a b : Obj S} (f : a ⟶ b)
    {i : ι} (ha : κ a = i) (hb : κ b = i) :
    eqToHom ((hobj a).trans (congrArg X ha)).symm ≫ I.functor.map f ≫
        eqToHom ((hobj b).trans (congrArg X hb)) = endList A i (Diagram.layers f) :=
  mapChain_transport hA (Diagram.chain f) ha hb

/-! ## The interpretation by endomorphisms -/

/-- The interpretation sending `a` to `X (κ a)` and a layer `L` to `A L (κ L.dom)`.-/
def ofEnd (κ : Obj S → ι) (X : ι → D) (A : Layer S → ∀ i, End (X i))
    (hκ : ∀ L : Layer S, L.Valid → κ L.cod = κ L.dom) : Interpretation S D where
  obj a := X (κ a)
  layer L hv := A L (κ L.dom) ≫ eqToHom (congrArg X (hκ L hv).symm)

/--
@isnad1 id=eq.1h7v.s6.7e6a830858d4 from=translated src=- shape=0c34f00f vocab=8ac46a0d
-/
@[simp] theorem ofEnd_obj (a : Obj S) : (ofEnd κ X A hκ).obj a = X (κ a) := rfl

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=layertra.1h6v.s6.83149b57a3bf from=translated src=- shape=1a1cd84c vocab=8afd40eb
-/
theorem ofEnd_layerTransport :
    (ofEnd κ X A hκ).LayerTransport (A := A) (fun _ => rfl) hκ := fun L hv => by
  simp [ofEnd]

/-- The image of a diagram under `ofEnd`, transported to `X i`.
@isnad1 id=eq.3h10v.s7.4f8e9d712653 from=translated src=- shape=f5b237e0 vocab=d31933ca
-/
theorem ofEnd_map_transport {a b : Obj S} (f : a ⟶ b) {i : ι} (ha : κ a = i) (hb : κ b = i) :
    eqToHom (congrArg X ha).symm ≫ (ofEnd κ X A hκ).functor.map f ≫ eqToHom (congrArg X hb) =
      endList A i (Diagram.layers f) :=
  Interpretation.map_transport (I := ofEnd κ X A hκ) (X := X) (κ := κ) (A := A) (hκ := hκ)
    (hobj := fun _ => rfl) ofEnd_layerTransport f ha hb

set_option backward.isDefEq.respectTransparency false in
/-- The image of an endomorphism diagram under `ofEnd`.
@isnad1 id=eq.1h8v.s7.f94161490e04 from=translated src=- shape=68205881 vocab=d6106167
-/
theorem ofEnd_map_end {a : Obj S} (f : a ⟶ a) :
    (ofEnd κ X A hκ).functor.map f = endList A (κ a) (Diagram.layers f) := by
  simpa using ofEnd_map_transport (hκ := hκ) (A := A) f rfl rfl

end Interpretation

/-! ## Linear evaluation -/

section Linear

variable {R : Type w} [CommRing R] [Preadditive D] [Linear R D] (A : Layer S → ∀ i, End (X i))

/-- Linear evaluation of linear combinations of diagrams in `End (X i)`: a diagram `d` goes to
`endList A i (layers d)`.-/
def linEnd (i : ι) {a b : Obj S} : ((a ⟶ b) →₀ R) →ₗ[R] End (X i) :=
  Finsupp.linearCombination R fun d : a ⟶ b => endList A i (Diagram.layers d)

/-- Linear evaluation after whiskering by `u` on the left and `v` on the right.-/
def linEndW (i : ι) (u : Obj S) (v : List S.Colour) {a b : Obj S} :
    ((a ⟶ b) →₀ R) →ₗ[R] End (X i) :=
  Finsupp.linearCombination R fun d : a ⟶ b =>
    endList A i ((Diagram.layers d).map (·.whisker u v))

section LinEndLemmas

variable (i : ι) {a b : Obj S}

/--
@isnad1 id=eq.0h11v.s9.857d5ede9987 from=translated src=- shape=ec9c6060 vocab=375b7007
-/
@[simp] theorem linEnd_single (d : a ⟶ b) (r : R) :
    linEnd A i (Finsupp.single d r : LinDiagram R a b) = r • endList A i (Diagram.layers d) :=
  Finsupp.linearCombination_single R r d

/--
@isnad1 id=eq.0h10v.s9.d2f9375059c0 from=translated src=- shape=5b0e0638 vocab=7877d2f9
-/
@[simp] theorem linEnd_of (d : a ⟶ b) :
    linEnd A i (LinDiagram.of d : LinDiagram R a b) = endList A i (Diagram.layers d) := by
  rw [LinDiagram.of, linEnd_single, one_smul]

variable (u : Obj S) (v : List S.Colour)

/--
@isnad1 id=eq.0h13v.s9.4455832510b7 from=translated src=- shape=8048f3cc vocab=6619c61f
-/
@[simp] theorem linEndW_single (d : a ⟶ b) (r : R) :
    linEndW A i u v (Finsupp.single d r : LinDiagram R a b) =
      r • endList A i ((Diagram.layers d).map (·.whisker u v)) :=
  Finsupp.linearCombination_single R r d

/--
@isnad1 id=eq.0h12v.s9.3aec52226096 from=translated src=- shape=60662479 vocab=da17ac86
-/
@[simp] theorem linEndW_of (d : a ⟶ b) :
    linEndW A i u v (LinDiagram.of d : LinDiagram R a b) =
      endList A i ((Diagram.layers d).map (·.whisker u v)) := by
  rw [LinDiagram.of, linEndW_single, one_smul]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating a whiskered linear combination is whiskered evaluation.
@isnad1 id=eq.1h12v.s9.a125b2960a8a from=translated src=- shape=6821c0ce vocab=fccc0b38
-/
theorem linEnd_whisker (Y : LinDiagram R a b) (hw : a.WhiskerOK u v) :
    linEnd A i (LinDiagram.whisker Y u v hw) = linEndW A i u v Y := by
  rw [linEnd, LinDiagram.whisker, Finsupp.linearCombination_mapDomain]
  rfl

end LinEndLemmas

namespace Interpretation

variable {I : Interpretation S D} {κ : Obj S → ι} {A}
  {hobj : ∀ a, I.obj a = X (κ a)} {hκ : ∀ L : Layer S, L.Valid → κ L.cod = κ L.dom}

end Interpretation

/-- The whiskered linear evaluation of an interchange relation: the two orders of the layers
of `g` (left) and `h` (right), with the Koszul sign.
@isnad1 id=eq.1h10v.s9.747af689f819 from=translated src=- shape=c02e517a vocab=1ca41a54
-/
theorem linEndW_interchange (x : InterchangeData S) (hx : x.Valid) (u : Obj S)
    (v : List S.Colour) (i : ι) :
    linEndW A i u v (InterchangeData.rel R hx) =
      A ⟨u.start, u.word ++ (S.cod x.g ++ x.mid), x.h, v⟩ i *
          A ⟨u.start, u.word, x.g, x.mid ++ (S.dom x.h ++ v)⟩ i -
        ((x.sign : ℤ) : R) •
          (A ⟨u.start, u.word, x.g, x.mid ++ (S.cod x.h ++ v)⟩ i *
            A ⟨u.start, u.word ++ (S.dom x.g ++ x.mid), x.h, v⟩ i) := by
  simp only [InterchangeData.rel, map_sub, map_smul, linEndW_of, InterchangeData.ghDiagram,
    InterchangeData.hgDiagram, Diagram.layers_mk, List.map_cons, List.map_nil, endList_cons,
    endList_nil, one_mul, InterchangeData.gh₁, InterchangeData.gh₂, InterchangeData.hg₁,
    InterchangeData.hg₂, Layer.whisker, List.append_nil, List.nil_append, List.append_assoc]

/-- The interchange part of the soundness hypotheses from a commutation hypothesis: for all
generators `g`, `g'` separated by the word `m`, with `l` to the left and `r` to the right,
the endomorphisms of the two layers commute up to the Koszul sign, at the index of the
source.
@isnad1 id=eq.1h11v.s10.5b27059c22eb from=translated src=- shape=ed086402 vocab=0834d56b
-/
theorem linEndW_interchange_eq_zero {κ : Obj S → ι}
    (hcomm : ∀ (s : S.Region) (l m r : List S.Colour) (g g' : S.Gen),
      let i := κ ⟨s, l ++ (S.dom g ++ (m ++ (S.dom g' ++ r)))⟩
      A ⟨s, l ++ (S.cod g ++ m), g', r⟩ i * A ⟨s, l, g, m ++ (S.dom g' ++ r)⟩ i =
        (((⟨s, g, m, g'⟩ : InterchangeData S).sign : ℤ) : R) •
          (A ⟨s, l, g, m ++ (S.cod g' ++ r)⟩ i * A ⟨s, l ++ (S.dom g ++ m), g', r⟩ i))
    (x : InterchangeData S) (hx : x.Valid) (u : Obj S) (v : List S.Colour) :
    linEndW A (κ (x.dom.whisker u v)) u v (InterchangeData.rel R hx) = 0 := by
  have hd : x.dom.whisker u v =
      ⟨u.start, u.word ++ (S.dom x.g ++ (x.mid ++ (S.dom x.h ++ v)))⟩ := by
    simp [InterchangeData.dom, Obj.whisker]
  rw [linEndW_interchange, hd, hcomm u.start u.word x.mid v x.g x.h, sub_eq_zero]
  rfl

end Linear

end StringDiagrams

end
