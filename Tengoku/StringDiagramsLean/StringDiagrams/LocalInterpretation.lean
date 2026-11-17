import Tengoku.StringDiagramsLean.StringDiagrams.Generation
import Tengoku.StringDiagramsLean.StringDiagrams.Interpretation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Interpretations by local operators

Many representations of presented categories are given by *local operators*: each object
`a` is sent to a module `M (κ a)` depending only on an index `κ a` (typically the number of
strands, or the word itself), and a layer acts by an operator determined by its generator
and its position. This file packages the transport and soundness bookkeeping common to all
such representations, so that it is done once.

## Setting

A `LocalInterpretation S R V M` consists of

* an index map `κ : Obj S → ι` and modules `M i`;
* a common *ambient* module `V` with, for every index `i`, a section `ext i : M i → V` and a
  retraction `res i : V → M i` (`res i ∘ ext i = id`);
* for every layer `L` an operator `op L : V → V` which is *local*: the component of
  `op L x` of index `κ L.cod` only depends on the component of `x` of index `κ L.dom`.

The image of a layer is `res (κ L.cod) ∘ op L ∘ ext (κ L.dom)`. Because all operators act on
the single module `V`, composites of layers never need to be transported along equalities of
indices; indices only appear at the two ends (`res`, `ext`), and there any equality of indices
can be absorbed by `subst`.

Three common shapes are covered:

* a single module for all objects (`LocalInterpretation.uniform`, `ι = Unit`,
  `ext = res = id`), as for the polynomial representation of free commuting dots;
* width-dependent modules embedded in a big module of functions, as for the
  Temperley–Lieb representation on functions of words, where `ext` is extension by zero and
  `res` is restriction;
* width-preserving layers acting componentwise on `Π i, M i` (`LocalInterpretation.pi`),
  where every diagram between objects of index `i` acts on `M i` by the product of the
  component operators of its layers (`pi_functor_map_transport`).

## Main results

* `LocalInterpretation.interp`, `LocalInterpretation.functor`: the interpretation in
  `ModuleCat R` and the functor out of the free 2-category.
* `functor_map_hom`: the image of a diagram `f : a ⟶ b` is
  `res (κ b) ∘ opList (layers f) ∘ ext (κ a)`, where `opList` composes the layer operators
  (bottom layer first); `functor_map_transport` is the same statement after transport along
  arbitrary equalities `κ a = i`, `κ b = j`. Proved once, by induction on the layers, from
  locality.
* `eval`, `evalW`: linear evaluation of linear combinations of diagrams (the latter after
  whiskering by `u` and `v`), with simp lemmas for `of`, `single`, `+`, `-`, `•`, `0`;
  `freeLift_map_hom`, `freeLift_map_whisker_hom` identify them with the linear extension
  `freeLift`, so that `Presentation.Respects` need never be unfolded.
* `respects_of`: `P.Respects Q.functor` from the vanishing of `evalW` on every whiskered
  relation and interchange instance; `evalW_interchange_eq_zero` derives the interchange part
  from a commutation (Koszul sign) hypothesis on pairs of layers at disjoint positions.
* `Presentation.int_smul_eq_zsmul`, `Presentation.hom_induction_int`: over `R = ℤ`, the
  scalar multiplication of the linear structure of a presented category agrees with `zsmul`,
  and induction on morphisms needs no scalar case.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w w₁ w₂ w₃ u₀ u₁ u₂

/-- An interpretation of the free 2-category on `S` by local operators on an ambient module
`V`, with the object `a` sent to `M (κ a)`. See the module documentation.-/
structure LocalInterpretation (S : Signature.{u₀, u₁, u₂}) (R : Type w) [CommRing R]
    {ι : Type w₁} (V : Type w₃) [AddCommGroup V] [Module R V]
    (M : ι → Type w₂) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] where
  /-- The index of an object.-/
  κ : Obj S → ι
  /-- The inclusion of `M i` into the ambient module.-/
  ext : ∀ i, M i →ₗ[R] V
  /-- The projection of the ambient module onto `M i`.-/
  res : ∀ i, V →ₗ[R] M i
  /-- The operator of a layer on the ambient module.-/
  op : Layer S → V →ₗ[R] V
  res_comp_ext : ∀ i, res i ∘ₗ ext i = LinearMap.id
  /-- Locality: the output component of index `κ L.cod` only depends on the input component
  of index `κ L.dom`.-/
  res_op_ext_res : ∀ L : Layer S, L.Valid →
    res (κ L.cod) ∘ₗ op L ∘ₗ ext (κ L.dom) ∘ₗ res (κ L.dom) = res (κ L.cod) ∘ₗ op L

namespace LocalInterpretation

variable {S : Signature.{u₀, u₁, u₂}} {R : Type w} [CommRing R] {ι : Type w₁}
  {V : Type w₃} [AddCommGroup V] [Module R V]
  {M : ι → Type w₂} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (Q : LocalInterpretation S R V M)

/--
@isnad1 id=eq.0h8v.s8.6eb589706815 from=translated src=- shape=730a63fd vocab=a41839ac
-/
@[simp] theorem res_ext_apply (i : ι) (x : M i) : Q.res i (Q.ext i x) = x :=
  LinearMap.congr_fun (Q.res_comp_ext i) x

/-! ## Operators of lists of layers -/

/-- The composite of the operators of a list of layers; the first (bottom) layer acts
first.-/
def opList : List (Layer S) → (V →ₗ[R] V)
  | [] => LinearMap.id
  | L :: ls => opList ls ∘ₗ Q.op L

/--
@isnad1 id=eq.0h6v.s7.95a54c16d574 from=translated src=- shape=07f33c40 vocab=04dd0e45
-/
@[simp] theorem opList_nil : Q.opList [] = LinearMap.id := rfl

/--
@isnad1 id=eq.0h8v.s7.92e1cb244afa from=translated src=- shape=e8f87b0a vocab=6ceeed59
-/
@[simp] theorem opList_cons (L : Layer S) (ls : List (Layer S)) :
    Q.opList (L :: ls) = Q.opList ls ∘ₗ Q.op L := rfl

/--
@isnad1 id=eq.0h8v.s7.16f4455c53e5 from=translated src=- shape=1d937800 vocab=b1727c88
-/
@[simp] theorem opList_append (ls ms : List (Layer S)) :
    Q.opList (ls ++ ms) = Q.opList ms ∘ₗ Q.opList ls := by
  induction ls with
  | nil => rfl
  | cons L ls ih => rw [List.cons_append, opList_cons, ih, opList_cons, LinearMap.comp_assoc]

/-- A single layer: no trailing identity (`LinearMap.id ∘ₗ`) is left behind. The priority
makes `simp` prefer it to `opList_cons`, so that composites of explicit layers normalise to
`op Lₙ ∘ₗ ⋯ ∘ₗ op L₁`.
@isnad1 id=eq.0h7v.s7.8d5476520281 from=translated src=- shape=70052549 vocab=2f61a2f0
-/
@[simp 1100] theorem opList_singleton (L : Layer S) : Q.opList [L] = Q.op L := rfl

/-- Pointwise form of `opList_nil`.
@isnad1 id=eq.0h7v.s7.bcad81c2db3b from=translated src=- shape=36e01d3d vocab=a8fdf4e1
-/
@[simp] theorem opList_nil_apply (x : V) : Q.opList [] x = x := rfl

/-- Pointwise form of `opList_cons`: the bottom layer acts first. Together with
`opList_nil_apply` this evaluates the operator of an explicit list of layers on a vector
without ever forming composites of linear maps.
@isnad1 id=eq.0h9v.s8.a6561f785676 from=translated src=- shape=cd89dc98 vocab=4dc6744f
-/
@[simp] theorem opList_cons_apply (L : Layer S) (ls : List (Layer S)) (x : V) :
    Q.opList (L :: ls) x = Q.opList ls (Q.op L x) := rfl

/-- Locality of a chain of layers.
@isnad1 id=eq.1h10v.s10.c1ab4968a097 from=translated src=- shape=4ea33b8d vocab=905da03c
-/
theorem res_opList_ext_res {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b) (x : V) :
    Q.res (Q.κ b) (Q.opList ls (Q.ext (Q.κ a) (Q.res (Q.κ a) x))) =
      Q.res (Q.κ b) (Q.opList ls x) := by
  induction ls generalizing a x with
  | nil =>
    cases h
    simp
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    have hL := LinearMap.congr_fun (Q.res_op_ext_res L hv) x
    simp only [LinearMap.comp_apply] at hL
    simp only [opList_cons, LinearMap.comp_apply]
    rw [← ih hc, hL, ih hc]

/-! ## The interpretation -/

/-- The module `M i` as an object of `ModuleCat R`.-/
abbrev mod (i : ι) : ModuleCat.{w₂} R := ModuleCat.of R (M i)

/-- The interpretation: `a` goes to `M (κ a)`, a layer `L` to
`res (κ L.cod) ∘ op L ∘ ext (κ L.dom)`.-/
def interp : Interpretation S (ModuleCat.{w₂} R) where
  obj a := mod (M := M) (Q.κ a)
  layer L _ := ModuleCat.ofHom (Q.res (Q.κ L.cod) ∘ₗ Q.op L ∘ₗ Q.ext (Q.κ L.dom))

/-- The functor from the free 2-category.-/
def functor : Obj S ⥤ ModuleCat.{w₂} R := Q.interp.functor

/--
@isnad1 id=eq.0h7v.s6.c3ae8c52c1cd from=translated src=- shape=c51dbff9 vocab=43ef0a85
-/
@[simp] theorem functor_obj (a : Obj S) : Q.functor.obj a = mod (M := M) (Q.κ a) := rfl

/--
@isnad1 id=eq.0h7v.s6.d5cdc40d3840 from=translated src=- shape=69c985fc vocab=530b4a67
-/
@[simp] theorem interp_obj (a : Obj S) : Q.interp.obj a = mod (M := M) (Q.κ a) := rfl

/--
@isnad1 id=eq.1h7v.s9.6fbcd0b6f0ca from=translated src=- shape=9b8d6ba8 vocab=5c411844
-/
@[simp] theorem interp_layer (L : Layer S) (hv : L.Valid) :
    Q.interp.layer L hv = ModuleCat.ofHom (Q.res (Q.κ L.cod) ∘ₗ Q.op L ∘ₗ Q.ext (Q.κ L.dom)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The image of a chain of layers.
@isnad1 id=eq.1h9v.s9.81be0512605f from=translated src=- shape=d6475463 vocab=025268db
-/
theorem interp_mapChain_hom {a b : Obj S} (ls : List (Layer S)) (h : Chain a ls b) :
    (Q.interp.mapChain a ls b h).hom = Q.res (Q.κ b) ∘ₗ Q.opList ls ∘ₗ Q.ext (Q.κ a) := by
  induction ls generalizing a with
  | nil =>
    cases h
    refine LinearMap.ext fun x => ?_
    simp only [Interpretation.mapChain, eqToHom_refl, ModuleCat.hom_id, opList_nil,
      LinearMap.id_comp, LinearMap.id_apply]
    exact (Q.res_ext_apply _ x).symm
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    refine LinearMap.ext fun x => ?_
    simp only [Interpretation.mapChain, eqToHom_refl, Category.id_comp, ModuleCat.hom_comp, ih hc,
      interp_layer, ModuleCat.hom_ofHom, LinearMap.comp_apply, opList_cons]
    exact Q.res_opList_ext_res hc _

/-- **The image of a diagram** is the composite of the operators of its layers, between the
inclusion and the projection of the end indices.
@isnad1 id=eq.0h9v.s9.69fbd0b98fb1 from=translated src=- shape=c4c3b43c vocab=a54a062d
-/
theorem functor_map_hom {a b : Obj S} (f : a ⟶ b) :
    (Q.functor.map f).hom = Q.res (Q.κ b) ∘ₗ Q.opList (Diagram.layers f) ∘ₗ Q.ext (Q.κ a) :=
  Q.interp_mapChain_hom _ _

/--
@isnad1 id=eq.0h10v.s10.f05a7cd594c0 from=translated src=- shape=e9506bed vocab=80fea00e
-/
theorem functor_map_apply {a b : Obj S} (f : a ⟶ b) (x : M (Q.κ a)) :
    (Q.functor.map f).hom x = Q.res (Q.κ b) (Q.opList (Diagram.layers f) (Q.ext (Q.κ a) x)) := by
  rw [functor_map_hom]; rfl

set_option backward.isDefEq.respectTransparency false in
/-- The image of a diagram, transported along arbitrary equalities of the end indices.
@isnad1 id=eq.2h11v.s9.9301fbd69872 from=translated src=- shape=611263f2 vocab=dc1be557
-/
theorem functor_map_transport {a b : Obj S} {i j : ι} (f : a ⟶ b) (ha : Q.κ a = i)
    (hb : Q.κ b = j) :
    eqToHom (congrArg (mod (M := M)) ha.symm) ≫ Q.functor.map f ≫
        eqToHom (congrArg (mod (M := M)) hb) =
      ModuleCat.ofHom (Q.res j ∘ₗ Q.opList (Diagram.layers f) ∘ₗ Q.ext i) := by
  subst ha hb
  apply ModuleCat.hom_ext
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, functor_map_hom,
    ModuleCat.hom_ofHom]

/-- The image of a single layer.
@isnad1 id=eq.3h9v.s9.0a0246068084 from=translated src=- shape=676292b6 vocab=972fc3a1
-/
theorem functor_map_layer_hom (L : Layer S) (hv : L.Valid) {a b : Obj S} (ha : L.dom = a)
    (hb : L.cod = b) :
    (Q.functor.map (Diagram.layer L hv ha hb)).hom =
      Q.res (Q.κ b) ∘ₗ Q.op L ∘ₗ Q.ext (Q.κ a) := by
  rw [functor_map_hom, Diagram.layers_layer, opList_cons, opList_nil, LinearMap.id_comp]

/-! ## Linear evaluation -/

/-- Linear evaluation of linear combinations of diagrams from `a` to `b`, between the indices
`i` and `j`: a diagram `d` goes to `res j ∘ opList (layers d) ∘ ext i`.-/
def eval (i j : ι) {a b : Obj S} : ((a ⟶ b) →₀ R) →ₗ[R] (M i →ₗ[R] M j) :=
  Finsupp.linearCombination R fun d : a ⟶ b =>
    Q.res j ∘ₗ Q.opList (Diagram.layers d) ∘ₗ Q.ext i

/-- Linear evaluation after whiskering by `u` on the left and `v` on the right: a diagram `d`
goes to `res j ∘ opList (layers (u ⊗ d ⊗ v)) ∘ ext i`.-/
def evalW (i j : ι) (u : Obj S) (v : List S.Colour) {a b : Obj S} :
    ((a ⟶ b) →₀ R) →ₗ[R] (M i →ₗ[R] M j) :=
  Finsupp.linearCombination R fun d : a ⟶ b =>
    Q.res j ∘ₗ Q.opList ((Diagram.layers d).map (·.whisker u v)) ∘ₗ Q.ext i

section EvalLemmas

variable (i j : ι) {a b : Obj S}

/--
@isnad1 id=eq.0h12v.s10.a93e125e2feb from=translated src=- shape=f6700b1c vocab=67ec17ca
-/
@[simp] theorem eval_single (d : a ⟶ b) (r : R) :
    Q.eval i j (Finsupp.single d r : LinDiagram R a b) =
      r • (Q.res j ∘ₗ Q.opList (Diagram.layers d) ∘ₗ Q.ext i) :=
  Finsupp.linearCombination_single R r d

/--
@isnad1 id=eq.0h11v.s10.165a52d9d481 from=translated src=- shape=660be45d vocab=d31b8813
-/
@[simp] theorem eval_of (d : a ⟶ b) :
    Q.eval i j (LinDiagram.of d : LinDiagram R a b) =
      Q.res j ∘ₗ Q.opList (Diagram.layers d) ∘ₗ Q.ext i := by
  rw [LinDiagram.of, eval_single, one_smul]

/--
@isnad1 id=eq.0h10v.s10.b6502d9ebb32 from=translated src=- shape=0aca1226 vocab=f89fcd4d
-/
@[simp] theorem eval_zero : Q.eval i j (0 : LinDiagram R a b) = 0 := map_zero _

/--
@isnad1 id=eq.0h12v.s11.e04576db519f from=translated src=- shape=89ebd78f vocab=ad6425d6
-/
@[simp] theorem eval_add (X Y : LinDiagram R a b) :
    Q.eval i j (X + Y : LinDiagram R a b) = Q.eval i j X + Q.eval i j Y := map_add _ X Y

/--
@isnad1 id=eq.0h12v.s11.bea3c514f528 from=translated src=- shape=89ebd78f vocab=96c74e10
-/
@[simp] theorem eval_sub (X Y : LinDiagram R a b) :
    Q.eval i j (X - Y : LinDiagram R a b) = Q.eval i j X - Q.eval i j Y := map_sub _ X Y

/--
@isnad1 id=eq.0h11v.s10.b6e8828f3e58 from=translated src=- shape=a3258aee vocab=695cdca9
-/
@[simp] theorem eval_neg (X : LinDiagram R a b) :
    Q.eval i j (-X : LinDiagram R a b) = -Q.eval i j X := map_neg _ X

/--
@isnad1 id=eq.0h12v.s11.0879d1a1190c from=translated src=- shape=0be81ba0 vocab=cb121ee4
-/
@[simp] theorem eval_smul (r : R) (X : LinDiagram R a b) :
    Q.eval i j (r • X : LinDiagram R a b) = r • Q.eval i j X := map_smul _ r X

variable (u : Obj S) (v : List S.Colour)

/--
@isnad1 id=eq.0h14v.s10.2d81daa49bdc from=translated src=- shape=4a435e3e vocab=10571a6c
-/
@[simp] theorem evalW_single (d : a ⟶ b) (r : R) :
    Q.evalW i j u v (Finsupp.single d r : LinDiagram R a b) =
      r • (Q.res j ∘ₗ Q.opList ((Diagram.layers d).map (·.whisker u v)) ∘ₗ Q.ext i) :=
  Finsupp.linearCombination_single R r d

/--
@isnad1 id=eq.0h13v.s10.3b5aed11a622 from=translated src=- shape=89148a8e vocab=a1791c82
-/
@[simp] theorem evalW_of (d : a ⟶ b) :
    Q.evalW i j u v (LinDiagram.of d : LinDiagram R a b) =
      Q.res j ∘ₗ Q.opList ((Diagram.layers d).map (·.whisker u v)) ∘ₗ Q.ext i := by
  rw [LinDiagram.of, evalW_single, one_smul]

/--
@isnad1 id=eq.0h12v.s10.9b0dd4b6f065 from=translated src=- shape=074be16a vocab=6edb00b2
-/
@[simp] theorem evalW_zero : Q.evalW i j u v (0 : LinDiagram R a b) = 0 := map_zero _

/--
@isnad1 id=eq.0h14v.s11.e3721839445f from=translated src=- shape=73580240 vocab=a527109e
-/
@[simp] theorem evalW_add (X Y : LinDiagram R a b) :
    Q.evalW i j u v (X + Y : LinDiagram R a b) = Q.evalW i j u v X + Q.evalW i j u v Y :=
  map_add _ X Y

/--
@isnad1 id=eq.0h14v.s11.55ef2a57c1ad from=translated src=- shape=73580240 vocab=e6c4b693
-/
@[simp] theorem evalW_sub (X Y : LinDiagram R a b) :
    Q.evalW i j u v (X - Y : LinDiagram R a b) = Q.evalW i j u v X - Q.evalW i j u v Y :=
  map_sub _ X Y

/--
@isnad1 id=eq.0h13v.s10.d3c1557f04d4 from=translated src=- shape=986f4aeb vocab=28aae834
-/
@[simp] theorem evalW_neg (X : LinDiagram R a b) :
    Q.evalW i j u v (-X : LinDiagram R a b) = -Q.evalW i j u v X := map_neg _ X

/--
@isnad1 id=eq.0h14v.s11.0cd167d1442f from=translated src=- shape=d71e18a2 vocab=07d2ace1
-/
@[simp] theorem evalW_smul (r : R) (X : LinDiagram R a b) :
    Q.evalW i j u v (r • X : LinDiagram R a b) = r • Q.evalW i j u v X := map_smul _ r X

/-- Pointwise evaluation of a single diagram.
@isnad1 id=eq.0h12v.s10.9f75f9eaad1d from=translated src=- shape=71773770 vocab=b35bd4a3
-/
theorem eval_of_apply (d : a ⟶ b) (x : M i) :
    Q.eval i j (LinDiagram.of d : LinDiagram R a b) x =
      Q.res j (Q.opList (Diagram.layers d) (Q.ext i x)) := by
  rw [eval_of]; rfl

/-- Pointwise whiskered evaluation of a single diagram.
@isnad1 id=eq.0h14v.s10.55203e102980 from=translated src=- shape=b9661e1a vocab=6321d29a
-/
theorem evalW_of_apply (d : a ⟶ b) (x : M i) :
    Q.evalW i j u v (LinDiagram.of d : LinDiagram R a b) x =
      Q.res j (Q.opList ((Diagram.layers d).map (·.whisker u v)) (Q.ext i x)) := by
  rw [evalW_of]; rfl

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating a whiskered linear combination is whiskered evaluation.
@isnad1 id=eq.1h13v.s10.a7c3de809651 from=translated src=- shape=f545cd5c vocab=0765b41b
-/
theorem eval_whisker (X : LinDiagram R a b) (hw : a.WhiskerOK u v) :
    Q.eval i j (LinDiagram.whisker X u v hw) = Q.evalW i j u v X := by
  rw [eval, LinDiagram.whisker, Finsupp.linearCombination_mapDomain]
  rfl

end EvalLemmas

/-! ## The linear extension -/

/-! ## Soundness -/

section Respects

variable (P : Presentation S R)

/-- The whiskered evaluation of an interchange relation: the two orders of the layers of
`g` (left) and `h` (right), with the Koszul sign.
@isnad1 id=eq.1h11v.s11.99ebc0868562 from=translated src=- shape=2d97a684 vocab=499908a5
-/
theorem evalW_interchange (x : InterchangeData S) (hx : x.Valid) (u : Obj S)
    (v : List S.Colour) (i j : ι) :
    Q.evalW i j u v (InterchangeData.rel R hx) =
      Q.res j ∘ₗ Q.op ⟨u.start, u.word ++ (S.cod x.g ++ x.mid), x.h, v⟩ ∘ₗ
          Q.op ⟨u.start, u.word, x.g, x.mid ++ (S.dom x.h ++ v)⟩ ∘ₗ Q.ext i -
        ((x.sign : ℤ) : R) •
          (Q.res j ∘ₗ Q.op ⟨u.start, u.word, x.g, x.mid ++ (S.cod x.h ++ v)⟩ ∘ₗ
            Q.op ⟨u.start, u.word ++ (S.dom x.g ++ x.mid), x.h, v⟩ ∘ₗ Q.ext i) := by
  simp only [InterchangeData.rel, evalW_sub, evalW_smul, evalW_of, InterchangeData.ghDiagram,
    InterchangeData.hgDiagram, Diagram.layers_mk, List.map_cons, List.map_nil, opList_cons,
    opList_nil, LinearMap.id_comp, LinearMap.comp_assoc, InterchangeData.gh₁,
    InterchangeData.gh₂, InterchangeData.hg₁, InterchangeData.hg₂, Layer.whisker,
    List.append_nil, List.nil_append, List.append_assoc]

/-- The interchange part of the soundness hypotheses from a commutation hypothesis: for all
generators `g`, `g'` separated by the word `m`, with `l` to the left and `r` to the right,
applying `g` then `g'` equals the Koszul sign times applying `g'` then `g`, between the
inclusion and the projection of the end indices.
@isnad1 id=eq.2h9v.s13.f02eef5d0e68 from=translated src=- shape=a043ec04 vocab=20f43e20
-/
theorem evalW_interchange_eq_zero
    (hcomm : ∀ (s : S.Region) (l m r : List S.Colour) (g g' : S.Gen),
      Q.res (Q.κ ⟨s, l ++ (S.cod g ++ (m ++ (S.cod g' ++ r)))⟩) ∘ₗ
          Q.op ⟨s, l ++ (S.cod g ++ m), g', r⟩ ∘ₗ Q.op ⟨s, l, g, m ++ (S.dom g' ++ r)⟩ ∘ₗ
          Q.ext (Q.κ ⟨s, l ++ (S.dom g ++ (m ++ (S.dom g' ++ r)))⟩) =
        (((⟨s, g, m, g'⟩ : InterchangeData S).sign : ℤ) : R) •
          (Q.res (Q.κ ⟨s, l ++ (S.cod g ++ (m ++ (S.cod g' ++ r)))⟩) ∘ₗ
            Q.op ⟨s, l, g, m ++ (S.cod g' ++ r)⟩ ∘ₗ Q.op ⟨s, l ++ (S.dom g ++ m), g', r⟩ ∘ₗ
            Q.ext (Q.κ ⟨s, l ++ (S.dom g ++ (m ++ (S.dom g' ++ r)))⟩)))
    (x : InterchangeData S) (hx : x.Valid) (u : Obj S) (v : List S.Colour) :
    Q.evalW (Q.κ (x.dom.whisker u v)) (Q.κ (x.cod.whisker u v)) u v
      (InterchangeData.rel R hx) = 0 := by
  have hd : x.dom.whisker u v =
      ⟨u.start, u.word ++ (S.dom x.g ++ (x.mid ++ (S.dom x.h ++ v)))⟩ := by
    simp [InterchangeData.dom, Obj.whisker]
  have hc : x.cod.whisker u v =
      ⟨u.start, u.word ++ (S.cod x.g ++ (x.mid ++ (S.cod x.h ++ v)))⟩ := by
    simp [InterchangeData.cod, Obj.whisker]
  rw [hd, hc, evalW_interchange, hcomm u.start u.word x.mid v x.g x.h, sub_eq_zero]
  rfl

/-- The same, from a commutation hypothesis on the ambient module (without projecting).
@isnad1 id=eq.2h9v.s11.b66d737410ee from=translated src=- shape=1ce12d2c vocab=5819b041
-/
theorem evalW_interchange_eq_zero_of_comm
    (hcomm : ∀ (s : S.Region) (l m r : List S.Colour) (g g' : S.Gen),
      Q.op ⟨s, l ++ (S.cod g ++ m), g', r⟩ ∘ₗ Q.op ⟨s, l, g, m ++ (S.dom g' ++ r)⟩ =
        (((⟨s, g, m, g'⟩ : InterchangeData S).sign : ℤ) : R) •
          (Q.op ⟨s, l, g, m ++ (S.cod g' ++ r)⟩ ∘ₗ Q.op ⟨s, l ++ (S.dom g ++ m), g', r⟩))
    (x : InterchangeData S) (hx : x.Valid) (u : Obj S) (v : List S.Colour) :
    Q.evalW (Q.κ (x.dom.whisker u v)) (Q.κ (x.cod.whisker u v)) u v
      (InterchangeData.rel R hx) = 0 := by
  refine Q.evalW_interchange_eq_zero (fun s l m r g g' => LinearMap.ext fun y => ?_) x hx u v
  have h := congrArg (Q.res (Q.κ ⟨s, l ++ (S.cod g ++ (m ++ (S.cod g' ++ r)))⟩))
    (LinearMap.congr_fun (hcomm s l m r g g')
      (Q.ext (Q.κ ⟨s, l ++ (S.dom g ++ (m ++ (S.dom g' ++ r)))⟩) y))
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul] at h ⊢
  exact h

end Respects

/-! ## A single module for all objects -/

section Uniform

/-- All objects are sent to the same module `V`, and layers act by the operators `op`.-/
def uniform (op : Layer S → V →ₗ[R] V) : LocalInterpretation S R V (fun _ : Unit => V) where
  κ _ := ()
  ext _ := LinearMap.id
  res _ := LinearMap.id
  op := op
  res_comp_ext _ := rfl
  res_op_ext_res _ _ := rfl

variable (op : Layer S → V →ₗ[R] V)

/--
@isnad1 id=eq.0h5v.s7.b216c48933ea from=translated src=- shape=2cf6d294 vocab=64aaa2b4
-/
@[simp] theorem uniform_ext (i : Unit) : (uniform op).ext i = LinearMap.id := rfl

/--
@isnad1 id=eq.0h5v.s7.c0a8955b806c from=translated src=- shape=2cf6d294 vocab=f8853f71
-/
@[simp] theorem uniform_res (i : Unit) : (uniform op).res i = LinearMap.id := rfl

/--
@isnad1 id=eq.0h5v.s6.585484b6e0a0 from=translated src=- shape=7b078c3a vocab=bf81b7f7
-/
@[simp] theorem uniform_op (L : Layer S) : (uniform op).op L = op L := rfl

/-- The image of a diagram under a uniform interpretation.
@isnad1 id=eq.0h7v.s9.53108e142af0 from=translated src=- shape=694518e3 vocab=29c4bf63
-/
theorem uniform_functor_map_hom {a b : Obj S} (f : a ⟶ b) :
    ((uniform op).functor.map f).hom = (uniform op).opList (Diagram.layers f) :=
  (uniform op).functor_map_hom f

/--
@isnad1 id=eq.0h6v.s7.12c1415d8756 from=translated src=- shape=16c67ddd vocab=27cf460e
-/
@[simp] theorem uniform_opList_cons (L : Layer S) (ls : List (Layer S)) :
    (uniform op).opList (L :: ls) = (uniform op).opList ls ∘ₗ op L := rfl

/--
@isnad1 id=eq.0h5v.s7.7ffd405bc087 from=translated src=- shape=b927f9ec vocab=8c56aaf7
-/
@[simp 1100] theorem uniform_opList_singleton (L : Layer S) :
    (uniform op).opList [L] = op L := rfl

/--
@isnad1 id=eq.0h7v.s8.adb1e173e2a9 from=translated src=- shape=9fbae0aa vocab=dc074314
-/
@[simp] theorem uniform_opList_cons_apply (L : Layer S) (ls : List (Layer S)) (x : V) :
    (uniform op).opList (L :: ls) x = (uniform op).opList ls (op L x) := rfl

/--
@isnad1 id=eq.0h9v.s9.e7f4e9223545 from=translated src=- shape=1b38b7dc vocab=af9670a6
-/
@[simp] theorem uniform_eval_of (i j : Unit) {a b : Obj S} (d : a ⟶ b) :
    (uniform op).eval i j (LinDiagram.of d : LinDiagram R a b) =
      (uniform op).opList (Diagram.layers d) :=
  (uniform op).eval_of i j d

/--
@isnad1 id=eq.0h11v.s9.661e20b760b6 from=translated src=- shape=1db26c83 vocab=d3988152
-/
@[simp] theorem uniform_evalW_of (i j : Unit) (u : Obj S) (v : List S.Colour) {a b : Obj S}
    (d : a ⟶ b) :
    (uniform op).evalW i j u v (LinDiagram.of d : LinDiagram R a b) =
      (uniform op).opList ((Diagram.layers d).map (·.whisker u v)) :=
  (uniform op).evalW_of i j u v d

/-- Pointwise evaluation of a single diagram under a uniform interpretation (no `ext`/`res`
and no composites of linear maps).
@isnad1 id=eq.0h10v.s9.9e7f1fdd2e43 from=translated src=- shape=2ee5551a vocab=af9670a6
-/
theorem uniform_eval_of_apply (i j : Unit) {a b : Obj S} (d : a ⟶ b) (x : V) :
    (uniform op).eval i j (LinDiagram.of d : LinDiagram R a b) x =
      (uniform op).opList (Diagram.layers d) x := by
  rw [uniform_eval_of]

/-- Pointwise whiskered evaluation of a single diagram under a uniform interpretation.
@isnad1 id=eq.0h12v.s9.7bcf1b0036ad from=translated src=- shape=6ffeec30 vocab=d3988152
-/
theorem uniform_evalW_of_apply (i j : Unit) (u : Obj S) (v : List S.Colour) {a b : Obj S}
    (d : a ⟶ b) (x : V) :
    (uniform op).evalW i j u v (LinDiagram.of d : LinDiagram R a b) x =
      (uniform op).opList ((Diagram.layers d).map (·.whisker u v)) x := by
  rw [uniform_evalW_of]

end Uniform

/-! ## Componentwise operators for index-preserving layers -/

section Pi

variable (κ : Obj S → ι) (A : Layer S → ∀ i, Module.End R (M i))
  (hκ : ∀ L : Layer S, L.Valid → κ L.cod = κ L.dom)

open Classical in
/-- Layers that preserve the index, acting on `Π i, M i` componentwise: the component of
index `i` of `op L` is `A L i`.-/
def pi : LocalInterpretation S R (∀ i, M i) M where
  κ := κ
  ext i := LinearMap.single R M i
  res i := LinearMap.proj i
  op L := LinearMap.pi fun i => A L i ∘ₗ LinearMap.proj i
  res_comp_ext i := LinearMap.ext fun x => by simp
  res_op_ext_res L hv := LinearMap.ext fun F => by
    simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.coe_proj,
      Function.eval, LinearMap.single_apply]
    rw [hκ L hv, Pi.single_eq_same]

/-- The product of the component operators of a list of layers at index `i`; the first
(bottom) layer acts first.-/
def piList (i : ι) : List (Layer S) → Module.End R (M i)
  | [] => 1
  | L :: ls => piList i ls * A L i

/--
@isnad1 id=eq.0h6v.s7.f522c07796e9 from=translated src=- shape=b47fcf1e vocab=5c92ea25
-/
@[simp] theorem piList_nil (i : ι) : piList A i [] = 1 := rfl

/--
@isnad1 id=eq.0h8v.s7.403c0d8171c6 from=translated src=- shape=16802dac vocab=1b2d4db8
-/
@[simp] theorem piList_cons (i : ι) (L : Layer S) (ls : List (Layer S)) :
    piList A i (L :: ls) = piList A i ls * A L i := rfl

/-- A single layer: no trailing `1 *`.
@isnad1 id=eq.0h7v.s6.b632afd3eed4 from=translated src=- shape=94702d56 vocab=7798de32
-/
@[simp 1100] theorem piList_singleton (i : ι) (L : Layer S) : piList A i [L] = A L i :=
  one_mul _

variable {κ A hκ}

/--
@isnad1 id=eq.1h9v.s8.27d0479fbab4 from=translated src=- shape=ef963aae vocab=846cf236
-/
@[simp] theorem pi_op_apply (L : Layer S) (F : ∀ i, M i) (i : ι) :
    (pi κ A hκ).op L F i = A L i (F i) := rfl

/--
@isnad1 id=eq.1h8v.s8.677e7b7553b0 from=translated src=- shape=5592aacd vocab=8b9fb7b2
-/
@[simp] theorem pi_res_apply (i : ι) (F : ∀ i, M i) : (pi κ A hκ).res i F = F i := rfl

open Classical in
/--
@isnad1 id=eq.1h8v.s8.2eaad1519288 from=translated src=- shape=92a04dc2 vocab=944a46d0
-/
@[simp] theorem pi_ext_apply (i : ι) (x : M i) : (pi κ A hκ).ext i x = Pi.single i x := rfl

/--
@isnad1 id=eq.1h9v.s8.fec5f317a052 from=translated src=- shape=7e3fb7b3 vocab=6198571a
-/
theorem pi_opList_apply (ls : List (Layer S)) (F : ∀ i, M i) (i : ι) :
    (pi κ A hκ).opList ls F i = piList A i ls (F i) := by
  induction ls generalizing F with
  | nil => rfl
  | cons L ls ih => simp [ih, Module.End.mul_apply]

/-- Evaluation of a list of layers between the same index is the product of the component
operators.
@isnad1 id=eq.1h8v.s9.4e2930212391 from=translated src=- shape=b0469971 vocab=4a85112c
-/
theorem pi_res_opList_ext (i : ι) (ls : List (Layer S)) :
    (pi κ A hκ).res i ∘ₗ (pi κ A hκ).opList ls ∘ₗ (pi κ A hκ).ext i = piList A i ls := by
  classical
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, pi_res_apply, pi_opList_apply]
  congr 1
  exact Pi.single_eq_same (M := M) i x

set_option backward.isDefEq.respectTransparency false in
/-- The image of a diagram between objects of index `i`, transported to `M i`, is the product
of the component operators of its layers.
@isnad1 id=eq.3h10v.s9.da62c112c2f6 from=translated src=- shape=f0709cf0 vocab=6ebe6c7a
-/
theorem pi_functor_map_transport {a b : Obj S} {i : ι} (f : a ⟶ b) (ha : κ a = i)
    (hb : κ b = i) :
    eqToHom (congrArg (mod (M := M)) ha.symm) ≫ (pi κ A hκ).functor.map f ≫
        eqToHom (congrArg (mod (M := M)) hb) =
      ModuleCat.ofHom (piList A i (Diagram.layers f)) := by
  rw [(pi κ A hκ).functor_map_transport f ha hb, pi_res_opList_ext]

/-- Whiskered evaluation between the same index `i`, for index-preserving componentwise
operators.
@isnad1 id=eq.1h12v.s9.9f6414447d36 from=translated src=- shape=bf823df8 vocab=d965f6d7
-/
theorem pi_evalW_of (i : ι) (u : Obj S) (v : List S.Colour) {a b : Obj S} (d : a ⟶ b) :
    (pi κ A hκ).evalW i i u v (LinDiagram.of d : LinDiagram R a b) =
      piList A i ((Diagram.layers d).map (·.whisker u v)) := by
  rw [evalW_of, pi_res_opList_ext]

end Pi

end LocalInterpretation

/-! ## Functors to modules, pointwise -/

section ModuleFunctor

variable {S : Signature.{u₀, u₁, u₂}} {R : Type w} [CommRing R]

end ModuleFunctor

/-! ## Integer coefficients -/

namespace Presentation

variable {S : Signature.{u₀, u₁, u₂}} {a b : Obj S}

/-- Over `R = ℤ`, the scalar multiplication of the linear structure `instLinear` of a
presented category is `zsmul`. The left-hand side is the scalar multiplication occurring in
`Presentation.hom_induction` for `R = ℤ`.
@isnad1 id=eq.0h6v.s11.9a15443e1a72 from=translated src=- shape=ed57bd2d vocab=1dfa1e73
-/
theorem int_smul_eq_zsmul (P : Presentation S ℤ) (n : ℤ) (f : P.obj a ⟶ P.obj b) :
    @HSMul.hSMul ℤ _ _ (@instHSMul _ _ (@SMulZeroClass.toSMul _ _ _
      (@DistribSMul.toSMulZeroClass _ _ _ (@DistribMulAction.toDistribSMul _ _ _ _
        (@Module.toDistribMulAction _ _ _ _ (P.instLinear.homModule (P.obj a) (P.obj b)))))))
      n f = n • f :=
  _root_.int_smul_eq_zsmul (P.instLinear.homModule (P.obj a) (P.obj b)) n f

/-- Induction on morphisms of a presented category over `ℤ`: classes of diagrams, zero, sums
and negatives.
@isnad1 id=var.0h10v.s10.2413d51d970d from=translated src=- shape=2e592842 vocab=33875259
-/
theorem hom_induction_int (P : Presentation S ℤ) {p : (P.obj a ⟶ P.obj b) → Prop}
    (diag : ∀ d : a ⟶ b, p (P.diag d)) (zero : p 0) (add : ∀ f g, p f → p g → p (f + g))
    (neg : ∀ f, p f → p (-f)) (f : P.obj a ⟶ P.obj b) : p f := by
  refine P.hom_induction diag zero add (fun n g hg => ?_) f
  rw [P.int_smul_eq_zsmul]
  have hn : ∀ k : ℕ, p ((k : ℤ) • g) := by
    intro k
    induction k with
    | zero => rw [Nat.cast_zero, zero_smul]; exact zero
    | succ k ih => rw [Nat.cast_succ, add_smul, one_smul]; exact add _ _ ih hg
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · exact hn k
  · rw [neg_smul]; exact neg _ (hn k)

end Presentation

end StringDiagrams

end
