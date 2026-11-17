import Tengoku.StringDiagramsLean.StringDiagrams.Signature
import Tengoku.Seed.CategoryTheory.EqToHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The free 2-category on a signature

Morphisms of the free (strict) 2-category on a signature `S` are *layered diagrams*: finite
lists of well-formed layers `id_left ⊗ g ⊗ id_right`, composed by concatenation. The
morphism type `a ⟶ b` is the subtype of layer lists that form a chain from `a` to `b`
(`Chain a ls b`). Typing information is carried by proofs only, so a morphism is
determined by its list of layers (`Diagram.ext`) and changing the type along an equality
of objects never changes the underlying data (`Diagram.layers_eqToHom`). This is what makes
diagrams of symbolic width (for example `n` strands with `n` a variable) convenient.

Objects are not required to be well formed: `Chain a [] b` is just `a = b`, so every object,
including a word whose regions do not match up, has an identity. Only layers are checked
(`Layer.Valid`), so no diagram with at least one layer has an ill-formed boundary, and no
relation is ever applied at an ill-formed object; identities of ill-formed objects are inert.

No relations are imposed here, not even the interchange law; interchange is imposed
together with the defining relations of a presentation (see
`StringDiagrams.Presentation`), where the Koszul sign of a super interchange law can be
included.

## Main definitions

* `StringDiagrams.Chain a ls b`: the layers `ls` form a well-typed diagram from `a` to `b`.
* `CategoryTheory.Category (Obj S)`: the free 2-category, with `a ⟶ b` the well-typed
  layer lists.
* `StringDiagrams.Diagram.ofLayer`: a single layer as a morphism.
* `StringDiagrams.Diagram.whisker`: whiskering `u ⊗ f ⊗ v` of a diagram.
-/

namespace StringDiagrams

open CategoryTheory

universe u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}}

/-- The layers `ls` form a well-typed diagram from `a` (bottom) to `b` (top).-/
def Chain : Obj S → List (Layer S) → Obj S → Prop
  | a, [], b => a = b
  | a, L :: ls, b => L.Valid ∧ L.dom = a ∧ Chain L.cod ls b

/--
@isnad1 id=iff.0h3v.s4.1282a0fed568 from=translated src=- shape=a0948acf vocab=4e55641a
-/
@[simp] theorem chain_nil (a b : Obj S) : Chain a [] b ↔ a = b := Iff.rfl

/--
@isnad1 id=iff.0h5v.s5.cd7c3de9e8b4 from=translated src=- shape=c99c260f vocab=250c3fa2
-/
@[simp] theorem chain_cons (a b : Obj S) (L : Layer S) (ls : List (Layer S)) :
    Chain a (L :: ls) b ↔ L.Valid ∧ L.dom = a ∧ Chain L.cod ls b := Iff.rfl

/--
@isnad1 id=chain.2h6v.s5.9f9329d20610 from=translated src=- shape=b6104e6e vocab=b1210c6d
-/
theorem Chain.append {a b c : Obj S} {ls ms : List (Layer S)} (h₁ : Chain a ls b)
    (h₂ : Chain b ms c) : Chain a (ls ++ ms) c := by
  induction ls generalizing a with
  | nil => cases h₁; exact h₂
  | cons L ls ih => exact ⟨h₁.1, h₁.2.1, ih h₁.2.2⟩

/--
@isnad1 id=eq.1h4v.s4.8ecb67592003 from=translated src=- shape=7ab3af88 vocab=e6019ac9
-/
theorem Chain.start_eq {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b) :
    b.start = a.start := by
  induction ls generalizing a with
  | nil => cases h; rfl
  | cons L ls ih => rw [ih h.2.2, ← h.2.1]; rfl

/--
@isnad1 id=eq.1h4v.s4.c2337bebc221 from=translated src=- shape=7ab3af88 vocab=14259da5
-/
theorem Chain.endR_eq {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b) :
    b.endR = a.endR := by
  induction ls generalizing a with
  | nil => cases h; rfl
  | cons L ls ih => rw [ih h.2.2, h.1.endR_eq, h.2.1]

/--
@isnad1 id=whiskero.2h6v.s5.a62a28803082 from=translated src=- shape=7bc46389 vocab=e464794e
-/
theorem Chain.whiskerOK {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b)
    {u : Obj S} {v : List S.Colour} (hw : a.WhiskerOK u v) : b.WhiskerOK u v :=
  ⟨hw.1, by rw [h.start_eq]; exact hw.2.1, by rw [h.endR_eq]; exact hw.2.2⟩

/--
@isnad1 id=chain.2h6v.s5.c01c6ad5fa57 from=translated src=- shape=c16225fd vocab=ebdf4acd
-/
theorem Chain.whisker {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b)
    {u : Obj S} {v : List S.Colour} (hw : a.WhiskerOK u v) :
    Chain (a.whisker u v) (ls.map (·.whisker u v)) (b.whisker u v) := by
  induction ls generalizing a with
  | nil => cases h; rfl
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    rw [List.map_cons, chain_cons, Layer.whisker_dom, Layer.whisker_cod]
    have hw' : L.cod.WhiskerOK u v := Chain.whiskerOK (ls := [L]) ⟨hv, rfl, rfl⟩ hw
    exact ⟨hv.whisker hw, rfl, ih hc hw'⟩

/-! ## Decidability of well-typedness -/

section Decidable

instance decChain [DecidableEq S.Region] [DecidableEq S.Colour] :
    (a : Obj S) → (ls : List (Layer S)) → (b : Obj S) → Decidable (Chain a ls b)
  | a, [], b => decidable_of_iff (a = b) (chain_nil a b).symm
  | a, L :: ls, b =>
    have := decChain L.cod ls b
    decidable_of_iff _ (chain_cons a b L ls).symm

/-- The top boundary of a layer list read from the bottom boundary `a`: the codomain of its
last layer, or `a` if there are no layers.-/
def Chain.target (a : Obj S) : List (Layer S) → Obj S
  | [] => a
  | L :: ls => Chain.target L.cod ls

/--
@isnad1 id=eq.1h4v.s4.45a7d630cc2d from=translated src=- shape=d863c579 vocab=21c1be90
-/
theorem Chain.target_eq {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b) :
    Chain.target a ls = b := by
  induction ls generalizing a with
  | nil => exact h
  | cons L ls ih => exact ih h.2.2

/--
@isnad1 id=eq.0h4v.s5.6faeb1bb23f0 from=translated src=- shape=9fbdc34f vocab=0329554a
-/
@[simp] theorem Chain.target_append_singleton (a : Obj S) (ls : List (Layer S)) (L : Layer S) :
    Chain.target a (ls ++ [L]) = L.cod := by
  induction ls generalizing a with
  | nil => rfl
  | cons L' ls ih => exact ih _

end Decidable

/-- A diagram from `a` to `b` in the free 2-category: a well-typed list of layers.-/
abbrev Diagram (a b : Obj S) : Type (max u₀ u₁ u₂) := {ls : List (Layer S) // Chain a ls b}

instance : Category (Obj S) where
  Hom := Diagram
  id _ := ⟨[], rfl⟩
  comp f g := ⟨f.1 ++ g.1, f.2.append g.2⟩
  id_comp _ := Subtype.ext (List.nil_append _)
  comp_id _ := Subtype.ext (List.append_nil _)
  assoc _ _ _ := Subtype.ext (List.append_assoc _ _ _)

namespace Diagram

variable {a b c : Obj S}

/-- The list of layers of a diagram, from bottom to top.-/
def layers (f : a ⟶ b) : List (Layer S) := f.1

/--
@isnad1 id=chain.0h4v.s4.55c39f802136 from=translated src=- shape=3ea79c58 vocab=d95e705d
-/
theorem chain (f : a ⟶ b) : Chain a (layers f) b := f.2

/-- Build a diagram from a list of layers and a typing proof.-/
def mk (ls : List (Layer S)) (h : Chain a ls b) : a ⟶ b := ⟨ls, h⟩

/--
@isnad1 id=eq.1h4v.s5.4a0781a88053 from=translated src=- shape=587f9f2a vocab=121cfb68
-/
@[simp] theorem layers_mk (ls : List (Layer S)) (h : Chain a ls b) :
    layers (mk ls h) = ls := rfl

/--
@isnad1 id=eq.1h5v.s6.e108c79390d9 from=translated src=- shape=b0a61dcd vocab=845f6d1f
-/
@[ext] theorem ext {f g : a ⟶ b} (h : layers f = layers g) : f = g := Subtype.ext h

/--
@isnad1 id=eq.0h2v.s4.1b97f44d151c from=translated src=- shape=a3e32963 vocab=90412340
-/
@[simp] theorem layers_id (a : Obj S) : layers (𝟙 a) = [] := rfl

/--
@isnad1 id=eq.0h6v.s6.efebd22a3020 from=translated src=- shape=ca97e224 vocab=fe407910
-/
@[simp] theorem layers_comp (f : a ⟶ b) (g : b ⟶ c) : layers (f ≫ g) = layers f ++ layers g :=
  rfl

/--
@isnad1 id=eq.1h3v.s5.d96834181cae from=translated src=- shape=7961f612 vocab=f109a92f
-/
@[simp] theorem layers_eqToHom (h : a = b) : layers (eqToHom h) = [] := by
  subst h; rfl

/-- A single well-formed layer as a diagram.-/
def ofLayer (L : Layer S) (hv : L.Valid) : L.dom ⟶ L.cod := ⟨[L], hv, rfl, rfl⟩

/--
@isnad1 id=eq.1h2v.s5.9a29348a8ead from=translated src=- shape=38812287 vocab=ca991057
-/
@[simp] theorem layers_ofLayer (L : Layer S) (hv : L.Valid) : layers (ofLayer L hv) = [L] :=
  rfl

/-- A single well-formed layer as a diagram between objects equal to its boundaries.-/
def layer (L : Layer S) (hv : L.Valid) (ha : L.dom = a) (hb : L.cod = b) : a ⟶ b :=
  ⟨[L], hv, ha, hb⟩

/--
@isnad1 id=eq.3h4v.s5.a2f7f019e61a from=translated src=- shape=cf1521e5 vocab=15fe3f72
-/
@[simp] theorem layers_layer (L : Layer S) (hv : L.Valid) (ha : L.dom = a) (hb : L.cod = b) :
    layers (layer L hv ha hb) = [L] := rfl

/-- Retype a diagram along equalities of its boundary objects; the layers are unchanged.-/
def cast {a' b' : Obj S} (f : a ⟶ b) (ha : a = a') (hb : b = b') : a' ⟶ b' :=
  mk (layers f) (ha ▸ hb ▸ chain f)

/--
@isnad1 id=eq.2h6v.s5.a6e3ba0d1edd from=translated src=- shape=16e3d8de vocab=90c2ea6f
-/
@[simp] theorem layers_cast {a' b' : Obj S} (f : a ⟶ b) (ha : a = a') (hb : b = b') :
    layers (cast f ha hb) = layers f := rfl

/--
@isnad1 id=eq.2h6v.s6.e81f12e83955 from=translated src=- shape=06548724 vocab=a2d8654b
-/
theorem cast_eq {a' b' : Obj S} (f : a ⟶ b) (ha : a = a') (hb : b = b') :
    cast f ha hb = eqToHom ha.symm ≫ f ≫ eqToHom hb := by
  ext; simp

/--
@isnad1 id=eq.0h4v.s5.43a0166da077 from=translated src=- shape=628ff701 vocab=3c7d2a13
-/
@[simp] theorem cast_rfl (f : a ⟶ b) : cast f rfl rfl = f := rfl

/--
@isnad1 id=eq.4h8v.s6.12e0f0b2c040 from=translated src=- shape=f28b4285 vocab=7ae65a10
-/
@[simp] theorem cast_cast {a' b' a'' b'' : Obj S} (f : a ⟶ b) (ha : a = a') (hb : b = b')
    (ha' : a' = a'') (hb' : b' = b'') :
    cast (cast f ha hb) ha' hb' = cast f (ha.trans ha') (hb.trans hb') := rfl

/--
@isnad1 id=eq.3h9v.s7.639be73053bf from=translated src=- shape=42ebc3ae vocab=6792b899
-/
theorem cast_comp {a' b' c' : Obj S} (f : a ⟶ b) (g : b ⟶ c) (ha : a = a') (hb : b = b')
    (hc : c = c') : cast (f ≫ g) ha hc = cast f ha hb ≫ cast g hb hc := rfl

/--
@isnad1 id=eq.2h4v.s6.86538274da54 from=translated src=- shape=5d94a363 vocab=2c301c85
-/
@[simp] theorem cast_id {a' a'' : Obj S} (ha : a = a') (ha' : a = a'') :
    cast (𝟙 a) ha' ha = eqToHom (ha'.symm.trans ha) := by
  ext; simp

/-- Two diagrams with the same layers agree up to retyping.-/
theorem eq_cast_of_layers_eq {a' b' : Obj S} {f : a ⟶ b} {g : a' ⟶ b'} (ha : a' = a)
    (hb : b' = b) (h : layers f = layers g) : f = cast g ha hb :=
  Diagram.ext h

/-- The source of a diagram is the source of its first layer.-/
theorem eq_dom_of_layers_eq_cons (f : a ⟶ b) {L : Layer S} {ls : List (Layer S)}
    (h : layers f = L :: ls) : a = L.dom := by
  have := chain f
  rw [h] at this
  exact this.2.1.symm

/-- The target of a diagram is the target of its last layer.-/
theorem eq_cod_of_layers_eq_append (f : a ⟶ b) {L : Layer S} {ls : List (Layer S)}
    (h : layers f = ls ++ [L]) : b = L.cod := by
  have := (chain f).target_eq
  rw [h, Chain.target_append_singleton] at this
  exact this.symm

/-- The boundaries of a diagram with one layer.-/
theorem eq_of_layers_eq_singleton (f : a ⟶ b) {L : Layer S} (h : layers f = [L]) :
    a = L.dom ∧ b = L.cod :=
  ⟨eq_dom_of_layers_eq_cons f h, eq_cod_of_layers_eq_append (ls := []) f h⟩

/-- The boundaries of a diagram with two layers.-/
theorem eq_of_layers_eq_pair (f : a ⟶ b) {L₁ L₂ : Layer S} (h : layers f = [L₁, L₂]) :
    a = L₁.dom ∧ L₁.cod = L₂.dom ∧ b = L₂.cod := by
  have := chain f
  rw [h] at this
  exact ⟨this.2.1.symm, this.2.2.2.1.symm, this.2.2.2.2.symm⟩

/-- The boundaries of a diagram with three layers.-/
theorem eq_of_layers_eq_triple (f : a ⟶ b) {L₁ L₂ L₃ : Layer S} (h : layers f = [L₁, L₂, L₃]) :
    a = L₁.dom ∧ L₁.cod = L₂.dom ∧ L₂.cod = L₃.dom ∧ b = L₃.cod := by
  have := chain f
  rw [h] at this
  exact ⟨this.2.1.symm, this.2.2.2.1.symm, this.2.2.2.2.2.1.symm, this.2.2.2.2.2.2.symm⟩

/-- Whiskering `u ⊗ f ⊗ v` of a diagram.-/
def whisker (f : a ⟶ b) (u : Obj S) (v : List S.Colour) (hw : a.WhiskerOK u v) :
    a.whisker u v ⟶ b.whisker u v :=
  ⟨(layers f).map (·.whisker u v), (chain f).whisker hw⟩

/--
@isnad1 id=eq.1h6v.s6.62309b416283 from=translated src=- shape=9a2dcc28 vocab=1991e829
-/
@[simp] theorem layers_whisker (f : a ⟶ b) (u : Obj S) (v : List S.Colour)
    (hw : a.WhiskerOK u v) : layers (whisker f u v hw) = (layers f).map (·.whisker u v) := rfl

/--
@isnad1 id=eq.1h4v.s6.ceb131faadee from=translated src=- shape=02648458 vocab=2e57dde6
-/
theorem whisker_id (u : Obj S) (v : List S.Colour) (hw : a.WhiskerOK u v) :
    whisker (𝟙 a) u v hw = 𝟙 _ := rfl

/--
@isnad1 id=eq.1h8v.s7.cb62580ea5bf from=translated src=- shape=4c6814f8 vocab=652aa11f
-/
theorem whisker_comp (f : a ⟶ b) (g : b ⟶ c) (u : Obj S) (v : List S.Colour)
    (hw : a.WhiskerOK u v) :
    whisker (f ≫ g) u v hw = whisker f u v hw ≫ whisker g u v ((chain f).whiskerOK hw) := by
  ext; simp

end Diagram

end StringDiagrams
