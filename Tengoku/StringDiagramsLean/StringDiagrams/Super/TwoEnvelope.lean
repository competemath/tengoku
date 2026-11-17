import Tengoku.StringDiagramsLean.StringDiagrams.Super.Bicategory
import Tengoku.StringDiagramsLean.StringDiagrams.Super.MonoidalEnvelope

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Π-envelope of a 2-supercategory

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 4.4 and Lemmas 4.5–4.6.

The Π-envelope `𝔄_π` of a 2-supercategory `𝔄` (`StringDiagrams.TwoEnvelope R B`) has the same
objects as `𝔄`, and its morphism supercategories are the Π-envelopes of those of `𝔄`: the
1-morphisms `λ → μ` are the `Πᵃ F` for `F : λ → μ` in `𝔄` and `a ∈ ℤ/2`, and
`Hom(Πᵃ F, Πᵇ G) := Π^{a+b} Hom_𝔄(F, G)`, the 2-morphism `x_a^b : Πᵃ F ⇒ Πᵇ G` coming from a
homogeneous `x : F ⇒ G` having parity `|x| + a + b`; vertical composition is (4.3),
`y_b^c ∘ x_a^b = (y ∘ x)_a^c`. In Lean the hom categories are literally
`Envelope R (a ⟶ b)`.

Horizontal composition of 1-morphisms is `(Πᵇ G)(Πᵃ F) := Π^{a+b}(GF)`, and of 2-morphisms is
(4.4): for `x : Πᵃ F ⇒ Πᶜ H` and `y : Πᵇ G ⇒ Πᵈ K`,

  `y_b^d x_a^c := (-1)^{b|x| + |y|c + bc + ab} (yx)_{a+b}^{c+d}`.

With 1-morphisms composed in diagrammatic order (`F ≫ G` is the paper's `GF`) and the
whiskering presentation of `StringDiagrams.TwoSupercategory`, (4.4) amounts to

* `Πᵃ F ◁ y = (-1)^{a|y|} (F ◁ y)` (the paper's `y (1_F)_a^a`), and
* `x ▷ Πᵇ G = (-1)^{b(|x| + a + c)} (x ▷ G)` (the paper's `(1_G)_b^b x`),

(`toHom_whiskerLeft_of_mem`, `toHom_whiskerRight_of_mem`), and the paper's formula (4.4) for
the horizontal composite is `TwoEnvelope.toHom_hcomp`. The coherence maps are those of `𝔄`.

The units are `𝟙_λ = Π⁰ 𝟙_λ`, and the Π-structure is `π_λ := Π¹ 𝟙_λ` with the odd 2-isomorphism
`ζ_λ := (1_{𝟙_λ})_1^0 : π_λ ⇒ 𝟙_λ`; `ξ_λ := ζ_λ ζ_λ` is minus the identity (`toHom_ξ`).

## Main statements

* `TwoEnvelope R B`, with its `BicategoryStruct` and hom-category instances, and
  `TwoEnvelope.twoSupercategory`: **Definition 4.4** and **Lemma 4.5** (the compositions (4.3)
  and (4.4) satisfy the super interchange law, in the paper's formulation
  `TwoEnvelope.toHom_super_interchange`).
* `TwoEnvelope.toHom_hcomp`: the sign formula (4.4).
* `TwoEnvelope.π`, `TwoEnvelope.ζ`, `TwoEnvelope.ζ_hom_mem`, `TwoEnvelope.toHom_ξ`: the
  Π-structure of Definition 4.4.
* `TwoEnvelope.associator_sign_eq`: the two expressions for `(z_c^f y_b^e) x_a^d` and
  `z_c^f (y_b^e x_a^d)` displayed in Definition 4.4 carry the same sign.
* `TwoEnvelope.PiComplete`, `TwoEnvelope.superequivalenceJ_iff` (**Lemma 4.6**): the canonical
  `𝕁 : 𝔄 → 𝔄_π` (identity on objects, `Envelope.J` on each morphism supercategory) induces
  superequivalences on all morphism supercategories if and only if `𝔄` is Π-complete, i.e.
  each `𝟙_λ` is the target of an odd 2-isomorphism.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct

universe w w₁ v u

/-- The objects of the Π-envelope of a 2-supercategory `B` (Brundan–Ellis, Definition 4.4):
the objects of `B`.-/
@[ext]
structure TwoEnvelope (R : Type w₁) (B : Type u) where
  /-- The underlying object.-/
  as : B

namespace TwoEnvelope

variable {R : Type w₁} {B : Type u} [BicategoryStruct.{w, v} B]

section Struct

variable [CommRing R] [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)]

/-- **Definition 4.4.** The bicategory data of the Π-envelope: 1-morphisms `a ⟶ b` are the
objects `Πᵃ F` of `Envelope R (a ⟶ b)`, `(Πᵃ F) ≫ (Πᵇ G) := Π^{a+b}(F ≫ G)`, units `Π⁰ 𝟙`,
whiskerings given by (4.4) and coherence maps those of `B`.-/
instance instBicategoryStruct : BicategoryStruct.{w, v} (TwoEnvelope R B) where
  Hom a b := Envelope R (a.as ⟶ b.as)
  id a := ⟨0, 𝟙 a.as⟩
  comp f g := ⟨f.par + g.par, f.obj ≫ g.obj⟩
  homCategory a b := inferInstanceAs (Category (Envelope R (a.as ⟶ b.as)))
  whiskerLeft f _ _ η := Envelope.ofHom (f.obj ◁ twist R f.par (Envelope.toHom η))
  whiskerRight {_ _ _ _ _} η h := Envelope.ofHom (Envelope.toHom (twist R h.par η) ▷ h.obj)
  associator f g h := Envelope.isoOfIso (associator f.obj g.obj h.obj)
  leftUnitor f := Envelope.isoOfIso (leftUnitor f.obj)
  rightUnitor f := Envelope.isoOfIso (rightUnitor f.obj)

instance (a b : TwoEnvelope R B) : Preadditive (a ⟶ b) :=
  inferInstanceAs (Preadditive (Envelope R (a.as ⟶ b.as)))

instance (a b : TwoEnvelope R B) : Linear R (a ⟶ b) :=
  inferInstanceAs (Linear R (Envelope R (a.as ⟶ b.as)))

instance (a b : TwoEnvelope R B) : Supercategory R (a ⟶ b) :=
  inferInstanceAs (Supercategory R (Envelope R (a.as ⟶ b.as)))

instance (a b : TwoEnvelope R B) : PiSupercategory R (a ⟶ b) :=
  inferInstanceAs (PiSupercategory R (Envelope R (a.as ⟶ b.as)))

open Envelope

variable {a b c d : TwoEnvelope R B}

/--
@isnad1 id=eq.0h7v.s8.1aa1753752ae from=translated src=- shape=377b9cfd vocab=3f94f052
-/
@[simp] theorem comp_par (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).par = f.par + g.par := rfl

/--
@isnad1 id=eq.0h7v.s7.f115ee4f2342 from=translated src=- shape=f13667c8 vocab=62d6e63b
-/
@[simp] theorem comp_obj (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).obj = f.obj ≫ g.obj := rfl

/--
@isnad1 id=eq.0h3v.s7.bb0b1d9cf6b2 from=translated src=- shape=935c8d78 vocab=4149b288
-/
@[simp] theorem id_par (a : TwoEnvelope R B) : (𝟙 a : a ⟶ a).par = 0 := rfl

/--
@isnad1 id=eq.0h3v.s7.284436739642 from=translated src=- shape=d2477159 vocab=a210a8e1
-/
@[simp] theorem id_obj (a : TwoEnvelope R B) : (𝟙 a : a ⟶ a).obj = 𝟙 a.as := rfl

/--
@isnad1 id=eq.0h9v.s11.e1cd2f9c2f11 from=translated src=- shape=39a5a777 vocab=cc34796f
-/
theorem toHom_whiskerLeft (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    toHom (f ◁ η) = f.obj ◁ twist R f.par (toHom η) := rfl

/--
@isnad1 id=eq.0h9v.s11.f0ee5db4f174 from=translated src=- shape=43b65de0 vocab=2eb4a463
-/
theorem toHom_whiskerRight {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    toHom (η ▷ h) = toHom (twist R h.par η) ▷ h.obj := rfl

/--
@isnad1 id=eq.0h9v.s9.e68b83830d58 from=translated src=- shape=0d309cc4 vocab=cc2f243b
-/
@[simp] theorem toHom_associator_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    toHom (associator f g h).hom = (associator f.obj g.obj h.obj).hom := rfl

/--
@isnad1 id=eq.0h9v.s9.5c8dbb7a1f6a from=translated src=- shape=b489560a vocab=72c73909
-/
@[simp] theorem toHom_associator_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    toHom (associator f g h).inv = (associator f.obj g.obj h.obj).inv := rfl

/--
@isnad1 id=eq.0h5v.s9.c73888dd372b from=translated src=- shape=6e198c85 vocab=e9f928b3
-/
@[simp] theorem toHom_leftUnitor_hom (f : a ⟶ b) :
    toHom (leftUnitor f).hom = (leftUnitor f.obj).hom := rfl

/--
@isnad1 id=eq.0h5v.s9.c55aae724f76 from=translated src=- shape=b6e12cbe vocab=eb96fea1
-/
@[simp] theorem toHom_leftUnitor_inv (f : a ⟶ b) :
    toHom (leftUnitor f).inv = (leftUnitor f.obj).inv := rfl

/--
@isnad1 id=eq.0h5v.s9.27e559613e8b from=translated src=- shape=8da12cc0 vocab=b616b89a
-/
@[simp] theorem toHom_rightUnitor_hom (f : a ⟶ b) :
    toHom (rightUnitor f).hom = (rightUnitor f.obj).hom := rfl

/--
@isnad1 id=eq.0h5v.s9.0d2a3283460f from=translated src=- shape=405d3edd vocab=660da6b4
-/
@[simp] theorem toHom_rightUnitor_inv (f : a ⟶ b) :
    toHom (rightUnitor f).inv = (rightUnitor f.obj).inv := rfl

end Struct

/-! ## Lemma 4.5: the Π-envelope is a 2-supercategory -/

section Axioms

variable [CommRing R] [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

open Envelope TwoSupercategory

variable {a b c d e : TwoEnvelope R B}

/-- `Πᵃ F ◁ y = (-1)^{a|y|} (F ◁ y)` for `y` of parity `r` in `B`.
@isnad1 id=eq.1h10v.s12.59e289fb0c5b from=translated src=- shape=50a934bd vocab=761be919
-/
theorem toHom_whiskerLeft_of_mem (f : a ⟶ b) {g h : b ⟶ c} {η : g ⟶ h} {r : ZMod 2}
    (hη : toHom η ∈ parity (R := R) g.obj h.obj r) :
    toHom (f ◁ η) = sign R (f.par * r) • (f.obj ◁ toHom η) := by
  rw [toHom_whiskerLeft, twist_of_mem _ hη, TwoSupercategory.whiskerLeft_smul]

/-- `x ▷ Πᵇ G = (-1)^{b(|x| + a + c)} (x ▷ G)` for `x : Πᵃ F ⇒ Πᶜ H` of parity `r` in `B`.
@isnad1 id=eq.1h10v.s12.de3594ee319d from=translated src=- shape=d00802a3 vocab=0d39af4a
-/
theorem toHom_whiskerRight_of_mem {f g : a ⟶ b} {η : f ⟶ g} {r : ZMod 2}
    (hη : toHom η ∈ parity (R := R) f.obj g.obj r) (h : b ⟶ c) :
    toHom (η ▷ h) = sign R (h.par * (r + (f.par + g.par))) • (toHom η ▷ h.obj) := by
  rw [toHom_whiskerRight, toHom_twist, twist_of_mem _ hη, smul_smul, ← sign_add,
    TwoSupercategory.smul_whiskerRight]
  congr 2
  ring

/--
@isnad1 id=mem.1h10v.s12.95ecdd22c503 from=translated src=- shape=682aee0a vocab=75fb7aa5
-/
theorem toHom_whiskerLeft_mem (f : a ⟶ b) {g h : b ⟶ c} {η : g ⟶ h} {r : ZMod 2}
    (hη : toHom η ∈ parity (R := R) g.obj h.obj r) :
    toHom (f ◁ η) ∈ parity (R := R) (f.obj ≫ g.obj) (f.obj ≫ h.obj) r := by
  rw [toHom_whiskerLeft_of_mem f hη]
  exact Submodule.smul_mem _ _ (TwoSupercategory.whiskerLeft_mem _ hη)

/--
@isnad1 id=mem.1h10v.s12.f5e9c0681d91 from=translated src=- shape=c323aa12 vocab=a833e4df
-/
theorem toHom_whiskerRight_mem {f g : a ⟶ b} {η : f ⟶ g} {r : ZMod 2}
    (hη : toHom η ∈ parity (R := R) f.obj g.obj r) (h : b ⟶ c) :
    toHom (η ▷ h) ∈ parity (R := R) (f.obj ≫ h.obj) (g.obj ≫ h.obj) r := by
  rw [toHom_whiskerRight_of_mem hη]
  exact Submodule.smul_mem _ _ (TwoSupercategory.whiskerRight_mem _ hη)

omit [TwoSupercategory R B] in
/--
@isnad1 id=eq.1h9v.s9.1f789cd5952b from=translated src=- shape=870ef4d1 vocab=cccad58d
-/
theorem toHom_whiskerLeft_of_par_zero (f : a ⟶ b) (hf : f.par = 0) {g h : b ⟶ c}
    (η : g ⟶ h) : toHom (f ◁ η) = f.obj ◁ toHom η := by
  rw [toHom_whiskerLeft, hf, twist_zero]

omit [TwoSupercategory R B] in
/--
@isnad1 id=eq.1h9v.s9.6ff3c5a4446d from=translated src=- shape=5c29f62a vocab=cc4465d4
-/
theorem toHom_whiskerRight_of_par_zero {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) (hh : h.par = 0) :
    toHom (η ▷ h) = toHom η ▷ h.obj := by
  rw [toHom_whiskerRight, hh, twist_zero]

/--
@isnad1 id=eq.1h9v.s10.76333629d0b0 from=translated src=- shape=e26503ef vocab=75fb7aa5
-/
theorem toHom_whiskerLeft_of_even (f : a ⟶ b) {g h : b ⟶ c} {η : g ⟶ h}
    (hη : toHom η ∈ parity (R := R) g.obj h.obj 0) : toHom (f ◁ η) = f.obj ◁ toHom η := by
  rw [toHom_whiskerLeft_of_mem f hη, mul_zero, sign_zero, one_smul]

/--
@isnad1 id=eq.2h9v.s11.e03fd34d15ce from=translated src=- shape=f9e68537 vocab=ee21a0fd
-/
theorem toHom_whiskerRight_of_even {f g : a ⟶ b} {η : f ⟶ g}
    (hη : toHom η ∈ parity (R := R) f.obj g.obj 0) (h : b ⟶ c) (hfg : f.par = g.par) :
    toHom (η ▷ h) = toHom η ▷ h.obj := by
  rw [toHom_whiskerRight_of_mem hη, hfg, zmod2_add_self, add_zero, mul_zero, sign_zero,
    one_smul]

/--
@isnad1 id=eq.0h10v.s11.b85850ab1a76 from=translated src=- shape=469b62cd vocab=a011d3c7
-/
theorem whiskerLeft_add' (f : a ⟶ b) {g h : b ⟶ c} (η θ : g ⟶ h) :
    f ◁ (η + θ) = f ◁ η + f ◁ θ := by
  apply hom_ext
  rw [toHom_add, toHom_whiskerLeft, toHom_whiskerLeft, toHom_whiskerLeft, toHom_add, map_add,
    TwoSupercategory.whiskerLeft_add (R := R)]

/--
@isnad1 id=eq.0h10v.s11.53a1f79902e6 from=translated src=- shape=97e81f5e vocab=52722e48
-/
theorem add_whiskerRight' {f g : a ⟶ b} (η θ : f ⟶ g) (h : b ⟶ c) :
    (η + θ) ▷ h = η ▷ h + θ ▷ h := by
  apply hom_ext
  rw [toHom_add, toHom_whiskerRight, toHom_whiskerRight, toHom_whiskerRight, map_add, toHom_add,
    TwoSupercategory.add_whiskerRight (R := R)]

/--
@isnad1 id=eq.0h8v.s9.f316692f315d from=translated src=- shape=dd44a9df vocab=cb247c9f
-/
theorem whiskerLeft_zero' (f : a ⟶ b) {g h : b ⟶ c} : f ◁ (0 : g ⟶ h) = 0 := by
  have := whiskerLeft_add' f (0 : g ⟶ h) 0
  rw [add_zero] at this
  exact (add_eq_left.1 this.symm)

/--
@isnad1 id=eq.0h8v.s9.ddab586d5113 from=translated src=- shape=037892e6 vocab=ef448ac8
-/
theorem zero_whiskerRight' {f g : a ⟶ b} (h : b ⟶ c) : (0 : f ⟶ g) ▷ h = 0 := by
  have := add_whiskerRight' (0 : f ⟶ g) 0 h
  rw [add_zero] at this
  exact (add_eq_left.1 this.symm)

/-- **Definition 4.4**, formula (4.4): for `x : Πᵃ F ⇒ Πᶜ H` and `y : Πᵇ G ⇒ Πᵈ K` homogeneous
in `B`, the horizontal composite in `𝔄_π` is
`y_b^d x_a^c = (-1)^{b|x| + |y|c + bc + ab} (yx)_{a+b}^{c+d}`.
@isnad1 id=eq.2h13v.s13.29eec886c7d2 from=translated src=- shape=ee900828 vocab=4846ace0
-/
theorem toHom_hcomp {f h : a ⟶ b} {g k : b ⟶ c} {x : f ⟶ h} {y : g ⟶ k} {px py : ZMod 2}
    (hx : toHom x ∈ parity (R := R) f.obj h.obj px)
    (hy : toHom y ∈ parity (R := R) g.obj k.obj py) :
    toHom (hcomp x y) =
      sign R (g.par * px + py * h.par + g.par * h.par + f.par * g.par) •
        hcomp (toHom x) (toHom y) := by
  rw [hcomp, hcomp, toHom_comp, toHom_whiskerRight_of_mem hx, toHom_whiskerLeft_of_mem _ hy,
    Linear.smul_comp, Linear.comp_smul, smul_smul, ← sign_add]
  congr 2
  ring

/-- The sign check displayed in Definition 4.4 for the associator: for
`x : Πᵃ F ⇒ Πᵈ F'`, `y : Πᵇ G ⇒ Πᵉ G'`, `z : Πᶜ H ⇒ Πᶠ H'`, the signs in
`(z_c^f y_b^e) x_a^d = (-1)^{c|y|+|z|e+ce+bc+(b+c)|x|+(|y|+|z|)d+(b+c)d+a(b+c)} ((zy)x)` and
`z_c^f (y_b^e x_a^d) = (-1)^{b|x|+|y|d+bd+ab+c(|x|+|y|)+|z|(d+e)+c(d+e)+(a+b)c} (z(yx))`
agree.
@isnad1 id=eq.0h8v.s11.6698048b322f from=translated src=- shape=66c6c797 vocab=bf73672e
-/
theorem associator_sign_eq (a b c d e x y z : ZMod 2) :
    c * y + z * e + c * e + b * c + (b + c) * x + (y + z) * d + (b + c) * d + a * (b + c) =
      b * x + y * d + b * d + a * b + c * (x + y) + z * (d + e) + c * (d + e) + (a + b) * c := by
  ring

/-! ## The Π-structure -/

variable (R) in
/-- `π_λ := Π¹ 𝟙_λ` (Definition 4.4).-/
def π (a : TwoEnvelope R B) : a ⟶ a := ⟨1, 𝟙 a.as⟩

omit [TwoSupercategory R B] in
variable (R) in
/-- `ζ_λ := (1_{𝟙_λ})_1^0 : π_λ ≅ 𝟙_λ` (Definition 4.4).-/
def ζ (a : TwoEnvelope R B) : π R a ≅ 𝟙 a := isoOfIso (Iso.refl (𝟙 a.as))

omit [TwoSupercategory R B] in
/--
@isnad1 id=mem.0h3v.s10.1f9c39ce81f1 from=translated src=- shape=22fe8775 vocab=33dbb17a
-/
theorem ζ_hom_mem (a : TwoEnvelope R B) : (ζ R a).hom ∈ parity (R := R) (π R a) (𝟙 a) 1 := by
  rw [mem_parity_iff]
  show 𝟙 (𝟙 a.as) ∈ parity (R := R) (𝟙 a.as) (𝟙 a.as) (1 + (1 + 0))
  exact id_mem _

omit [TwoSupercategory R B] in
/--
@isnad1 id=eq.0h3v.s8.1f3daac8d6b8 from=translated src=- shape=9ecd49c2 vocab=126bb59f
-/
@[simp] theorem toHom_ζ_hom (a : TwoEnvelope R B) : toHom (ζ R a).hom = 𝟙 (𝟙 a.as) := rfl

/-- **Definition 4.4.** `ξ_λ := ζ_λ ζ_λ : π_λ π_λ ⇒ 𝟙_λ 𝟙_λ` is minus the identity.
@isnad1 id=eq.0h3v.s10.4659a71cd609 from=translated src=- shape=3df4ade6 vocab=a8358488
-/
theorem toHom_ξ (a : TwoEnvelope R B) :
    toHom (hcomp (ζ R a).hom (ζ R a).hom) = -𝟙 (𝟙 a.as ≫ 𝟙 a.as) := by
  rw [toHom_hcomp (x := (ζ R a).hom) (y := (ζ R a).hom) (px := 0) (py := 0) (id_mem (𝟙 a.as))
    (id_mem (𝟙 a.as)), hcomp, toHom_ζ_hom]
  show sign R ((1 : ZMod 2) * 0 + 0 * 0 + 1 * 0 + 1 * 1) •
    (𝟙 (𝟙 a.as) ▷ 𝟙 a.as ≫ 𝟙 a.as ◁ 𝟙 (𝟙 a.as)) = _
  rw [TwoSupercategory.id_whiskerRight (R := R), TwoSupercategory.whiskerLeft_id (R := R),
    Category.comp_id]
  simp

/-! ## The canonical `𝕁` and Lemma 4.6 -/

variable (R B) in
/-- A 2-supercategory is Π-complete (Lemma 4.6) if each unit `𝟙_λ` is the target of an odd
2-isomorphism `π_λ ≅ 𝟙_λ`.-/
def PiComplete : Prop :=
  ∀ a : B, ∃ (p : a ⟶ a) (e : p ≅ 𝟙 a), e.hom ∈ parity (R := R) p (𝟙 a) 1

/-- In a Π-complete 2-supercategory every morphism supercategory is Π-complete: `F : λ → μ` is
the target of the odd 2-isomorphism `π_λ F ≅ 𝟙_λ F ≅ F`.
@isnad1 id=picomple.1h4v.s7.a2fa4efdec69 from=translated src=- shape=9f90aed4 vocab=d5f1e79a
-/
theorem piComplete_hom (h : PiComplete R B) (x y : B) : Envelope.PiComplete R (x ⟶ y) := by
  intro f
  obtain ⟨p, e, he⟩ := h x
  let w : p ≫ f ≅ 𝟙 x ≫ f :=
    { hom := e.hom ▷ f
      inv := e.inv ▷ f
      hom_inv_id := by
        rw [← TwoSupercategory.comp_whiskerRight (R := R), e.hom_inv_id,
          TwoSupercategory.id_whiskerRight (R := R)]
      inv_hom_id := by
        rw [← TwoSupercategory.comp_whiskerRight (R := R), e.inv_hom_id,
          TwoSupercategory.id_whiskerRight (R := R)] }
  refine ⟨p ≫ f, w.trans (leftUnitor f), ?_⟩
  have := comp_mem (TwoSupercategory.whiskerRight_mem (R := R) f he)
    (TwoSupercategory.leftUnitor_hom_mem (R := R) f)
  simpa using this

/-- **Lemma 4.6.** The canonical 2-superfunctor `𝕁 : 𝔄 → 𝔄_π` (the identity on objects, so
that it is a 2-superequivalence exactly when it induces superequivalences on all morphism
supercategories) is a 2-superequivalence if and only if `𝔄` is Π-complete.
@isnad1 id=iff.0h2v.s8.7f276193bda6 from=translated src=- shape=7a36559f vocab=bbf14d03
-/
theorem superequivalenceJ_iff :
    (∀ x y : B, Nonempty (Superequivalence R (Envelope.J R (x ⟶ y)))) ↔ PiComplete R B := by
  constructor
  · intro h x
    exact Envelope.piComplete_of_superequivalence (h x x).some (𝟙 x)
  · intro h x y
    exact ⟨Envelope.superequivalenceJ (piComplete_hom h x y)⟩

end Axioms

end TwoEnvelope

end StringDiagrams

end
