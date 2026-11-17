import Tengoku.StringDiagramsLean.StringDiagrams.Super.Presented

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 2-morphisms of presented bicategories as morphisms of the presented category

The 2-morphisms `x ⟶ y` between 1-morphisms `x y : l ⟶ m` of `P.Bicat` are, by definition,
the morphisms `P.obj x.obj ⟶ P.obj y.obj` of the presented category `P.Presented`, with the
same composition, identities, sums and scalar multiples. The two types are definitionally
equal but syntactically different, and the instances on `x ⟶ y` are reached by several
paths (the hom categories of `Presentation.instBicategoryStruct`, of
`Presentation.instBicategory` for even signatures, and the linear structures of
`StringDiagrams.Super.Presented` and `StringDiagrams.Biadjunction.Presented`), so rewriting
across them with `rw` may fail or be slow. The lemmas below (all `rfl`) state the
identifications explicitly: rewriting with them from left to right turns an expression in
the hom category of `P.Bicat` into one in `P.Presented`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}} {R : Type w} [CommRing R] {P : Presentation.{w, v} S R}

namespace Presentation.Bicat

variable {l m : P.Bicat} {x y z : l ⟶ m}

/-- A 2-morphism of `P.Bicat` as a morphism of the presented category.-/
abbrev toHom (f : x ⟶ y) : P.obj x.obj ⟶ P.obj y.obj := f

/--
@isnad1 id=eq.0h10v.s8.d7c2a60c576a from=translated src=- shape=0325e409 vocab=0a690c6e
-/
theorem comp_def (f : x ⟶ y) (g : y ⟶ z) :
    f ≫ g = ((toHom f ≫ toHom g : P.obj x.obj ⟶ P.obj z.obj) : x ⟶ z) := rfl

/--
@isnad1 id=eq.0h6v.s7.6b3440ad1adc from=translated src=- shape=fb31e412 vocab=450e1410
-/
theorem id_def (x : l ⟶ m) : 𝟙 x = ((𝟙 (P.obj x.obj) : P.obj x.obj ⟶ P.obj x.obj) : x ⟶ x) :=
  rfl

/--
@isnad1 id=eq.0h10v.s8.edadec03ee19 from=translated src=- shape=52e1149f vocab=0a690c6e
-/
theorem toHom_comp (f : x ⟶ y) (g : y ⟶ z) : toHom (f ≫ g) = toHom f ≫ toHom g := rfl

/--
@isnad1 id=eq.0h6v.s7.908500c80436 from=translated src=- shape=6b42cdfc vocab=68cdec55
-/
theorem toHom_id (x : l ⟶ m) : toHom (𝟙 x) = 𝟙 (P.obj x.obj) := rfl

/--
@isnad1 id=eq.1h7v.s8.13cce542d932 from=translated src=- shape=36de17f7 vocab=36556786
-/
theorem toHom_eqToHom (h : x = y) :
    toHom (eqToHom h) = eqToHom (congrArg (fun z : l ⟶ m => P.obj z.obj) h) := by
  subst h; rfl

end Presentation.Bicat

end StringDiagrams

end
