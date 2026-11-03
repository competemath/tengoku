import Tengoku.Seed.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Tengoku.Seed.Algebra.Homology.ShortComplex.ShortExact
import Tengoku.Seed.Algebra.Homology.ShortComplex.SnakeLemma

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Ext-class splicing devices for short exact sequences

Generic homological devices in an abelian category `C` with `[HasExt.{w} C]`
(Joël Riou's `Ext` API), around the pullback of a short exact sequence and
the composition of `Ext`-classes:

* `pbSES S x` — the pullback short complex of a short complex `S` along a map
  `x : Z ⟶ S.X₃` (the `SnakeLemma.L₀'` pattern, standalone), with
  `pbSES_shortExact`: the pullback is short exact when `S` is;
* `pbSESHom` — the canonical morphism of short complexes `pbSES S x ⟶ S`;
* `pbExtClass x hS : Ext Z S.X₁ 1` — the extension class of the pulled-back
  short exact sequence, typed once at the named endpoints `Z`, `S.X₁`;
* `pbExtClass_eq` — **the pullback–extClass identity**: the class of the
  pulled-back short exact sequence is the Yoneda composite
  `(Ext.mk₀ x).comp hS.extClass` (via `extClass_naturality`);
* `extClass_eq_zero_of_splitting` — a split short exact sequence has
  vanishing extension class (the principal-vanishing engine);
* `spliceClass hT u e₂` and its packaging `spliceHom : Ext Z G 1 →+
  Ext Z T.X₁ 2` — the Yoneda splice of a degree-1 class into `G` with the
  extension class of a short exact `T`, along a map `u : G ⟶ T.X₃`,
  via `Ext.comp`; it is additive in the degree-1 slot (`spliceClass_add`,
  `spliceClass_zero`) and vanishes when `T` splits
  (`spliceClass_eq_zero_of_splitting`).

## Claim discipline

Every statement in this module is a generic homological statement about
short exact sequences, pullbacks, and `Ext`-class composition in an abelian
category, and nothing stronger.  NO pairing on any (hyper)cohomology carrier
is constructed, claimed, or implied — in particular no cup product on any
carrier is constructed, claimed, or implied.  No geometric object appears
anywhere in this module; nothing here makes the Hodge conjecture statable.
-/

open CategoryTheory Limits Abelian

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

namespace HodgePilot

namespace ExtSplice

/-! ### The pullback SES device -/

section PbSES

variable (S : ShortComplex C) {Z : C} (x : Z ⟶ S.X₃)

/-- Pullback of a short complex along `x : Z ⟶ S.X₃` (SnakeLemma `L₀'`
pattern): `S.X₁ ⟶ pullback S.g x ⟶ Z`.-/
noncomputable def pbSES : ShortComplex C where
  X₁ := S.X₁
  X₂ := pullback S.g x
  X₃ := Z
  f := pullback.lift S.f 0 (by rw [S.zero, zero_comp])
  g := pullback.snd _ _
  zero := pullback.lift_snd _ _ _

variable {S}

omit [HasExt.{w} C] in
/-- The pullback of a short exact sequence along any map into its third
object is short exact.
@isnad1 id=shortexa.1h4v.s6.173428ed509b from=translated src=- shape=24f1a213 vocab=10633496
-/
theorem pbSES_shortExact (hS : S.ShortExact) : (pbSES S x).ShortExact := by
  have := hS.epi_g
  haveI : Mono S.f := hS.mono_f
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro A a ha
    change A ⟶ pullback S.g x at a
    change a ≫ pullback.snd S.g x = 0 at ha
    obtain ⟨A', π, hπ, x₁, fac⟩ := hS.exact.exact_up_to_refinements (a ≫ pullback.fst S.g x)
      (by rw [Category.assoc, pullback.condition, reassoc_of% ha, zero_comp])
    refine ⟨A', π, hπ, x₁, ?_⟩
    show π ≫ a = x₁ ≫ (pbSES S x).f
    dsimp only [pbSES]
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst] using fac
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, comp_zero, ha, comp_zero]
  · exact @mono_of_mono_fac _ _ _ _ _ _ _ _ hS.mono_f
      (show (pbSES S x).f ≫ pullback.fst S.g x = S.f from pullback.lift_fst _ _ _)
  · dsimp only [pbSES]; infer_instance

/-- The canonical morphism of short complexes `pbSES S x ⟶ S`.-/
noncomputable def pbSESHom : pbSES S x ⟶ S where
  τ₁ := 𝟙 _
  τ₂ := pullback.fst S.g x
  τ₃ := x
  comm₁₂ := by
    dsimp only [pbSES]
    rw [pullback.lift_fst, Category.id_comp]
  comm₂₃ := by
    dsimp only [pbSES]
    exact pullback.condition

/-- The pulled-back extension class, typed once at the NAMED endpoints `Z`,
`S.X₁` (the G-W2S4a retype-once idiom).-/
noncomputable def pbExtClass (hS : S.ShortExact) : Ext Z S.X₁ 1 :=
  (pbSES_shortExact x hS).extClass

/-- THE pullback-extClass identity: the class of the pulled-back short exact
sequence is the Yoneda composite of `x` (in degree 0) with the class of `S` —
via `extClass_naturality`, ascribed at uniform endpoints so `comp_mk₀_id`
fires.
@isnad1 id=eq.1h4v.s7.9498703e0fa7 from=translated src=- shape=2c63847c vocab=7476cb5e
-/
theorem pbExtClass_eq (hS : S.ShortExact) :
    pbExtClass x hS = (Ext.mk₀ x).comp hS.extClass (zero_add 1) := by
  have h2 : (pbExtClass x hS).comp (Ext.mk₀ (𝟙 S.X₁)) (add_zero 1) =
      (Ext.mk₀ x).comp hS.extClass (zero_add 1) :=
    ShortComplex.ShortExact.extClass_naturality (pbSES_shortExact x hS) hS (pbSESHom x)
  rwa [Ext.comp_mk₀_id] at h2

end PbSES

/-! ### Split SES ⇒ extClass = 0 (principal-vanishing engine) -/

/-- A split short exact sequence has vanishing extension class.
@isnad1 id=eq.1h3v.s8.8c87569f62dc from=translated src=- shape=3aac5c83 vocab=dd70236f
-/
theorem extClass_eq_zero_of_splitting {S : ShortComplex C} (hS : S.ShortExact)
    (σ : S.Splitting) : hS.extClass = 0 := by
  calc hS.extClass
      = (Ext.mk₀ (𝟙 S.X₃)).comp hS.extClass (zero_add 1) := (Ext.mk₀_id_comp _).symm
    _ = (Ext.mk₀ (σ.s ≫ S.g)).comp hS.extClass (zero_add 1) := by rw [σ.s_g]
    _ = (Ext.mk₀ σ.s).comp ((Ext.mk₀ S.g).comp hS.extClass (zero_add 1)) (zero_add 1) := by
        rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero]
    _ = 0 := by rw [hS.comp_extClass, Ext.comp_zero]

/-! ### The splice: a degree-1 class composed with an extension class,
additive in the degree-1 slot -/

section Splice

variable {Z G : C} {T : ShortComplex C} (hT : T.ShortExact) (u : G ⟶ T.X₃)

/-- The Yoneda splice: a degree-1 class into `G`, moved into `T.X₃` along
`u` (unitor-shaped), then spliced with the extension class of `T`.-/
noncomputable def spliceClass (e₂ : Ext Z G 1) : Ext Z T.X₁ 2 :=
  (e₂.comp (Ext.mk₀ u) (add_zero 1)).comp hT.extClass rfl

/-- The splice is additive in the degree-1 slot.
@isnad1 id=eq.1h7v.s8.ed9737944b74 from=translated src=- shape=be0579e1 vocab=023eb19d
-/
theorem spliceClass_add (e e' : Ext Z G 1) :
    spliceClass hT u (e + e') = spliceClass hT u e + spliceClass hT u e' := by
  unfold spliceClass
  rw [Ext.add_comp, Ext.add_comp]

/-- The splice vanishes at the zero degree-1 class.
@isnad1 id=eq.1h5v.s8.6acc279c2d16 from=translated src=- shape=a4794fbc vocab=260d5ba0
-/
theorem spliceClass_zero : spliceClass hT u (0 : Ext Z G 1) = 0 := by
  unfold spliceClass
  rw [Ext.zero_comp, Ext.zero_comp]

/-- The splice packaged as an additive map in the degree-1 slot.-/
noncomputable def spliceHom : Ext Z G 1 →+ Ext Z T.X₁ 2 where
  toFun := spliceClass hT u
  map_zero' := spliceClass_zero hT u
  map_add' := spliceClass_add hT u

/-- If the spliced short exact sequence splits, the splice vanishes
(left-slot principal vanishing consumes this through `Splitting.map`).
@isnad1 id=eq.1h7v.s8.29c068f2cf2d from=translated src=- shape=46a7456d vocab=aa5dda76
-/
theorem spliceClass_eq_zero_of_splitting (σ : T.Splitting) (e₂ : Ext Z G 1) :
    spliceClass hT u e₂ = 0 := by
  unfold spliceClass
  rw [extClass_eq_zero_of_splitting hT σ, Ext.comp_zero]

end Splice

end ExtSplice

end HodgePilot
