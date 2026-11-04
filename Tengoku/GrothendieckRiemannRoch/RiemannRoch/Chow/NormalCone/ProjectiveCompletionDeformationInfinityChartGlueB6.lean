/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.AlgebraicGeometry.Modules.Sheaf
import Tengoku.Seed.Topology.Sheaves.SheafCondition.UniqueGluing
import Tengoku.Seed.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Tengoku.Seed.CategoryTheory.Limits.Preserves.Shapes.Products

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Abstract sheaf-gluing of a chart kernel (route B6)

An abstract gluing datum on a scheme `P`: sheaves of modules `S V` (supported on opens `R V`),
restriction morphisms `ρ`, and the kernel `G.K` of the two descent maps from the product of the
`S V` to the product over refinements (exactly the shape of `nativeGlobalKernel`).

Main results (Mathlib only, no native-twist input):

* `GlueDatum.proj_bijective`: the chart projection `G.K ⟶ G.S U` is bijective on sections over
  every open `W ≤ G.R U`, using the sheaf property, bijectivity of the restrictions `ρ` over the
  support of the smaller chart, the cocycle law on sections, and the chart-overlap covering;
* `chart_isIso`: if `p : K ⟶ ι_* N` is bijective on sections over opens inside the range of an
  open immersion `ι`, then its adjoint `ι^* K ⟶ N` is invertible;
* `mate_bij`, `supp_pushforward`: section-level consequences of an invertible adjoint mate along
  an open immersion and of pushing forward along an open immersion;
* `rhoMap_app`, `rho_cocycle`: section formula and cocycle law for pushed restrictions.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
namespace RRB6
variable {P : Scheme.{u}}

/-- Evaluation of sections of a module at an open, as a functor to abelian groups.-/
noncomputable def secF (W : P.Opens) : P.Modules ⥤ Ab.{u} :=
  Scheme.Modules.toPresheaf P ⋙ (evaluation _ _).obj (op W)

noncomputable def secF_isLimit (W : P.Opens) {J : Type*} [Category J]
    [PreservesLimitsOfShape J (Scheme.Modules.toPresheaf P)] [HasLimitsOfShape J Ab.{u}]
    {F : J ⥤ P.Modules} {c : Cone F} (hc : IsLimit c) : IsLimit ((secF W).mapCone c) :=
  isLimitOfPreserves ((evaluation (Opens P)ᵒᵖ Ab.{u}).obj (op W))
    (isLimitOfPreserves (Scheme.Modules.toPresheaf P) hc)

/--
@isnad1 id=eq.0h5v.s6.b04392fbf207 from=translated src=- shape=2c01d7b8 vocab=bb087b31
-/
theorem secF_map {A B : P.Modules} (f : A ⟶ B) (W : P.Opens) : (secF W).map f = f.app W := rfl

/-- element of an abelian group as a hom from ℤ-/
noncomputable def zhom {G : Ab.{u}} (x : G) : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ G :=
  AddCommGrpCat.ofHom ((zmultiplesHom G x).comp (AddEquiv.ulift (α := ℤ)).toAddMonoidHom)

/--
@isnad1 id=eq.0h2v.s7.c6cdc942e940 from=translated src=- shape=0edfec87 vocab=68884140
-/
theorem zhom_one {G : Ab.{u}} (x : G) : zhom x ⟨1⟩ = x := by
  change (1 : ℤ) • x = x
  simp

/--
@isnad1 id=eq.0h4v.s7.e33ff263fa46 from=translated src=- shape=b08012eb vocab=8b88cc7c
-/
theorem zhom_comp {G H : Ab.{u}} (x : G) (f : G ⟶ H) : zhom x ≫ f = zhom (f x) := by
  ext ⟨n⟩
  change f (n • x) = n • f x
  simp

theorem eq_of_zhom {G : Ab.{u}} {x y : G} (h : zhom x = zhom y) : x = y :=
  (zhom_one x).symm.trans ((congrArg (fun f => f ⟨1⟩) h).trans (zhom_one y))

/-- Every family of elements over an open comes from the product.
@isnad1 id=ex.0h5v.s11.a6e4fdb707e2 from=translated src=- shape=e42600dd vocab=45c6c7d7
-/
theorem pi_sections_exists {ι : Type u} (S : ι → P.Modules) [HasProduct S] (W : P.Opens)
    (a : ∀ i, Γ(S i, W)) : ∃ x : Γ(∏ᶜ S, W), ∀ i, (Pi.π S i).app W x = a i := by
  have hl := secF_isLimit W (productIsProduct S)
  let c : Cone (Discrete.functor S ⋙ secF W) :=
    { pt := AddCommGrpCat.of (ULift.{u} ℤ)
      π := Discrete.natTrans (fun i => zhom (a i.as)) }
  refine ⟨(hl.lift c) ⟨1⟩, fun i => ?_⟩
  have := hl.fac c ⟨i⟩
  have h2 := congrArg (fun f => f ⟨1⟩) this
  exact h2.trans (zhom_one _)

/--
@isnad1 id=eq.0h1v.s6.5f094a48bc17 from=translated src=- shape=85d309d1 vocab=9b2ce366
-/
theorem zhom_zero {G : Ab.{u}} : zhom (0 : G) = 0 := by
  ext ⟨n⟩
  change n • (0 : G) = 0
  simp

section ker

end ker

/-! ### Section restriction API -/

/-- Restriction of sections of a module.-/
noncomputable def rs (M : P.Modules) {A B : P.Opens} (h : A ≤ B) (x : Γ(M, B)) : Γ(M, A) :=
  M.presheaf.map (homOfLE h).op x

/--
@isnad1 id=eq.1h4v.s11.e4985662fc6e from=translated src=- shape=2bcddd88 vocab=03504a32
-/
theorem rs_zero (M : P.Modules) {A B : P.Opens} (h : A ≤ B) : rs M h 0 = 0 := by
  simp [rs]

/--
@isnad1 id=eq.1h6v.s11.d3e6cbee4ea5 from=translated src=- shape=4906a520 vocab=505d0b15
-/
theorem rs_sub (M : P.Modules) {A B : P.Opens} (h : A ≤ B) (x y : Γ(M, B)) :
    rs M h (x - y) = rs M h x - rs M h y := by
  simp [rs]

/--
@isnad1 id=eq.2h6v.s8.cc650953c06d from=translated src=- shape=a2ad4857 vocab=00548edd
-/
theorem rs_rs (M : P.Modules) {A B C : P.Opens} (h1 : A ≤ B) (h2 : B ≤ C) (x : Γ(M, C)) :
    rs M h1 (rs M h2 x) = rs M (h1.trans h2) x := by
  unfold rs
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/--
@isnad1 id=eq.1h7v.s11.f6a51cb43be8 from=translated src=- shape=53ce0599 vocab=43c4110f
-/
theorem hom_rs {M N : P.Modules} (φ : M ⟶ N) {A B : P.Opens} (h : A ≤ B) (x : Γ(M, B)) :
    φ.app A (rs M h x) = rs N h (φ.app B x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x

/--
@isnad1 id=eq.0h5v.s11.d36b3f5f4777 from=translated src=- shape=8ada0f34 vocab=16e6d5b6
-/
theorem hom_zero' {M N : P.Modules} (φ : M ⟶ N) (A : P.Opens) : φ.app A 0 = 0 := by simp

/--
@isnad1 id=eq.0h7v.s12.69eb02d8c4ec from=translated src=- shape=5ab6856e vocab=92337b13
-/
theorem hom_sub' {M N : P.Modules} (φ : M ⟶ N) (A : P.Opens) (x y : Γ(M, A)) :
    φ.app A (x - y) = φ.app A x - φ.app A y := by simp

/--
@isnad1 id=eq.3h7v.s9.7ebce112ecea from=translated src=- shape=1de3f472 vocab=2f0d5337
-/
theorem loc_eq (M : P.Modules) {ι : Type*} (O : ι → P.Opens) {V : P.Opens} (hO : ∀ i, O i ≤ V)
    (hc : V ≤ iSup O) (s t : Γ(M, V)) (h : ∀ i, rs M (hO i) s = rs M (hO i) t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab P) O V
    (fun i => homOfLE (hO i)) hc s t h

/--
@isnad1 id=ex.3h6v.s9.cc42348b43ba from=translated src=- shape=3e38c670 vocab=355d3e83
-/
theorem glue (M : P.Modules) {ι : Type*} (O : ι → P.Opens) {V : P.Opens} (hO : ∀ i, O i ≤ V)
    (hc : V ≤ iSup O) (sf : ∀ i, Γ(M, O i))
    (h : ∀ i j, rs M (inf_le_left : O i ⊓ O j ≤ O i) (sf i) =
      rs M (inf_le_right : O i ⊓ O j ≤ O j) (sf j)) :
    ∃ s : Γ(M, V), ∀ i, rs M (hO i) s = sf i := by
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab P)
    O V (fun i => homOfLE (hO i)) hc sf h
  exact ⟨s, hs⟩

/-! ### Abstract gluing datum -/

/-- Abstract datum: sheaves `S V` on `P` supported on opens `R V`, restriction morphisms,
and a family of refinements.-/
structure GlueDatum (P : Scheme.{u}) (I : Type u) [Preorder I] where
  S : I → P.Modules
  R : I → P.Opens
  ρ : ∀ {C V : I}, C ≤ V → (S V ⟶ S C)
  Ref : Type u
  l : Ref → I
  r : Ref → I
  c : Ref → I
  hl : ∀ q, c q ≤ l q
  hr : ∀ q, c q ≤ r q
  left : (∏ᶜ S) ⟶ ∏ᶜ (fun q : Ref => S (c q))
  right : (∏ᶜ S) ⟶ ∏ᶜ (fun q : Ref => S (c q))
  left_π : ∀ q, left ≫ Pi.π (fun q : Ref => S (c q)) q = Pi.π S (l q) ≫ ρ (hl q)
  right_π : ∀ q, right ≫ Pi.π (fun q : Ref => S (c q)) q = Pi.π S (r q) ≫ ρ (hr q)
  ex : ∀ (V U C : I), C ≤ V → C ≤ U → ∃ q, l q = V ∧ r q = U ∧ c q = C
  Rmono : ∀ {C V : I}, C ≤ V → R C ≤ R V
  bij : ∀ {C V : I} (_ : C ≤ V) (W : P.Opens), W ≤ R C → Function.Bijective ((ρ ‹C ≤ V›).app W)
  supp : ∀ (V : I) (W : P.Opens), Function.Bijective (rs (S V) (inf_le_left : W ⊓ R V ≤ W))
  comp : ∀ {D C V : I} (h1 : D ≤ C) (h2 : C ≤ V) (W : P.Opens) (x : Γ(S V, W)),
    (ρ h1).app W ((ρ h2).app W x) = (ρ (h1.trans h2)).app W x
  ov : ∀ (U V : I) (x : P), x ∈ R U → x ∈ R V → ∃ C, C ≤ U ∧ C ≤ V ∧ x ∈ R C

variable {I : Type u} [Preorder I] (G : GlueDatum P I)

namespace GlueDatum

noncomputable abbrev chart : P.Modules := ∏ᶜ G.S
noncomputable abbrev overlap : P.Modules := ∏ᶜ (fun q : G.Ref => G.S (G.c q))

noncomputable def K : P.Modules := kernel (G.left - G.right)

noncomputable def proj (U : I) : G.K ⟶ G.S U := kernel.ι (G.left - G.right) ≫ Pi.π G.S U

/-- Compatibility of a family of sections.-/
def Compat (W : P.Opens) (a : ∀ V, Γ(G.S V, W)) : Prop :=
  ∀ q : G.Ref, (G.ρ (G.hl q)).app W (a (G.l q)) = (G.ρ (G.hr q)).app W (a (G.r q))

/--
@isnad1 id=compat.0h5v.s10.f3cc471fa293 from=translated src=- shape=cbeaacf1 vocab=edae254e
-/
theorem proj_compat (W : P.Opens) (k : Γ(G.K, W)) :
    G.Compat W (fun V => (G.proj V).app W k) := by
  intro q
  have h0 := kernel.condition (G.left - G.right)
  have h1 : kernel.ι (G.left - G.right) ≫ G.left = kernel.ι (G.left - G.right) ≫ G.right :=
    sub_eq_zero.mp (by rw [← Preadditive.comp_sub]; exact h0)
  have e1 : G.left ≫ Pi.π (fun q : G.Ref => G.S (G.c q)) q = Pi.π G.S (G.l q) ≫ G.ρ (G.hl q) :=
    G.left_π q
  have e2 : G.right ≫ Pi.π (fun q : G.Ref => G.S (G.c q)) q = Pi.π G.S (G.r q) ≫ G.ρ (G.hr q) :=
    G.right_π q
  have h3 : (kernel.ι (G.left - G.right) ≫ Pi.π G.S (G.l q)) ≫ G.ρ (G.hl q) =
      (kernel.ι (G.left - G.right) ≫ Pi.π G.S (G.r q)) ≫ G.ρ (G.hr q) := by
    have := congrArg (fun f => f ≫ Pi.π (fun q : G.Ref => G.S (G.c q)) q) h1
    simp only [Category.assoc, e1, e2] at this
    simpa [Category.assoc] using this
  exact congrArg (fun f => f.app W k) h3

/--
@isnad1 id=eq.3h8v.s11.ba8ccec9c564 from=translated src=- shape=64f791fc vocab=dc097853
-/
theorem compat_ex {W : P.Opens} {a : ∀ V, Γ(G.S V, W)} (ha : G.Compat W a) {V U C : I}
    (h1 : C ≤ V) (h2 : C ≤ U) :
    (G.ρ h1).app W (a V) = (G.ρ h2).app W (a U) := by
  obtain ⟨q, hV, hU, hC⟩ := G.ex V U C h1 h2
  subst hV hU hC
  exact ha q

section comb
variable {G} {U : I} {W : P.Opens}

/--
@isnad1 id=le.1h6v.s7.37a5c6c376f5 from=translated src=- shape=23ce263b vocab=621d8bfb
-/
theorem O_le {C V : I} (h : C ≤ V) : W ⊓ G.R C ≤ W ⊓ G.R V := inf_le_inf_left W (G.Rmono h)

/--
@isnad1 id=eq.3h7v.s11.357cc8dd88d5 from=translated src=- shape=11382393 vocab=6349261f
-/
theorem inj_comb (hW : W ≤ G.R U) (a : ∀ V, Γ(G.S V, W)) (ha : G.Compat W a) (h0 : a U = 0)
    (V : I) : a V = 0 := by
  apply (G.supp V W).1
  rw [rs_zero]
  refine loc_eq (G.S V) (fun C : {C : I // C ≤ U ∧ C ≤ V} => W ⊓ G.R C.1)
    (fun C => O_le C.2.2) ?_ _ _ ?_
  · intro x hx
    obtain ⟨C, hCU, hCV, hxC⟩ := G.ov U V x (hW hx.1) hx.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨C, hCU, hCV⟩, ⟨hx.1, hxC⟩⟩
  · rintro ⟨C, hCU, hCV⟩
    simp only [rs_rs, rs_zero]
    apply (G.bij hCV (W ⊓ G.R C) inf_le_right).1
    rw [hom_rs, hom_zero', compat_ex G ha hCV hCU, h0, hom_zero', rs_zero]

/--
@isnad1 id=eq.4h10v.s12.8e5905b5f5f8 from=translated src=- shape=c8956934 vocab=e6c23269
-/
theorem piece {C D V : I} (hDC : D ≤ C) (hCU : C ≤ U) (hCV : C ≤ V) (t : Γ(G.S U, W))
    {σ : Γ(G.S V, W ⊓ G.R C)}
    (hσ : (G.ρ hCV).app (W ⊓ G.R C) σ = rs (G.S C) inf_le_left ((G.ρ hCU).app W t)) :
    (G.ρ (hDC.trans hCV)).app (W ⊓ G.R D) (rs (G.S V) (O_le hDC) σ) =
      rs (G.S D) inf_le_left ((G.ρ (hDC.trans hCU)).app W t) := by
  rw [← G.comp hDC hCV, hom_rs, hσ, rs_rs, hom_rs, G.comp hDC hCU]

/--
@isnad1 id=ex.1h7v.s11.afcc062ea895 from=translated src=- shape=3ccaf476 vocab=31c5db1c
-/
theorem surj_one (hW : W ≤ G.R U) (t : Γ(G.S U, W)) (V : I) :
    ∃ aV : Γ(G.S V, W), ∀ (C : I) (hCU : C ≤ U) (hCV : C ≤ V),
      rs (G.S C) (inf_le_left : W ⊓ G.R C ≤ W) ((G.ρ hCV).app W aV) =
      rs (G.S C) (inf_le_left : W ⊓ G.R C ≤ W) ((G.ρ hCU).app W t) := by
  let e : ∀ C : {C : I // C ≤ U ∧ C ≤ V},
      Γ(G.S C.1, W ⊓ G.R C.1) ≃ Γ(G.S V, W ⊓ G.R C.1) := fun C =>
    (Equiv.ofBijective _ (G.bij C.2.2 (W ⊓ G.R C.1) inf_le_right)).symm
  let σ : ∀ C : {C : I // C ≤ U ∧ C ≤ V}, Γ(G.S V, W ⊓ G.R C.1) := fun C =>
    e C (rs (G.S C.1) inf_le_left ((G.ρ C.2.1).app W t))
  have hσ : ∀ C : {C : I // C ≤ U ∧ C ≤ V}, (G.ρ C.2.2).app (W ⊓ G.R C.1) (σ C) =
      rs (G.S C.1) inf_le_left ((G.ρ C.2.1).app W t) := fun C =>
    (Equiv.ofBijective _ (G.bij C.2.2 (W ⊓ G.R C.1) inf_le_right)).apply_symm_apply _
  have hcov : W ⊓ G.R V ≤ iSup (fun C : {C : I // C ≤ U ∧ C ≤ V} => W ⊓ G.R C.1) := by
    intro x hx
    obtain ⟨C, hCU, hCV, hxC⟩ := G.ov U V x (hW hx.1) hx.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨C, hCU, hCV⟩, ⟨hx.1, hxC⟩⟩
  obtain ⟨s, hs⟩ := glue (G.S V) (fun C : {C : I // C ≤ U ∧ C ≤ V} => W ⊓ G.R C.1)
    (fun C => O_le C.2.2) hcov σ (by
      intro C C'
      refine loc_eq (G.S V) (fun D : {D : I // D ≤ C.1 ∧ D ≤ C'.1} => W ⊓ G.R D.1)
        (fun D => le_inf (O_le D.2.1) (O_le D.2.2)) ?_ _ _ ?_
      · intro x hx
        obtain ⟨D, hDC, hDC', hxD⟩ := G.ov C.1 C'.1 x hx.1.2 hx.2.2
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨D, hDC, hDC'⟩, ⟨hx.1.1, hxD⟩⟩
      · rintro ⟨D, hDC, hDC'⟩
        rw [rs_rs, rs_rs]
        apply (G.bij (hDC.trans C.2.2) (W ⊓ G.R D) inf_le_right).1
        have h1 := piece hDC C.2.1 C.2.2 t (hσ C)
        have h2 := piece hDC' C'.2.1 C'.2.2 t (hσ C')
        exact h1.trans h2.symm)
  refine ⟨(Equiv.ofBijective _ (G.supp V W)).symm s, fun C hCU hCV => ?_⟩
  have ha : rs (G.S V) (inf_le_left : W ⊓ G.R V ≤ W)
      ((Equiv.ofBijective _ (G.supp V W)).symm s) = s :=
    (Equiv.ofBijective _ (G.supp V W)).apply_symm_apply s
  have hs' := hs ⟨C, hCU, hCV⟩
  calc rs (G.S C) (inf_le_left : W ⊓ G.R C ≤ W)
        ((G.ρ hCV).app W ((Equiv.ofBijective _ (G.supp V W)).symm s))
      = (G.ρ hCV).app (W ⊓ G.R C) (rs (G.S V) (inf_le_left : W ⊓ G.R C ≤ W)
          ((Equiv.ofBijective _ (G.supp V W)).symm s)) := (hom_rs _ _ _).symm
    _ = (G.ρ hCV).app (W ⊓ G.R C) (rs (G.S V) (O_le hCV : W ⊓ G.R C ≤ W ⊓ G.R V)
          (rs (G.S V) (inf_le_left : W ⊓ G.R V ≤ W)
          ((Equiv.ofBijective _ (G.supp V W)).symm s))) := by rw [rs_rs]
    _ = (G.ρ hCV).app (W ⊓ G.R C) (σ ⟨C, hCU, hCV⟩) := by rw [ha, hs']
    _ = _ := hσ ⟨C, hCU, hCV⟩

/--
@isnad1 id=ex.1h6v.s11.55cbfca0840c from=translated src=- shape=6520e5de vocab=31c5db1c
-/
theorem surj_comb (hW : W ≤ G.R U) (t : Γ(G.S U, W)) :
    ∃ a : ∀ V, Γ(G.S V, W), a U = t ∧ ∀ (V C : I) (hCU : C ≤ U) (hCV : C ≤ V),
      rs (G.S C) (inf_le_left : W ⊓ G.R C ≤ W) ((G.ρ hCV).app W (a V)) =
      rs (G.S C) (inf_le_left : W ⊓ G.R C ≤ W) ((G.ρ hCU).app W t) := by
  choose a ha using surj_one hW t
  refine ⟨a, ?_, fun V C hCU hCV => ha V C hCU hCV⟩
  refine loc_eq (G.S U) (fun _ : Unit => W ⊓ G.R U) (fun _ => inf_le_left) ?_ _ _ ?_
  · intro x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(), ⟨hx, hW hx⟩⟩
  · intro _
    apply (G.bij (le_refl U) (W ⊓ G.R U) inf_le_right).1
    rw [hom_rs, hom_rs]
    exact ha U U le_rfl le_rfl

/--
@isnad1 id=compat.2h7v.s11.301dc755c09b from=translated src=- shape=b698ca60 vocab=0d3fc3b2
-/
theorem compat_of_P (hW : W ≤ G.R U) (t : Γ(G.S U, W)) (a : ∀ V, Γ(G.S V, W))
    (ha : ∀ (V C : I) (hCU : C ≤ U) (hCV : C ≤ V),
      rs (G.S C) (inf_le_left : W ⊓ G.R C ≤ W) ((G.ρ hCV).app W (a V)) =
      rs (G.S C) (inf_le_left : W ⊓ G.R C ≤ W) ((G.ρ hCU).app W t)) :
    G.Compat W a := by
  intro q
  apply (G.supp (G.c q) W).1
  refine loc_eq (G.S (G.c q)) (fun D : {D : I // D ≤ U ∧ D ≤ G.c q} => W ⊓ G.R D.1)
    (fun D => O_le D.2.2) ?_ _ _ ?_
  · intro x hx
    obtain ⟨D, hDU, hDE, hxD⟩ := G.ov U (G.c q) x (hW hx.1) hx.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨D, hDU, hDE⟩, ⟨hx.1, hxD⟩⟩
  · rintro ⟨D, hDU, hDE⟩
    rw [rs_rs, rs_rs]
    apply (G.bij hDE (W ⊓ G.R D) inf_le_right).1
    rw [hom_rs, hom_rs]
    rw [G.comp hDE (G.hl q), G.comp hDE (G.hr q), ha _ D hDU (hDE.trans (G.hl q)), ha _ D hDU (hDE.trans (G.hr q))]

end comb

end GlueDatum

/-! ### Bridge: chart morphism of a gluing is invertible -/

/--
@isnad1 id=eq.1h4v.s8.793417c23615 from=translated src=- shape=7cfcb8ff vocab=03504a32
-/
theorem rs_id (M : P.Modules) {A : P.Opens} (h : A ≤ A) (x : Γ(M, A)) : rs M h x = x := by
  simp [rs]

/--
@isnad1 id=bijectiv.2h4v.s8.031352a13cf1 from=translated src=- shape=e730271c vocab=eb9317a5
-/
theorem rs_bij (M : P.Modules) {A B : P.Opens} (h : A ≤ B) (h' : B ≤ A) :
    Function.Bijective (rs M h) := by
  refine ⟨fun x y hxy => ?_, fun y => ⟨rs M h' y, ?_⟩⟩
  · have := congrArg (rs M h') hxy
    rwa [rs_rs, rs_rs, rs_id, rs_id] at this
  · rw [rs_rs, rs_id]

section bridge
variable {X : Scheme.{u}} (ι : X ⟶ P) [IsOpenImmersion ι]

/--
@isnad1 id=eq.0h6v.s9.faa8b5298323 from=translated src=- shape=c0fdaee1 vocab=07cf2a37
-/
theorem restrict_comm (K : P.Modules) (N : X.Modules) (p : K ⟶ (Scheme.Modules.pushforward ι).obj N) :
    (Scheme.Modules.restrictFunctorIsoPullback ι).hom.app K ≫
      ((Scheme.Modules.pullbackPushforwardAdjunction ι).homEquiv K N).symm p =
    ((Scheme.Modules.restrictAdjunction ι).homEquiv K N).symm p := by
  apply ((Scheme.Modules.restrictAdjunction ι).homEquiv K N).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right]
  have h1 := Adjunction.homEquiv_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction ι)
    (Scheme.Modules.pullbackPushforwardAdjunction ι) K
  have h2 : (Scheme.Modules.restrictFunctorIsoPullback ι).hom.app K =
      ((Scheme.Modules.restrictAdjunction ι).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction ι)).hom.app K := rfl
  rw [h2, h1]
  have h3 := Equiv.apply_symm_apply ((Scheme.Modules.pullbackPushforwardAdjunction ι).homEquiv K N) p
  rw [Adjunction.homEquiv_unit] at h3
  exact h3

/-- If `p : K ⟶ ι_* N` is bijective on all sections over opens inside the range of the open
immersion `ι`, then its adjoint `ι^* K ⟶ N` is invertible.
@isnad1 id=isiso.1h6v.s11.520b34c80266 from=translated src=- shape=98b4fa50 vocab=d761dfa6
-/
theorem chart_isIso (K : P.Modules) (N : X.Modules) (p : K ⟶ (Scheme.Modules.pushforward ι).obj N)
    (hp : ∀ W : P.Opens, W ≤ ι.opensRange → Function.Bijective (p.app W)) :
    IsIso (((Scheme.Modules.pullbackPushforwardAdjunction ι).homEquiv K N).symm p) := by
  have hα : IsIso ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app K) := inferInstance
  have hφ : IsIso (((Scheme.Modules.restrictAdjunction ι).homEquiv K N).symm p) := by
    rw [Adjunction.homEquiv_counit]
    have hr : IsIso ((Scheme.Modules.restrictFunctor ι).map p) := by
      rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
      intro W
      have hb := hp (ι ''ᵁ W) (Scheme.Hom.image_le_opensRange ι W)
      exact (ConcreteCategory.isIso_iff_bijective _).2 hb
    haveI : IsIso ((Scheme.Modules.restrictAdjunction ι).counit.app N) :=
      NatIso.isIso_app_of_isIso (Scheme.Modules.restrictAdjunction ι).counit N
    exact IsIso.comp_isIso' hr this
  rw [← restrict_comm] at hφ
  exact IsIso.of_isIso_comp_left ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app K) _

/-- Sections-level bijectivity of a morphism whose adjoint mate along an open immersion is
invertible, over opens inside the range.
@isnad1 id=bijectiv.2h7v.s11.a761f3c31ba8 from=translated src=- shape=72779345 vocab=d761dfa6
-/
theorem mate_bij (N : P.Modules) (N' : X.Modules) (φ : N ⟶ (Scheme.Modules.pushforward ι).obj N')
    (hm : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction ι).homEquiv N N').symm φ))
    (A : P.Opens) (hA : A ≤ ι.opensRange) : Function.Bijective (φ.app A) := by
  have hα : IsIso ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app N) := inferInstance
  have hφ'' : IsIso (((Scheme.Modules.restrictAdjunction ι).homEquiv N N').symm φ) := by
    rw [← restrict_comm]; infer_instance
  have hφ := (Equiv.apply_symm_apply ((Scheme.Modules.restrictAdjunction ι).homEquiv N N') φ).symm
  rw [Adjunction.homEquiv_unit] at hφ
  have hle : A ≤ ι ''ᵁ (ι ⁻¹ᵁ A) := by
    intro x hx
    obtain ⟨y, rfl⟩ := hA hx
    exact ⟨y, hx, rfl⟩
  have key : ⇑(φ.app A) = (((Scheme.Modules.restrictAdjunction ι).homEquiv N N').symm φ).app
      (ι ⁻¹ᵁ A) ∘ rs N (Scheme.Hom.image_preimage_le ι A) := by
    funext x
    have := congrArg (fun f => f.app A x) hφ
    exact this
  rw [key]
  refine Function.Bijective.comp ?_ ?_
  · exact (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  · exact rs_bij N _ hle

/--
@isnad1 id=bijectiv.0h5v.s8.6582b1838b69 from=translated src=- shape=d32239cf vocab=95eb2391
-/
theorem supp_pushforward (N : X.Modules) (W : P.Opens) :
    Function.Bijective (rs ((Scheme.Modules.pushforward ι).obj N)
      (inf_le_left : W ⊓ ι.opensRange ≤ W)) := by
  have hle : ι ⁻¹ᵁ W ≤ ι ⁻¹ᵁ (W ⊓ ι.opensRange) := fun x hx => ⟨hx, ⟨x, rfl⟩⟩
  have e : rs ((Scheme.Modules.pushforward ι).obj N) (inf_le_left : W ⊓ ι.opensRange ≤ W) =
      rs N ((Opens.map ι.base).monotone (inf_le_left : W ⊓ ι.opensRange ≤ W)) := rfl
  rw [e]
  exact rs_bij N _ hle

end bridge

/-! ### Adjunction-mate bookkeeping and section formulas -/

/--
@isnad1 id=eq.0h6v.s10.d3dc6737ca6c from=translated src=- shape=10fd2024 vocab=be64fbd3
-/
theorem map_eq_rs (M : P.Modules) {A B : P.Opens} (f : A ⟶ B) (x : Γ(M, B)) :
    M.presheaf.map f.op x = rs M (leOfHom f) x := by
  unfold rs
  exact congrArg (fun g => M.presheaf.map g.op x) (Subsingleton.elim f (homOfLE (leOfHom f)))

/--
@isnad1 id=eq.0h12v.s9.8a77936aea4c from=translated src=- shape=036b6843 vocab=f3865bf1
-/
theorem homEquiv_conj {C D : Type*} [Category C] [Category D] {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (σ : L₂ ⟶ L₁) (K : C) (Y : D) (h : L₁.obj K ⟶ Y) :
    adj₂.homEquiv K Y (σ.app K ≫ h) = adj₁.homEquiv K Y h ≫ (conjugateEquiv adj₁ adj₂ σ).app Y := by
  simp only [Adjunction.homEquiv_unit, conjugateEquiv_apply_app]
  have n1 := adj₂.unit.naturality (R₁.map h)
  have n2 := σ.naturality (R₁.map h)
  have n3 := adj₂.unit.naturality (adj₁.unit.app K)
  have n4 := σ.naturality (adj₁.unit.app K)
  have tri := adj₁.left_triangle_components K
  have n5 := adj₁.counit.naturality h
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj] at n1 n2 n3 n4 n5
  rw [Category.assoc]
  erw [reassoc_of% n1]
  erw [← Functor.map_comp_assoc, ← Functor.map_comp, n2]
  erw [Category.assoc, n5]
  erw [reassoc_of% n3]
  erw [← Functor.map_comp]
  congr 1
  erw [← Category.assoc, n4]
  erw [Category.assoc, reassoc_of% tri]

/--
@isnad1 id=eq.0h10v.s10.5dc60fd1d9db from=translated src=- shape=6ec4866c vocab=364e2ea3
-/
theorem homEquiv_pullbackComp {X0 X1 X2 : Scheme.{u}} (f1 : X1 ⟶ X0) (f2 : X2 ⟶ X1)
    (K0 : X0.Modules) (K1 : X1.Modules) (K2 : X2.Modules)
    (α : (Scheme.Modules.pullback f1).obj K0 ⟶ K1) (β : (Scheme.Modules.pullback f2).obj K1 ⟶ K2) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f2 ≫ f1)).homEquiv K0 K2
      ((Scheme.Modules.pullbackComp f2 f1).inv.app K0 ≫ (Scheme.Modules.pullback f2).map α ≫ β) =
    (Scheme.Modules.pullbackPushforwardAdjunction f1).homEquiv K0 K1 α ≫
      (Scheme.Modules.pushforward f1).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f2).homEquiv K1 K2 β) ≫
      (Scheme.Modules.pushforwardComp f2 f1).hom.app K2 := by
  have h := homEquiv_conj ((Scheme.Modules.pullbackPushforwardAdjunction f1).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f2))
    (Scheme.Modules.pullbackPushforwardAdjunction (f2 ≫ f1))
    (Scheme.Modules.pullbackComp f2 f1).inv K0 K2 ((Scheme.Modules.pullback f2).map α ≫ β)
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  erw [h, Adjunction.comp_homEquiv]
  have step : (Scheme.Modules.pullbackPushforwardAdjunction f1).homEquiv K0
      ((Scheme.Modules.pushforward f2).obj K2)
      ((Scheme.Modules.pullbackPushforwardAdjunction f2).homEquiv ((Scheme.Modules.pullback f1).obj K0) K2
        ((Scheme.Modules.pullback f2).map α ≫ β)) =
      (Scheme.Modules.pullbackPushforwardAdjunction f1).homEquiv K0 K1 α ≫
        (Scheme.Modules.pushforward f1).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f2).homEquiv K1 K2 β) := by
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  exact congrArg (fun t ↦ t ≫ (Scheme.Modules.pushforwardComp f2 f1).hom.app K2) step

section sections
variable {X' X : Scheme.{u}}

/-- The shape of `pushedNativeRestriction`: push the adjoint along the chart and identify
through the pushforward composition and the chart equality.-/
noncomputable def rhoMap (f : X' ⟶ X) (g : X ⟶ P) (g' : X' ⟶ P) (w : f ≫ g = g')
    {N : X.Modules} {N' : X'.Modules} (φ : N ⟶ (Scheme.Modules.pushforward f).obj N') :
    (Scheme.Modules.pushforward g).obj N ⟶ (Scheme.Modules.pushforward g').obj N' :=
  (Scheme.Modules.pushforward g).map φ ≫ (Scheme.Modules.pushforwardComp f g).inv.app N' ≫
    (Scheme.Modules.pushforwardCongr w).hom.app N'

/--
@isnad1 id=eq.2h11v.s12.e023921da491 from=translated src=- shape=b6b65c60 vocab=575af719
-/
theorem rhoMap_app (f : X' ⟶ X) (g : X ⟶ P) (g' : X' ⟶ P) (w : f ≫ g = g')
    {N : X.Modules} {N' : X'.Modules} (φ : N ⟶ (Scheme.Modules.pushforward f).obj N')
    (W : P.Opens) (hle : g' ⁻¹ᵁ W ≤ f ⁻¹ᵁ (g ⁻¹ᵁ W))
    (x : Γ((Scheme.Modules.pushforward g).obj N, W)) :
    (rhoMap f g g' w φ).app W x = rs N' hle (φ.app (g ⁻¹ᵁ W) x) := by
  subst w
  have h0 := ConcreteCategory.congr_hom (Scheme.Modules.pushforwardCongr_hom_app_app
    (M := N') (rfl : f ≫ g = f ≫ g) W) (φ.app (g ⁻¹ᵁ W) x)
  have h1 : (rhoMap f g (f ≫ g) rfl φ).app W x =
      ((Scheme.Modules.pushforwardCongr (rfl : f ≫ g = f ≫ g)).hom.app N').app W
        (φ.app (g ⁻¹ᵁ W) x) := rfl
  rw [h1, h0]
  exact map_eq_rs N' _ _

variable {XD XC XV : Scheme.{u}}

end sections

end RRB6
