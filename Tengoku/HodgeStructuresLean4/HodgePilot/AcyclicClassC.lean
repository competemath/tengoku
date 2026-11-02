import Tengoku.HodgeStructuresLean4.HodgePilot.AcyclicDescent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A sections-surjectivity class engine for abelian sheaves

For abelian sheaves on a site `(C, J)` with sheafification we introduce the
predicate `IsSectionsSurjectiveKernel T G`: every short exact sequence
`0 ⟶ G ⟶ B ⟶ R ⟶ 0` of abelian sheaves induces a surjection
`Γ(T, B) → Γ(T, R)` on sections over `T`.  This is a workhorse lifting
predicate, *not* a classical softness, flasqueness or fineness notion: no
sections-over-closed-sets machinery and no topology enter its definition.

Main results:

* `isSectionsSurjectiveKernel_of_injective` — injective sheaves satisfy the
  predicate (a short exact sequence with injective kernel splits, via
  `Injective.factorThru`, and the splitting's section surjects componentwise);
* `subsingleton_ext_one_of_liftable` and `subsingleton_ext_succ_of_shortExact`
  — generic dimension-shifting bricks over any abelian category with `HasExt`,
  by pure `Ext` long-exact-sequence bookkeeping (no derived category enters);
* `subsingleton_H_one_of_isSectionsSurjectiveKernel` — over a terminal object
  of the site, the predicate forces `Sheaf.H G 1` to be a subsingleton;
* `subsingleton_H_of_isSectionsSurjectiveKernel_class` — **the engine**: for
  a class `P` of abelian sheaves such that (i) every `P`-sheaf satisfies the
  predicate and (ii) `P` is stable under cokernels of `P`-kernels embedded in
  injectives, every `P`-sheaf has subsingleton `Sheaf.H` in every positive
  degree — by induction over the injective-embedding cokernel tower from
  `EnoughInjectives`;
* `space_*` versions — the instantiations at abelian sheaves on a topological
  space, over the terminal object `⊤ : Opens X`.

## Design note

The engine is deliberately *parametric* in the class `P`: membership in the
sections-surjectivity predicate alone constrains only degree-one behaviour,
so the stability of the class under the cokernels appearing in the tower is
taken as the explicit hypothesis `hquot`, to be supplied by whatever
structural property cuts out `P` at the instantiation site.  Both the
exactness and the stability inputs are hypotheses here, consumed and not
proven.

## Claim discipline

Everything in this module is generic homological algebra about abstract
classes of abelian sheaves.  The vanishing conclusions are conditional on
explicit class hypotheses; no concrete sheaf is claimed to satisfy any of
them, and no identification of sheaf cohomology with any other cohomology
theory is stated or implied.  Nothing here makes the Hodge conjecture
statable.
-/

open CategoryTheory Abelian CategoryTheory.Limits Opposite HodgePilot.AcyclicDescent

universe w' w v u

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace HodgePilot.AcyclicClassC

/-! ## Generic dimension-shifting bricks over an abelian category -/

section Bricks

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/-- **Degree-one brick.**  If every map `Z ⟶ S.X₃` lifts through `S.g` and
`Ext Z S.X₂ 1` is a subsingleton, then `Ext Z S.X₁ 1` is a subsingleton — by
the covariant `Ext` long exact sequence of the short exact sequence `S`.-/
theorem subsingleton_ext_one_of_liftable (Z : A) {S : ShortComplex A}
    (hS : S.ShortExact)
    (hlift : ∀ φ : Z ⟶ S.X₃, ∃ ψ : Z ⟶ S.X₂, ψ ≫ S.g = φ)
    (hmid : Subsingleton (Ext.{w} Z S.X₂ 1)) :
    Subsingleton (Ext.{w} Z S.X₁ 1) := by
  haveI := hmid
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨y, hy⟩ :=
    Ext.covariant_sequence_exact₁ Z hS x (Subsingleton.elim _ 0) (zero_add 1)
  obtain ⟨ψ, hψ⟩ := hlift (Ext.addEquiv₀ y)
  have e1 : x =
      ((Ext.mk₀ ψ).comp (Ext.mk₀ S.g) (zero_add 0)).comp hS.extClass (zero_add 1) := by
    rw [Ext.mk₀_comp_mk₀, hψ, Ext.mk₀_addEquiv₀_apply, hy]
  have e2 : ((Ext.mk₀ ψ).comp (Ext.mk₀ S.g) (zero_add 0)).comp hS.extClass (zero_add 1) =
      (Ext.mk₀ ψ).comp ((Ext.mk₀ S.g).comp hS.extClass (zero_add 1)) (zero_add 1) :=
    Ext.comp_assoc (Ext.mk₀ ψ) (Ext.mk₀ S.g) hS.extClass (zero_add 0) (zero_add 1)
      (show 0 + 0 + 1 = 1 from rfl)
  rw [e1, e2, hS.comp_extClass]
  exact Ext.comp_zero _ _ _ _ (zero_add 1)

/-- **Dimension-shifting brick.**  If `Ext Z S.X₃ (m+1)` and `Ext Z S.X₂ (m+2)`
are subsingletons, then so is `Ext Z S.X₁ (m+2)` — by the covariant `Ext` long
exact sequence of the short exact sequence `S`.-/
theorem subsingleton_ext_succ_of_shortExact (Z : A) {S : ShortComplex A}
    (hS : S.ShortExact) (m : ℕ)
    (hthird : Subsingleton (Ext.{w} Z S.X₃ (m + 1)))
    (hmid : Subsingleton (Ext.{w} Z S.X₂ (m + 2))) :
    Subsingleton (Ext.{w} Z S.X₁ (m + 2)) := by
  haveI := hthird
  haveI := hmid
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨y, hy⟩ :=
    Ext.covariant_sequence_exact₁ Z hS x (Subsingleton.elim _ 0) rfl
  rw [Subsingleton.elim y 0, Ext.zero_comp] at hy
  exact hy.symm

end Bricks

/-! ## The sections-surjectivity predicate -/

section Predicate

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The sections-surjectivity predicate on an abelian sheaf `G`: every short
exact sequence `0 ⟶ G ⟶ B ⟶ R ⟶ 0` of abelian sheaves induces a surjection
on sections over `T`.  A workhorse lifting predicate — *not* a classical
softness, flasqueness or fineness notion; both the short exactness input and
any eventual membership proof are entirely abelian-categorical data.-/
def IsSectionsSurjectiveKernel (T : C) (G : Sheaf J AddCommGrpCat.{w}) : Prop :=
  ∀ ⦃B R : Sheaf J AddCommGrpCat.{w}⦄ (f : G ⟶ B) (g : B ⟶ R) (hfg : f ≫ g = 0),
    (ShortComplex.mk f g hfg).ShortExact →
    Function.Surjective (g.hom.app (op T))

variable [HasSheafify J AddCommGrpCat.{w}]

set_option backward.isDefEq.respectTransparency false in
/-- Injective sheaves satisfy the sections-surjectivity predicate: a short
exact sequence with injective kernel splits, and the section of the splitting
surjects componentwise.-/
theorem isSectionsSurjectiveKernel_of_injective (T : C)
    (G : Sheaf J AddCommGrpCat.{w}) [Injective G] :
    IsSectionsSurjectiveKernel T G := by
  intro B R f g hfg hS
  haveI : Injective (ShortComplex.mk f g hfg).X₁ := inferInstanceAs (Injective G)
  have σ := hS.splittingOfInjective
  intro r
  refine ⟨σ.s.hom.app (op T) r, ?_⟩
  have hsg : σ.s ≫ g = 𝟙 R := σ.s_g
  calc g.hom.app (op T) (σ.s.hom.app (op T) r)
      = (σ.s ≫ g).hom.app (op T) r := rfl
    _ = (𝟙 R : R ⟶ R).hom.app (op T) r := by rw [hsg]
    _ = r := rfl

end Predicate

/-! ## The bridge and the engine -/

section Engine

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

/-- The bridge from sections-surjectivity to hom-surjectivity out of the
constant abelian sheaf at `ULift ℤ`, over a terminal object of the site, via
`homEquivSections`.-/
lemma exists_lift_of_isSectionsSurjectiveKernel {T : C} (hT : IsTerminal T)
    {G B R : Sheaf J AddCommGrpCat.{w}} (hG : IsSectionsSurjectiveKernel T G)
    (f : G ⟶ B) (g : B ⟶ R) (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact) (φ : constZ J ⟶ R) :
    ∃ ψ : constZ J ⟶ B, ψ ≫ g = φ := by
  obtain ⟨b, hb⟩ := hG f g hfg hS (homEquivSections hT R φ)
  exact ⟨(homEquivSections hT B).symm b, by
    rw [homEquivSections_symm_naturality hT g b, hb, AddEquiv.symm_apply_apply]⟩

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]

/-- Over a terminal object of the site, a sheaf satisfying the
sections-surjectivity predicate has subsingleton first sheaf cohomology:
lifting against the injective-embedding short exact sequence kills the
degree-one obstruction.-/
theorem subsingleton_H_one_of_isSectionsSurjectiveKernel {T : C}
    (hT : IsTerminal T) {G : Sheaf J AddCommGrpCat.{w}}
    (hG : IsSectionsSurjectiveKernel T G) :
    Subsingleton (Sheaf.H G 1) := by
  have hS : (ShortComplex.mk (Injective.ι G) (cokernel.π (Injective.ι G))
      (cokernel.condition _)).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := inferInstanceAs (Mono (Injective.ι G))
      epi_g := inferInstanceAs (Epi (cokernel.π (Injective.ι G))) }
  exact subsingleton_ext_one_of_liftable (constZ J) hS
    (fun φ => exists_lift_of_isSectionsSurjectiveKernel hT hG _ _ _ hS φ)
    (inferInstanceAs (Subsingleton (Sheaf.H (Injective.under G) (0 + 1))))

/-- **The class engine.**  Let `P` be a class of abelian sheaves on a site
with a terminal object such that

* every `P`-sheaf satisfies the sections-surjectivity predicate (`hsurj`), and
* for every short exact sequence `0 ⟶ G ⟶ B ⟶ R ⟶ 0` with `P G` and `B`
  injective, also `P R` (`hquot`).

Then every `P`-sheaf has subsingleton `Sheaf.H` in every positive degree, by
induction over the injective-embedding cokernel tower.  Both hypotheses are
consumed, not proven, here.-/
theorem subsingleton_H_of_isSectionsSurjectiveKernel_class {T : C}
    (hT : IsTerminal T) (P : Sheaf J AddCommGrpCat.{w} → Prop)
    (hsurj : ∀ G, P G → IsSectionsSurjectiveKernel T G)
    (hquot : ∀ ⦃G B R : Sheaf J AddCommGrpCat.{w}⦄ (f : G ⟶ B) (g : B ⟶ R)
      (hfg : f ≫ g = 0), (ShortComplex.mk f g hfg).ShortExact →
      P G → Injective B → P R) :
    ∀ (m : ℕ) (G : Sheaf J AddCommGrpCat.{w}), P G →
      Subsingleton (Sheaf.H G (m + 1)) := by
  intro m
  induction m with
  | zero =>
    exact fun G hG =>
      subsingleton_H_one_of_isSectionsSurjectiveKernel hT (hsurj G hG)
  | succ m ih =>
    intro G hG
    have hS : (ShortComplex.mk (Injective.ι G) (cokernel.π (Injective.ι G))
        (cokernel.condition _)).ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact _
        mono_f := inferInstanceAs (Mono (Injective.ι G))
        epi_g := inferInstanceAs (Epi (cokernel.π (Injective.ι G))) }
    have hQ : P (cokernel (Injective.ι G)) :=
      hquot _ _ (cokernel.condition _) hS hG (Injective.injective_under G)
    exact subsingleton_ext_succ_of_shortExact (constZ J) hS m (ih _ hQ)
      (inferInstanceAs (Subsingleton (Sheaf.H (Injective.under G) ((m + 1) + 1))))

end Engine

/-! ## Instantiation at abelian sheaves on a topological space -/

section Space

open TopologicalSpace

variable {X : TopCat.{0}}

set_option backward.isDefEq.respectTransparency false in
/-- Injective abelian sheaves on a topological space satisfy the
sections-surjectivity predicate over `⊤ : Opens X`.-/
theorem space_isSectionsSurjectiveKernel_of_injective
    (G : TopCat.Sheaf AddCommGrpCat.{0} X) [Injective G] :
    IsSectionsSurjectiveKernel (⊤ : Opens X) G :=
  isSectionsSurjectiveKernel_of_injective (⊤ : Opens X) G

set_option backward.isDefEq.respectTransparency false in
/-- Space-level degree-one vanishing: an abelian sheaf on a topological space
satisfying the sections-surjectivity predicate over `⊤ : Opens X` has
subsingleton first sheaf cohomology.-/
theorem space_subsingleton_H_one_of_isSectionsSurjectiveKernel
    {G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (hG : IsSectionsSurjectiveKernel (⊤ : Opens X) G) :
    Subsingleton (Sheaf.H G 1) :=
  subsingleton_H_one_of_isSectionsSurjectiveKernel
    (HodgePilot.Betti.opensTopTerminal X) hG

set_option backward.isDefEq.respectTransparency false in
/-- **Space-level class engine**: for a class `P` of abelian sheaves on a
topological space such that `P`-sheaves satisfy the sections-surjectivity
predicate over `⊤ : Opens X` and `P` is stable under cokernels of `P`-kernels
embedded in injectives, every `P`-sheaf has subsingleton `Sheaf.H` in every
positive degree.  Both hypotheses are consumed, not proven, here.-/
theorem space_subsingleton_H_of_isSectionsSurjectiveKernel_class
    (P : TopCat.Sheaf AddCommGrpCat.{0} X → Prop)
    (hsurj : ∀ G, P G → IsSectionsSurjectiveKernel (⊤ : Opens X) G)
    (hquot : ∀ ⦃G B R : TopCat.Sheaf AddCommGrpCat.{0} X⦄ (f : G ⟶ B) (g : B ⟶ R)
      (hfg : f ≫ g = 0), (ShortComplex.mk f g hfg).ShortExact →
      P G → Injective B → P R)
    (m : ℕ) (G : TopCat.Sheaf AddCommGrpCat.{0} X) (hG : P G) :
    Subsingleton (Sheaf.H G (m + 1)) :=
  subsingleton_H_of_isSectionsSurjectiveKernel_class
    (HodgePilot.Betti.opensTopTerminal X) P hsurj hquot m G hG

end Space

end HodgePilot.AcyclicClassC
