/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.KTheory.PrincipalGysinTwistedAR1

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Abstract base change and `i^*`-comparison for the Cartier Gysin map (route AR8)

Abstract abelian-category content of AR1 items 4 and 5 (`PrincipalGysinTwistedAR1.cartierGysin`).

* **Item 4 (G3 analogue).** `Φ : C ⥤ D` (geometrically a finite pushforward `F_*`) with
  `Φ (T E) ≅ T (Φ E)` compatible with `σ` (`PushCompat`; geometrically the projection formula
  `F_*(F^*L⁻¹ ⊗ V) ≅ L⁻¹ ⊗ F_*V`). Then `cartierGysin_D ∘ Φ = Φ ∘ cartierGysin_C`
  (`cartierGysin_comp_map`), as maps of Grothendieck groups.
* **Item 5 (G2 analogue).** For an adjunction `G ⊣ H` with `σ` vanishing on `H G E`
  (`i_* i^* E` is killed by the divisor), `G σ_E = 0` (`map_ap_eq_zero_of_adj`), hence
  `G E ≅ G (coker σ_E)` and, for `σ_E` mono, `pull (cartierGysin [E]) = [G E]`
  (`pull_cartierGysin_classOf_of_mono`).
-/

set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open ExactGrothendieck.PrincipalGysin (KerCokerClosed classOf_eq_of_iso)

universe u v

namespace ExactGrothendieck

namespace CartierGysinAR8

open CartierGysinAR1

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u} [Category.{v} D] [Abelian D]

section MapOn

variable {P : C → Prop} {Q : D → Prop}

/-- The Grothendieck-group map induced by a functor which is exact on short exact sequences
whose three terms lie in `P` (the finite pushforward is exact only on quasicoherent sheaves).-/
def mapOn (Φ : C ⥤ D) [Φ.PreservesZeroMorphisms] (hobj : ∀ E, P E → Q (Φ.obj E))
    (hΦ : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃ →
      (S.map Φ).ShortExact) :
    SubcategoryGroup C P →+ SubcategoryGroup D Q :=
  map (fun E => ⟨Φ.obj E.1, hobj E.1 E.2⟩) fun A B E h => by
    obtain ⟨f, g, zero, hshort⟩ := h
    let S := ShortComplex.mk f g zero
    change shortExactIn D Q ⟨(S.map Φ).X₁, hobj A.1 A.2⟩ ⟨(S.map Φ).X₂, hobj B.1 B.2⟩
      ⟨(S.map Φ).X₃, hobj E.1 E.2⟩
    exact ⟨(S.map Φ).f, (S.map Φ).g, (S.map Φ).zero, hΦ S hshort A.2 B.2 E.2⟩

/--
@isnad1 id=eq.1h8v.s9.76025df412e1 from=translated src=- shape=bf1fce43 vocab=dd44e57f
-/
theorem mapOn_classOf (Φ : C ⥤ D) [Φ.PreservesZeroMorphisms] (hobj : ∀ E, P E → Q (Φ.obj E))
    (hΦ : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃ →
      (S.map Φ).ShortExact) (E : C) (hE : P E) :
    mapOn Φ hobj hΦ (subcategoryClassOf C P E hE) = subcategoryClassOf D Q (Φ.obj E) (hobj E hE) := by
  simp [mapOn, subcategoryClassOf]

end MapOn

section Item4

variable {TC : C ⥤ C} [TC.Additive] [PreservesFiniteLimits TC] [PreservesFiniteColimits TC]
  [TC.PreservesMonomorphisms] {σC : TC ⟶ 𝟭 C}
variable {TD : D ⥤ D} [TD.Additive] [PreservesFiniteLimits TD] [PreservesFiniteColimits TD]
  [TD.PreservesMonomorphisms] {σD : TD ⟶ 𝟭 D}

/-- The compatibility datum of `Φ` with the twists and the sections:
`Φ (T E) ≅ T (Φ E)`, carrying `Φ σ_E` to `σ_{Φ E}`.-/
structure PushCompat (TC : C ⥤ C) (σC : TC ⟶ 𝟭 C) (TD : D ⥤ D) (σD : TD ⟶ 𝟭 D)
    (Φ : C ⥤ D) where
  /-- the comparison isomorphism-/
  iso : ∀ E : C, Φ.obj (TC.obj E) ≅ TD.obj (Φ.obj E)
  /-- compatibility with the sections-/
  comm : ∀ E : C, (iso E).hom ≫ ap TD σD (Φ.obj E) = Φ.map (ap TC σC E)

variable {Φ : C ⥤ D} [Φ.Additive]

/--
@isnad1 id=eq.0h9v.s8.b5f839c7fce2 from=translated src=- shape=fe31ed4b vocab=51e34e09
-/
theorem PushCompat.ap_eq (c : PushCompat TC σC TD σD Φ) (E : C) :
    ap TD σD (Φ.obj E) = (c.iso E).inv ≫ Φ.map (ap TC σC E) := by
  rw [← c.comm E, Iso.inv_hom_id_assoc]

/--
@isnad1 id=eq.1h9v.s8.16a5d0999062 from=translated src=- shape=74467773 vocab=487edca2
-/
theorem PushCompat.ap_eq_zero (c : PushCompat TC σC TD σD Φ) {E : C} (h : ap TC σC E = 0) :
    ap TD σD (Φ.obj E) = 0 := by
  rw [c.ap_eq, h, Functor.map_zero, comp_zero]

variable {PC : C → Prop} {PD : D → Prop}

/-- `Φ` maps `σ`-killed objects to `σ`-killed objects.
@isnad1 id=killed.1h12v.s7.c6307fbef422 from=translated src=- shape=00ee0e19 vocab=9bbf304b
-/
theorem PushCompat.killed (c : PushCompat TC σC TD σD Φ) (hobj : ∀ E, PC E → PD (Φ.obj E))
    (E : C) (hE : Killed TC σC PC E) : Killed TD σD PD (Φ.obj E) :=
  ⟨hobj E hE.1, c.ap_eq_zero hE.2⟩

/-- The map on the killed groups induced by `Φ`.-/
def killedMap (c : PushCompat TC σC TD σD Φ) (hobj : ∀ E, PC E → PD (Φ.obj E))
    (hΦ : ∀ S : ShortComplex C, S.ShortExact → PC S.X₁ → PC S.X₂ → PC S.X₃ →
      (S.map Φ).ShortExact) :
    SubcategoryGroup C (Killed TC σC PC) →+ SubcategoryGroup D (Killed TD σD PD) :=
  mapOn Φ (c.killed hobj) fun S hS h1 h2 h3 => hΦ S hS h1.1 h2.1 h3.1

/-- Cokernel of `σ_{Φ E}` is `Φ (coker σ_E)`, provided `Φ` preserves that cokernel.-/
def cokernelIso (c : PushCompat TC σC TD σD Φ) (E : C)
    [IsIso (cokernelComparison (ap TC σC E) Φ)] :
    cokernel (ap TD σD (Φ.obj E)) ≅ Φ.obj (cokernel (ap TC σC E)) :=
  cokernelIsoOfEq (c.ap_eq E) ≪≫ cokernelEpiComp _ _ ≪≫ asIso (cokernelComparison _ Φ)

/-- Kernel of `σ_{Φ E}` is `Φ (ker σ_E)`, provided `Φ` preserves that kernel.-/
def kernelIso (c : PushCompat TC σC TD σD Φ) (E : C)
    [IsIso (kernelComparison (ap TC σC E) Φ)] :
    kernel (ap TD σD (Φ.obj E)) ≅ Φ.obj (kernel (ap TC σC E)) :=
  kernelIsoOfEq (c.ap_eq E) ≪≫ kernelIsIsoComp _ _ ≪≫ (asIso (kernelComparison _ Φ)).symm

variable (hcC : Central TC σC) (hPC : KerCokerClosed PC) (hTC : ∀ E, PC E → PC (TC.obj E))
  (hcD : Central TD σD) (hPD : KerCokerClosed PD) (hTD : ∀ E, PD E → PD (TD.obj E))

/-- **Base change for the Cartier Gysin map along `Φ`** (G3 analogue, abstract form):
`D^!_D ∘ Φ_* = Φ_* ∘ D^!_C` on Grothendieck groups, when `Φ` is exact, compatible with
`(T, σ)` (`PushCompat`) and preserves kernels and cokernels of the `σ_E`, `E ∈ PC`.
@isnad1 id=eq.7h13v.s10.688d6ffcbe29 from=translated src=- shape=3dc0915d vocab=2e92a6d3
-/
theorem cartierGysin_comp_map (c : PushCompat TC σC TD σD Φ) (hobj : ∀ E, PC E → PD (Φ.obj E))
    (hΦ : ∀ S : ShortComplex C, S.ShortExact → PC S.X₁ → PC S.X₂ → PC S.X₃ →
      (S.map Φ).ShortExact)
    (hker : ∀ E, PC E → IsIso (kernelComparison (ap TC σC E) Φ))
    (hcok : ∀ E, PC E → IsIso (cokernelComparison (ap TC σC E) Φ)) :
    (cartierGysin hcD hPD hTD).comp
        (mapOn Φ hobj hΦ) =
      (killedMap c hobj hΦ).comp (cartierGysin hcC hPC hTC) := by
  refine hom_ext _ _ fun E => ?_
  obtain ⟨E, hE⟩ := E
  have hQ := killedClosed (T := TD) (σ := σD) hPD
  haveI := hker E hE
  haveI := hcok E hE
  have hΦE : PD (Φ.obj E) := hobj E hE
  change cartierGysin hcD hPD hTD (mapOn Φ hobj hΦ
      (subcategoryClassOf C PC E hE)) =
    killedMap c hobj hΦ (cartierGysin hcC hPC hTC (subcategoryClassOf C PC E hE))
  rw [mapOn_classOf, cartierGysin_classOf, cartierGysin_classOf, map_sub]
  have hc' : Killed TC σC PC (cokernel (ap TC σC E)) := killed_cokernel hcC hPC hTC hE
  have hk' : Killed TC σC PC (kernel (ap TC σC E)) := killed_kernel hcC hPC hTC hE
  have m1 : killedMap c hobj hΦ (subcategoryClassOf C (Killed TC σC PC) _ hc') =
      subcategoryClassOf D (Killed TD σD PD) (Φ.obj (cokernel (ap TC σC E)))
        (c.killed hobj _ hc') := mapOn_classOf _ _ _ _ _
  have m2 : killedMap c hobj hΦ (subcategoryClassOf C (Killed TC σC PC) _ hk') =
      subcategoryClassOf D (Killed TD σD PD) (Φ.obj (kernel (ap TC σC E)))
        (c.killed hobj _ hk') := mapOn_classOf _ _ _ _ _
  rw [m1, m2]
  rw [classOf_eq_of_iso hQ (cokernelIso c E) (killed_cokernel hcD hPD hTD hΦE)
      (c.killed hobj _ hc'),
    classOf_eq_of_iso hQ (kernelIso c E) (killed_kernel hcD hPD hTD hΦE) (c.killed hobj _ hk')]

end Item4

section Item5

variable {TC : C ⥤ C} [TC.Additive] [PreservesFiniteLimits TC] [PreservesFiniteColimits TC]
  [TC.PreservesMonomorphisms] {σC : TC ⟶ 𝟭 C}

/-- Right exact `G` sends the cokernel projection of a morphism killed by `G` to an isomorphism
(abstract form of F19 `isIso_map_cokernel_π_of_map_eq_zero`).
@isnad1 id=isiso.1h6v.s7.91ff2a49a089 from=translated src=- shape=b7ee233c vocab=241a8989
-/
theorem isIso_map_cokernel_π_of_map_eq_zero (G : C ⥤ D) [PreservesColimitsOfSize.{0, 0} G]
    {X Y : C} (f : X ⟶ Y) (h : G.map f = 0) : IsIso (G.map (cokernel.π f)) := by
  haveI : IsIso (cokernel.π (G.map f)) := cokernel.π_of_zero h
  rw [← π_comp_cokernelComparison f G]
  infer_instance

/-- **`G σ_E = 0`** for a left adjoint `G ⊣ H` as soon as `σ` vanishes on `H G E`
(abstract form of F19 `pullback_tMul_eq_zero`).
@isnad1 id=eq.1h8v.s8.839253a1c658 from=translated src=- shape=08a0dfec vocab=b2c7fa49
-/
theorem map_ap_eq_zero_of_adj {G : C ⥤ D} {H : D ⥤ C} (adj : G ⊣ H) [G.PreservesZeroMorphisms]
    (E : C) (hH : ap TC σC (H.obj (G.obj E)) = 0) : G.map (ap TC σC E) = 0 := by
  have hn : (TC.map (adj.unit.app E)) ≫ ap TC σC (H.obj (G.obj E)) =
      ap TC σC E ≫ adj.unit.app E := naturality' TC σC _
  have hu := adj.unit.naturality (ap TC σC E)
  have h0 : adj.homEquiv _ _ (G.map (ap TC σC E)) = 0 := by
    rw [Adjunction.homEquiv_unit]
    refine hu.symm.trans ?_
    change ap TC σC E ≫ adj.unit.app E = 0
    rw [← hn, hH]
    exact comp_zero
  calc G.map (ap TC σC E)
      = (adj.homEquiv _ _).symm (adj.homEquiv _ _ (G.map (ap TC σC E))) := by simp
    _ = (adj.homEquiv _ _).symm 0 := by rw [h0]
    _ = 0 := by simp [Adjunction.homEquiv_counit]

variable (hcC : Central TC σC) {PC : C → Prop} (hPC : KerCokerClosed PC)
  (hTC : ∀ E, PC E → PC (TC.obj E))

/-- **`cartierGysin = G` on `σ`-regular classes** (G2 analogue, abstract form). Let `G ⊣ H`
with `σ` zero on `H G E`, and let `pull` be any additive map on the killed group computing `G`
on classes of killed objects (geometrically `AR4.pullFibre` composed with the identification of
`σ`-killed with `IdealKills`). If `σ_E` is mono, then `pull (D^! [E]) = [G E]`.
@isnad1 id=eq.4h15v.s11.21805082778b from=translated src=- shape=fc29a804 vocab=d68a21aa
-/
theorem pull_cartierGysin_classOf_of_mono {G : C ⥤ D} {H : D ⥤ C} (adj : G ⊣ H)
    [G.PreservesZeroMorphisms] [PreservesColimitsOfSize.{0, 0} G] {Q : D → Prop}
    (hQ0 : Q 0) (pull : SubcategoryGroup C (Killed TC σC PC) →+ SubcategoryGroup D Q)
    (hpull : ∀ K (hK : Killed TC σC PC K), ∃ h : Q (G.obj K),
      pull (subcategoryClassOf C _ K hK) = subcategoryClassOf D Q (G.obj K) h)
    (E : C) (hE : PC E) [Mono (ap TC σC E)] (hH : ap TC σC (H.obj (G.obj E)) = 0)
    (hGE : Q (G.obj E)) :
    pull (cartierGysin hcC hPC hTC (subcategoryClassOf C PC E hE)) =
      subcategoryClassOf D Q (G.obj E) hGE := by
  rw [cartierGysin_classOf_of_mono]
  obtain ⟨h, hh⟩ := hpull _ (killed_cokernel hcC hPC hTC hE)
  rw [hh]
  haveI := isIso_map_cokernel_π_of_map_eq_zero G _ (map_ap_eq_zero_of_adj adj E hH)
  exact subcategoryClassOf_iso D Q h hGE hQ0 (isZero_zero D)
    (asIso (G.map (cokernel.π (ap TC σC E)))).symm

end Item5

end CartierGysinAR8

end ExactGrothendieck
