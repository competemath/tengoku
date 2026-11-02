import Tengoku.HodgeStructuresLean4.HodgePilot.AcyclicClassC
import Tengoku.HodgeStructuresLean4.HodgePilot.SingularGammaRel
import Tengoku.HodgeStructuresLean4.HodgePilot.FlasqueEmbed
import Tengoku.HodgeStructuresLean4.HodgePilot.CPointsMetrizable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Subsingleton sheaf cohomology of the sheafified cochain sheaves

This file assembles the parametric class engine of
`HodgePilot.AcyclicClassC`, the Godement/flasque toolkit of
`HodgePilot.FlasqueEmbed`, and the relative `Γ`-surjectivity lemma of
`HodgePilot.SingularGammaRel` into the stage's positive headline
(`subsingleton_H_sheafifiedCochain`): on a paracompact Hausdorff space all of
whose opens carry paracompact subspace topology, every sheafified cochain
sheaf `(sheafifiedCochainComplex X).X k` has subsingleton sheaf cohomology
`Sheaf.H _ (m + 1)` in every positive degree.

The class fed to the engine is

  `FlasqueOrCochain X G := G.IsFlasque ∨ ∃ k, G = (sheafifiedCochainComplex X).X k`.

Its two engine hypotheses are discharged as follows:

* **sections-surjectivity**: flasque sheaves satisfy the engine's predicate by
  Mathlib's Zorn theorem `TopCat.Sheaf.IsFlasque.epi_of_shortExact`
  (`isSectionsSurjectiveKernel_of_isFlasque`), and the sheafified cochain
  sheaves satisfy it by the committed Lemma W of `HodgePilot.SingularGamma`
  (`isSectionsSurjectiveKernel_sheafifiedCochain`);
* **stability under cokernels of injective embeddings**: for a flasque kernel
  by flasque-by-flasque quotient stability
  (`TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂`) together with
  flasqueness of injective sheaves
  (`HodgePilot.FlasqueEmbed.isFlasque_of_injective`); for a sheafified-cochain
  kernel because the cokernel is itself flasque
  (`flasqueCokernel_sheafifiedCochain`): a section of the cokernel over any
  open lifts through the middle over that open by relative Lemma W (this is
  where every open must be paracompact), the lift extends by flasqueness of
  the injective middle, and pushing back down recovers the original section by
  naturality.

Main results:

* `subsingleton_H_sheafifiedCochain` — **the headline**: for a paracompact
  Hausdorff `X` with every open of `X` paracompact in the subspace topology,
  `Subsingleton (Sheaf.H ((sheafifiedCochainComplex X).X k) (m + 1))` for all
  `k` and `m`;
* `paracompactSpace_opens_of_metrizableSpace` — on a metrizable space every
  open carries paracompact subspace topology (subtype metrizability plus
  paracompactness of metric spaces);
* `subsingleton_H_sheafifiedCochain_of_metrizable` — the corollary at
  metrizable scope, with `[MetrizableSpace ↑X]` as the only hypothesis
  (Hausdorffness and both paracompactness hypotheses follow);
* `subsingleton_H_sheafifiedCochain_cpoints`,
  `subsingleton_H_sheafifiedCochain_spoints` — the instantiations at the
  analytic point-spaces `CPoints A` and `SPoints (structMor A)` of a
  finite-type ℂ-algebra `A`, via the metrizability instances of
  `HodgePilot.CPointsMetrizable`.

## Claim discipline

The headline and each corollary are claimed at exactly their stated
hypotheses; nothing is asserted at bare-paracompact scope, and no sheaf other
than those named above is claimed to be flasque or to have subsingleton
cohomology.  The sheaf-level carriers throughout are the sheafified cochain
sheaves of `HodgePilot.SingularResolution` — the word "singular" is not used
in this file for any sheaf-level carrier.  No comparison map is constructed or
used and no comparison statement appears: nothing in this file identifies
sheaf cohomology with singular cohomology in any degree — that identification
remains the named, future, unproven and undeclared Prop
(`SingularSheafComparison`, the P4-Prop of the commentary in
`HodgePilot.HodgePredicate`), untouched by this module.  Nothing here makes
the Hodge conjecture statable.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
  HodgePilot.SingularResolution HodgePilot.AcyclicClassC

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace HodgePilot.CochainAcyclic

variable {X : TopCat.{0}}

/-! ## The two membership legs of the class -/

set_option backward.isDefEq.respectTransparency false in
/-- Flasque abelian sheaves satisfy the engine's sections-surjectivity
predicate over `⊤` — repackaging of Mathlib's Zorn theorem
`TopCat.Sheaf.IsFlasque.epi_of_shortExact`.-/
theorem isSectionsSurjectiveKernel_of_isFlasque
    (G : TopCat.Sheaf AddCommGrpCat.{0} X) [G.IsFlasque] :
    IsSectionsSurjectiveKernel (⊤ : Opens X) G := by
  intro B R f g hfg hS
  haveI : TopCat.Sheaf.IsFlasque (ShortComplex.mk f g hfg).X₁ :=
    inferInstanceAs G.IsFlasque
  have hepi : Epi ((ShortComplex.mk f g hfg).g.1.app (op (⊤ : Opens X))) :=
    TopCat.Sheaf.IsFlasque.epi_of_shortExact hS
  exact (AddCommGrpCat.epi_iff_surjective _).mp hepi

set_option backward.isDefEq.respectTransparency false in
/-- The committed Lemma W of `HodgePilot.SingularGamma`, repackaged into the
engine's predicate: on a paracompact Hausdorff space the sheafified cochain
sheaves satisfy the sections-surjectivity predicate over `⊤`.-/
theorem isSectionsSurjectiveKernel_sheafifiedCochain
    [ParacompactSpace ↑X] [T2Space ↑X] (n : ℕ) :
    IsSectionsSurjectiveKernel (⊤ : Opens X)
      ((sheafifiedCochainComplex X).X n) := by
  intro B R f g hfg hS
  exact HodgePilot.SingularGamma.gammaSurjective_of_shortExact_sheafifiedCochain
    X n f g hfg hS

/-! ## The class -/

/-- The class fed to the parametric engine of `HodgePilot.AcyclicClassC`:
flasque, or literally one of the sheafified cochain sheaves.  Both engine
hypotheses are proven for this class below (`isSectionsSurjectiveKernel_of_
isFlasque`, `isSectionsSurjectiveKernel_sheafifiedCochain`,
`flasqueCokernel_sheafifiedCochain`) at their stated scopes.-/
abbrev FlasqueOrCochain (X : TopCat.{0}) :
    TopCat.Sheaf AddCommGrpCat.{0} X → Prop :=
  fun G => G.IsFlasque ∨ ∃ k : ℕ, G = (sheafifiedCochainComplex X).X k

/-! ## The flasque cokernel -/

set_option backward.isDefEq.respectTransparency false in
/-- **The flasque cokernel.**  On a Hausdorff space all of whose opens carry
paracompact subspace topology, the cokernel of an injective embedding of a
sheafified cochain sheaf is flasque: a section of the cokernel over an open
`V` lifts through the middle over `V` by relative Lemma W
(`HodgePilot.SingularGammaRel.relativeLemmaW`), the lift extends to any larger
open by flasqueness of the injective middle
(`HodgePilot.FlasqueEmbed.isFlasque_of_injective`), and pushing back down hits
the original section by naturality.-/
theorem flasqueCokernel_sheafifiedCochain [T2Space ↑X]
    (hpar : ∀ W : Opens X, ParacompactSpace ↥W) :
    ∀ (n : ℕ) ⦃B R : TopCat.Sheaf AddCommGrpCat.{0} X⦄
      (f : (sheafifiedCochainComplex X).X n ⟶ B) (g : B ⟶ R)
      (hfg : f ≫ g = 0), (ShortComplex.mk f g hfg).ShortExact →
      Injective B → R.IsFlasque := by
  intro n B R f g hfg hSE hB
  refine ⟨fun {U V} i => ?_⟩
  refine (AddCommGrpCat.epi_iff_surjective _).mpr fun q => ?_
  obtain ⟨b, hb⟩ :=
    HodgePilot.SingularGammaRel.relativeLemmaW X V.unop (hpar _) n f g hfg hSE q
  haveI := HodgePilot.FlasqueEmbed.isFlasque_of_injective B hB
  obtain ⟨b', hb'⟩ :=
    (AddCommGrpCat.epi_iff_surjective (B.1.map i)).mp inferInstance b
  refine ⟨g.hom.app U b', ?_⟩
  have hnat : R.1.map i (g.hom.app U b') = g.hom.app V (B.1.map i b') := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      g.hom.naturality]
  rw [hnat, hb']
  exact hb

/-! ## The headline -/

set_option backward.isDefEq.respectTransparency false in
/-- The engine marriage, parametric in the cokernel joint: on a paracompact
Hausdorff space, if the cokernel of every injective embedding of a sheafified
cochain sheaf is flasque (`hcok`, consumed), then every sheafified cochain
sheaf has subsingleton sheaf cohomology in every positive degree — feed the
class `FlasqueOrCochain X` to the parametric engine of
`HodgePilot.AcyclicClassC`.-/
theorem subsingleton_H_sheafifiedCochain_of_flasqueCokernel
    [ParacompactSpace ↑X] [T2Space ↑X]
    (hcok : ∀ (n : ℕ) ⦃B R : TopCat.Sheaf AddCommGrpCat.{0} X⦄
      (f : (sheafifiedCochainComplex X).X n ⟶ B) (g : B ⟶ R) (hfg : f ≫ g = 0),
      (ShortComplex.mk f g hfg).ShortExact → Injective B → R.IsFlasque)
    (k m : ℕ) :
    Subsingleton (Sheaf.H ((sheafifiedCochainComplex X).X k) (m + 1)) := by
  have hsurj : ∀ G, FlasqueOrCochain X G →
      IsSectionsSurjectiveKernel (⊤ : Opens X) G := by
    rintro G (hfl | ⟨n, rfl⟩)
    · haveI := hfl
      exact isSectionsSurjectiveKernel_of_isFlasque G
    · exact isSectionsSurjectiveKernel_sheafifiedCochain n
  have hquot : ∀ ⦃G B R : TopCat.Sheaf AddCommGrpCat.{0} X⦄ (f : G ⟶ B)
      (g : B ⟶ R) (hfg : f ≫ g = 0), (ShortComplex.mk f g hfg).ShortExact →
      FlasqueOrCochain X G → Injective B → FlasqueOrCochain X R := by
    rintro G B R f g hfg hSE (hfl | ⟨n, rfl⟩) hB
    · haveI : TopCat.Sheaf.IsFlasque (ShortComplex.mk f g hfg).X₁ := hfl
      haveI : TopCat.Sheaf.IsFlasque (ShortComplex.mk f g hfg).X₂ :=
        HodgePilot.FlasqueEmbed.isFlasque_of_injective B hB
      exact Or.inl
        (TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hSE)
    · exact Or.inl (hcok n f g hfg hSE hB)
  exact space_subsingleton_H_of_isSectionsSurjectiveKernel_class
    (FlasqueOrCochain X) hsurj hquot m ((sheafifiedCochainComplex X).X k)
    (Or.inr ⟨k, rfl⟩)

set_option backward.isDefEq.respectTransparency false in
/-- **The headline.**  On a paracompact Hausdorff space all of whose opens
carry paracompact subspace topology, every sheafified cochain sheaf has
subsingleton sheaf cohomology in every positive degree:
`Subsingleton (Sheaf.H ((sheafifiedCochainComplex X).X k) (m + 1))` for all
`k` and `m`.  Claimed at exactly these hypotheses; the metrizable corollary
below discharges all of them at once.-/
theorem subsingleton_H_sheafifiedCochain
    [ParacompactSpace ↑X] [T2Space ↑X]
    (hpar : ∀ W : Opens X, ParacompactSpace ↥W) (k m : ℕ) :
    Subsingleton (Sheaf.H ((sheafifiedCochainComplex X).X k) (m + 1)) :=
  subsingleton_H_sheafifiedCochain_of_flasqueCokernel
    (flasqueCokernel_sheafifiedCochain hpar) k m

/-! ## The metrizable discharge -/

/-- On a metrizable space every open carries paracompact subspace topology:
the subtype inclusion is an embedding, so the open is metrizable, and every
metrizable space is paracompact (endow it with a compatible metric; every
pseudo-e-metric space is paracompact).-/
theorem paracompactSpace_opens_of_metrizableSpace
    [MetrizableSpace ↑X] (W : Opens X) : ParacompactSpace ↥W := by
  haveI : MetrizableSpace ↥W :=
    Topology.IsEmbedding.subtypeVal.metrizableSpace
  letI : MetricSpace ↥W := TopologicalSpace.metrizableSpaceMetric ↥W
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- **The metrizable corollary.**  On a metrizable space, every sheafified
cochain sheaf has subsingleton sheaf cohomology in every positive degree —
metrizability supplies Hausdorffness, paracompactness of the space, and
paracompactness of every open.-/
theorem subsingleton_H_sheafifiedCochain_of_metrizable (X : TopCat.{0})
    [MetrizableSpace ↑X] (k m : ℕ) :
    Subsingleton (Sheaf.H ((sheafifiedCochainComplex X).X k) (m + 1)) := by
  haveI : ParacompactSpace ↑X := by
    letI : MetricSpace ↑X := TopologicalSpace.metrizableSpaceMetric ↑X
    infer_instance
  exact subsingleton_H_sheafifiedCochain
    (fun W => paracompactSpace_opens_of_metrizableSpace W) k m

/-! ## Instantiation at the analytic point-spaces -/

set_option backward.isDefEq.respectTransparency false in
/-- **Instantiation at the affine analytic point-space**: for a finite-type
ℂ-algebra `A`, every sheafified cochain sheaf on the analytic point-space
`CPoints A` has subsingleton sheaf cohomology in every positive degree —
`CPoints A` is metrizable by `HodgePilot.Analytic.instMetrizableSpaceCPoints`.-/
theorem subsingleton_H_sheafifiedCochain_cpoints (A : Type) [CommRing A]
    [Algebra ℂ A] [Algebra.FiniteType ℂ A] (k m : ℕ) :
    Subsingleton (Sheaf.H
      ((sheafifiedCochainComplex
        (TopCat.of (HodgePilot.Analytic.CPoints A))).X k) (m + 1)) := by
  haveI : MetrizableSpace ↑(TopCat.of (HodgePilot.Analytic.CPoints A)) :=
    inferInstanceAs (MetrizableSpace (HodgePilot.Analytic.CPoints A))
  exact subsingleton_H_sheafifiedCochain_of_metrizable
    (TopCat.of (HodgePilot.Analytic.CPoints A)) k m

set_option backward.isDefEq.respectTransparency false in
/-- **Instantiation at the scheme-level analytic point-space of an affine
ℂ-scheme**: for a finite-type ℂ-algebra `A`, every sheafified cochain sheaf on
`SPoints (structMor A)` has subsingleton sheaf cohomology in every positive
degree — metrizability by
`HodgePilot.Analytic.instMetrizableSpaceSPointsAffine`.-/
theorem subsingleton_H_sheafifiedCochain_spoints (A : Type) [CommRing A]
    [Algebra ℂ A] [Algebra.FiniteType ℂ A] (k m : ℕ) :
    Subsingleton (Sheaf.H
      ((sheafifiedCochainComplex
        (TopCat.of (HodgePilot.Analytic.SPoints
          (HodgePilot.Analytic.structMor A)))).X k) (m + 1)) := by
  haveI : MetrizableSpace ↑(TopCat.of (HodgePilot.Analytic.SPoints
      (HodgePilot.Analytic.structMor A))) :=
    inferInstanceAs (MetrizableSpace (HodgePilot.Analytic.SPoints
      (HodgePilot.Analytic.structMor A)))
  exact subsingleton_H_sheafifiedCochain_of_metrizable
    (TopCat.of (HodgePilot.Analytic.SPoints
      (HodgePilot.Analytic.structMor A))) k m

end HodgePilot.CochainAcyclic
