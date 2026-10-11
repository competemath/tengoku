import Tengoku.OpenaiMath.OAI.Geometry.KahlerSplitting.Monodromy

namespace OAI

section

noncomputable section
open Set Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {Z : ComplexManifold n}

end FirstGerm
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {m n : ℕ} {M : ComplexManifold m} {X : ComplexManifold n}

lemma holomorphic_eq_of_eventuallyEq [ConnectedSpace M.Carrier]
    {f g : M.Carrier → X.Carrier} (hf : MDifferentiable (model m) (model n) f)
    (hg : MDifferentiable (model m) (model n) g) {o : M.Carrier} (h : f =ᶠ[𝓝 o] g) : f=g := by
  exact funext fun x ↦ (holomorphic_manifolds_eqOn_of_preconnected_of_eventuallyEq
    isOpen_univ isPreconnected_univ hf.mdifferentiableOn hg.mdifferentiableOn (mem_univ o) h) (mem_univ x)

lemma LocalBiholomorphism.eq_germ_of_comp_eq {Z : ComplexManifold n}
    {p : Z.Carrier → X.Carrier} (hp : LocalBiholomorphism p)
    {A : Type*} [TopologicalSpace A] {F G : A → Z.Carrier} {a : A}
    (hF : ContinuousAt F a) (hG : ContinuousAt G a) (h0 : F a=G a)
    (he : (p ∘ F) =ᶠ[𝓝 a] (p ∘ G)) : F =ᶠ[𝓝 a] G := by
  obtain ⟨e,hea,hep,_,_⟩ := hp (F a)
  have hea' : G a ∈ e.source := h0 ▸ hea
  filter_upwards [hF (e.open_source.mem_nhds hea),hG (e.open_source.mem_nhds hea'),he] with b hb hb' heq
  apply e.injOn hb hb'
  exact (hep _ hb).trans (heq.trans (hep _ hb').symm)

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}

structure GlobalProjection (π : OrdinaryUniversalCover X Z) (o : Z.Carrier)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S)) where
  germs : C(Z.Carrier,HolomorphicEtale.Germs X X)
  germs_base : HolomorphicEtale.base X X ∘ germs=π.projection
  germs_initial : germs o=initial h₁ h₂ (π.projection o)
  germs_first : ∀ z, IsFirst (S := S) (germs z).val
  toFun : Z.Carrier → Z.Carrier
  holomorphic : MDifferentiable (model n) (model n) toFun
  based : toFun o=o
  lift : π.projection ∘ toFun=HolomorphicEtale.value ∘ germs

variable {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}

lemma GlobalProjection.initial_germ (Q : GlobalProjection π o h₁ h₂)
    (e : SplittingChart S) (he : π.projection o ∈ e.chart.source) :
    (π.projection ∘ Q.toFun) =ᶠ[𝓝 o]
      (e.firstProjection (e.chart (π.projection o)).2 ∘ π.projection) := by
  have hev := HolomorphicEtale.value_locally Q.germs.continuous (a := o)
    (f := e.firstProjection (e.chart (π.projection o)).2) (by
      rw [Q.germs_initial,initial_eq h₁ h₂ e _ he]; rfl)
  rw [Q.lift]
  filter_upwards [hev] with z hz
  exact hz.trans (congrArg (e.firstProjection (e.chart (π.projection o)).2) (congrFun Q.germs_base z))

lemma value_vertical {A : Type*} [TopologicalSpace A]
    {F : A → HolomorphicEtale.Germs X X} (hF : Continuous F)
    (hfirst : ∀ a, IsFirst (S := S) (F a).val)
    (hv : ProductBoxTopology.IsVertical (splittingAtlas S) (HolomorphicEtale.base X X ∘ F))
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S)) :
    IsLocallyConstant (HolomorphicEtale.value ∘ F) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro a
  obtain ⟨e,hea,_⟩ := exists_splittingChart S h₁ h₂ (HolomorphicEtale.base X X (F a))
  obtain ⟨f,hf⟩ := hfirst a e hea
  have hev := HolomorphicEtale.value_locally hF hf
  let W := (HolomorphicEtale.base X X ∘ F) ⁻¹' e.chart.source
  have hW : IsOpen W := e.chart.open_source.preimage hv.1
  have hlc := (hv.2 e.chart ⟨e,rfl⟩).eventually_eq (⟨a,hea⟩ : W)
  obtain ⟨V,hV,hsub⟩ := (mem_nhds_subtype W ⟨a,hea⟩ _).mp hlc
  filter_upwards [hev,hV,hW.mem_nhds hea] with b hb hbV hbW
  have hh := hsub (show (⟨b,hbW⟩ : W) ∈ Subtype.val ⁻¹' V from hbV)
  change (e.chart (HolomorphicEtale.base X X (F b))).1=
    (e.chart (HolomorphicEtale.base X X (F a))).1 at hh
  change HolomorphicEtale.value (F b)=HolomorphicEtale.value (F a)
  rw [hb,HolomorphicEtale.value_of_section hf,hh]

lemma GlobalProjection.horizontal_germs (Q : GlobalProjection π o h₁ h₂)
    {α : I → Z.Carrier} (hα : Continuous α) (ha : α 0=o)
    (hh : ProductBoxTopology.IsHorizontal (splittingAtlas S) (π.projection ∘ α)) :
    ∀ t, Q.germs (α t)=initial h₁ h₂ (π.projection (α t)) := by
  have heq : (fun t ↦ Q.germs (α t))=(fun t ↦ initial h₁ h₂ (π.projection (α t))) := by
    refine (HolomorphicEtale.separated X X).eq_of_comp_eq
      (HolomorphicEtale.localHomeomorph X X).isLocallyInjective (Q.germs.continuous.comp hα)
      (continuous_horizontal h₁ h₂ hh) ?_ 0 ?_
    · ext t
      exact congrFun Q.germs_base (α t)
    · rw [ha,Q.germs_initial]
  exact congrFun heq

lemma GlobalProjection.horizontal_fixed (Q : GlobalProjection π o h₁ h₂)
    {α : I → Z.Carrier} (hα : Continuous α) (ha : α 0=o)
    (hh : ProductBoxTopology.IsHorizontal (splittingAtlas S) (π.projection ∘ α)) :
    ∀ t, Q.toFun (α t)=α t := by
  have hb : π.projection ∘ (Q.toFun ∘ α)=π.projection ∘ α := by
    ext t
    have H := congrFun Q.lift (α t)
    change π.projection (Q.toFun (α t))=HolomorphicEtale.value (Q.germs (α t)) at H
    rw [Q.horizontal_germs hα ha hh] at H
    obtain ⟨e,he,_⟩ := exists_splittingChart S h₁ h₂ (π.projection (α t))
    rw [initial_eq h₁ h₂ e _ he] at H
    exact H.trans (e.firstProjection_self he)
  have heq : Q.toFun ∘ α=α := by
    refine π.covering.isSeparatedMap.eq_of_comp_eq π.covering.isLocalHomeomorph.isLocallyInjective
      (Q.holomorphic.continuous.comp hα) hα hb 0 ?_
    change Q.toFun (α 0)=α 0
    rw [ha,Q.based]
  exact congrFun heq

lemma GlobalProjection.vertical_constant (Q : GlobalProjection π o h₁ h₂)
    {β : I → Z.Carrier} (hβ : Continuous β)
    (hv : ProductBoxTopology.IsVertical (splittingAtlas S) (π.projection ∘ β)) :
    ∀ t, Q.toFun (β t)=Q.toFun (β 0) := by
  have hc := value_vertical (Q.germs.continuous.comp hβ) (fun t ↦ Q.germs_first (β t))
    (show ProductBoxTopology.IsVertical (splittingAtlas S)
      (HolomorphicEtale.base X X ∘ (Q.germs ∘ β)) from by
        have he : HolomorphicEtale.base X X ∘ (Q.germs ∘ β)=π.projection ∘ β := by
          ext t; exact congrFun Q.germs_base (β t)
        rw [he]; exact hv) h₁ h₂
  have hb : π.projection ∘ (Q.toFun ∘ β)=π.projection ∘ (fun _ : I ↦ Q.toFun (β 0)) := by
    ext t
    exact (congrFun Q.lift (β t)).trans ((hc.apply_eq_of_preconnectedSpace t 0).trans
      (congrFun Q.lift (β 0)).symm)
  have heq : Q.toFun ∘ β=(fun _ : I ↦ Q.toFun (β 0)) :=
    π.covering.isSeparatedMap.eq_of_comp_eq π.covering.isLocalHomeomorph.isLocallyInjective
      (Q.holomorphic.continuous.comp hβ) continuous_const hb 0 rfl
  exact congrFun heq

end FirstGerm
end UniversalCoverSplitting
end
end

end OAI
