import Tengoku.PshdLean.PshLines.Plurisubharmonic
import Tengoku.Seed.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Complex affine pullback of plurisubharmonic functions

A complex continuous linear affine map sends each parametrized closed disc
to the corresponding parametrized closed disc, with the same angular
parameter. Thus its pullback preserves the actual nonnegative circle-deficit
integrals. No general holomorphic pullback theorem is assumed here.
-/

open Set

namespace PshLines

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The actual image of a closed affine complex disc under an affine map.
@isnad1 id=eq.0h7v.s8.f05abede1bd0 from=translated src=- shape=4f395af1 vocab=fc2f2e66
-/
theorem image_affineClosedDisc (L : E →L[ℂ] F) (b : F) (x v : E) (r : ℝ) :
    (fun y => b + L y) '' affineClosedDisc x v r =
      affineClosedDisc (b + L x) (L v) r := by
  unfold affineClosedDisc
  rw [image_image]
  congr 1
  funext z
  simp only [map_add, map_smul, add_assoc]

/-- The angular deficit integral is exactly preserved by affine pullback,
including infinite deficit values at poles.
@isnad1 id=eq.0h9v.s8.9365fe2c3380 from=translated src=- shape=4dc7cd7f vocab=fc02ba6c
-/
theorem circleDeficit_comp_affine (u : F → EReal) (L : E →L[ℂ] F) (b : F)
    (x v : E) (r C : ℝ) :
    circleDeficit (fun y => u (b + L y)) x v r C =
      circleDeficit u (b + L x) (L v) r C := by
  simp only [circleDeficit, map_add, map_smul, add_assoc]

/--
@isnad1 id=hasdiscs.1h6v.s8.a785c3ff1ac5 from=translated src=- shape=6d28de3e vocab=dd5ca891
-/
theorem HasDiscSubmeanOn.comp_affine {u : F → EReal} {U : Set F}
    (hu : HasDiscSubmeanOn u U) (L : E →L[ℂ] F) (b : F) :
    HasDiscSubmeanOn (fun y => u (b + L y)) ((fun y => b + L y) ⁻¹' U) := by
  intro x v r hr hD C hC
  have hDU : affineClosedDisc (b + L x) (L v) r ⊆ U := by
    rw [← image_affineClosedDisc L b]
    rintro _ ⟨y, hy, rfl⟩
    exact hD hy
  have hbound : ∀ z ∈ affineClosedDisc (b + L x) (L v) r, u z ≤ (C : EReal) := by
    rw [← image_affineClosedDisc L b]
    rintro _ ⟨y, hy, rfl⟩
    exact hC y hy
  rw [circleDeficit_comp_affine]
  exact hu (b + L x) (L v) r hr hDU C hbound

/-- The full disc criterion is stable under arbitrary complex continuous
linear affine pullback. Injectivity and surjectivity are not required.
@isnad1 id=discpsho.1h6v.s8.b95183b2dbcf from=translated src=- shape=6d28de3e vocab=e4e8e638
-/
theorem DiscPshOn.comp_affine {u : F → EReal} {U : Set F}
    (hu : DiscPshOn u U) (L : E →L[ℂ] F) (b : F) :
    DiscPshOn (fun y => u (b + L y)) ((fun y => b + L y) ⁻¹' U) := by
  refine ⟨fun y hy => hu.ne_top (b + L y) hy, ?_, hu.submean.comp_affine L b⟩
  exact hu.upperSemicontinuousOn.comp
    (continuous_const.add L.continuous).continuousOn (fun _ hy => hy)

/--
@isnad1 id=plurisub.1h6v.s8.0d3deb4605ca from=translated src=- shape=a09e2233 vocab=cc27e238
-/
theorem PlurisubharmonicAt.comp_affine (L : E →L[ℂ] F) (b : F)
    {u : F → EReal} {x : E} (hu : PlurisubharmonicAt u (b + L x)) :
    PlurisubharmonicAt (fun y => u (b + L y)) x := by
  obtain ⟨U, hU, hx, hu⟩ := hu
  exact ⟨(fun y => b + L y) ⁻¹' U,
    hU.preimage (continuous_const.add L.continuous), hx, hu.comp_affine L b⟩

/--
@isnad1 id=plurisub.1h6v.s8.13eec30e6f6d from=translated src=- shape=6d28de3e vocab=625b84ef
-/
theorem PlurisubharmonicOn.comp_affine {u : F → EReal} {U : Set F}
    (hu : PlurisubharmonicOn u U) (L : E →L[ℂ] F) (b : F) :
    PlurisubharmonicOn (fun y => u (b + L y)) ((fun y => b + L y) ⁻¹' U) := by
  intro x hx
  exact PlurisubharmonicAt.comp_affine L b (hu (b + L x) hx)

/--
@isnad1 id=discpsho.1h5v.s8.864655c2d59d from=translated src=- shape=e80f4cce vocab=565284d4
-/
theorem DiscPshOn.comp_continuousLinearMap {u : F → EReal} {U : Set F}
    (hu : DiscPshOn u U) (L : E →L[ℂ] F) :
    DiscPshOn (fun y => u (L y)) (L ⁻¹' U) := by
  simpa only [zero_add] using hu.comp_affine L 0

/--
@isnad1 id=plurisub.1h5v.s8.69a6cc2d51a0 from=translated src=- shape=2929f4d5 vocab=daf3ec57
-/
theorem PlurisubharmonicAt.comp_continuousLinearMap (L : E →L[ℂ] F)
    {u : F → EReal} {x : E} (hu : PlurisubharmonicAt u (L x)) :
    PlurisubharmonicAt (fun y => u (L y)) x := by
  have h : PlurisubharmonicAt u (0 + L x) := by simpa only [zero_add] using hu
  simpa only [zero_add] using PlurisubharmonicAt.comp_affine L 0 h

/--
@isnad1 id=plurisub.1h5v.s8.4d575841c75d from=translated src=- shape=e80f4cce vocab=759336a7
-/
theorem PlurisubharmonicOn.comp_continuousLinearMap {u : F → EReal} {U : Set F}
    (hu : PlurisubharmonicOn u U) (L : E →L[ℂ] F) :
    PlurisubharmonicOn (fun y => u (L y)) (L ⁻¹' U) := by
  simpa only [zero_add] using hu.comp_affine L 0

/-- Restriction to a complex linear subspace preserves the disc criterion;
the subspace need not be closed.
@isnad1 id=discpsho.1h4v.s8.52a5c1f2dd0d from=translated src=- shape=392cb099 vocab=691582f6
-/
theorem DiscPshOn.submodule {u : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (S : Submodule ℂ E) :
    DiscPshOn (fun y : S => u y) ((fun y : S => (y : E)) ⁻¹' U) := by
  simpa only [Submodule.coe_subtypeL, Submodule.coe_subtype] using!
    hu.comp_continuousLinearMap S.subtypeL

/--
@isnad1 id=plurisub.1h4v.s8.6adbb99949d2 from=translated src=- shape=977491be vocab=007359c5
-/
theorem PlurisubharmonicAt.submodule {u : E → EReal} (S : Submodule ℂ E)
    {x : S} (hu : PlurisubharmonicAt u (x : E)) :
    PlurisubharmonicAt (fun y : S => u y) x := by
  exact PlurisubharmonicAt.comp_continuousLinearMap S.subtypeL hu

/--
@isnad1 id=plurisub.1h4v.s8.502db9a53f40 from=translated src=- shape=392cb099 vocab=947f411c
-/
theorem PlurisubharmonicOn.submodule {u : E → EReal} {U : Set E}
    (hu : PlurisubharmonicOn u U) (S : Submodule ℂ E) :
    PlurisubharmonicOn (fun y : S => u y) ((fun y : S => (y : E)) ⁻¹' U) := by
  simpa only [Submodule.coe_subtypeL, Submodule.coe_subtype] using!
    hu.comp_continuousLinearMap S.subtypeL

end PshLines
