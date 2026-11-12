import Tengoku.AbelFormalization.AbelFormalization.RegularZeroGraphLift

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Regular zeros and implicit graph equations

This module extends the explicit graph-lift theorem to a graph cut out by a
smooth scalar equation.  The vertical derivative of the graph equation is
assumed surjective.  This is the exact block calculation used when adjoining
the fixed-iterate shift equations in the pair-merging argument.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative block of a lifted system `(F̃,h)`, where the second row
is an arbitrary scalar implicit equation.-/
def implicitGraphBlockCLM
    (A : E →L[ℝ] F) (B : ℝ →L[ℝ] F)
    (C : E →L[ℝ] ℝ) (D : ℝ →L[ℝ] ℝ) :
    (E × ℝ) →L[ℝ] (F × ℝ) :=
  (ContinuousLinearMap.coprod A B).prod
    (ContinuousLinearMap.coprod C D)

/--
@isnad1 id=eq.0h8v.s9.1509fa57a521 from=translated src=- shape=ea46a5ea vocab=adda72a0
-/
@[simp]
theorem implicitGraphBlockCLM_apply
    (A : E →L[ℝ] F) (B : ℝ →L[ℝ] F)
    (C : E →L[ℝ] ℝ) (D : ℝ →L[ℝ] ℝ)
    (u : E) (v : ℝ) :
    implicitGraphBlockCLM A B C D (u, v) =
      (A u + B v, C u + D v) := by
  simp [implicitGraphBlockCLM]

/-- A block system with a surjective vertical scalar block is surjective
exactly when its restriction to the tangent graph is surjective.
@isnad1 id=iff.2h7v.s9.1d4f78d75cf2 from=translated src=- shape=2bf3b623 vocab=b8141442
-/
theorem surjective_implicitGraphBlockCLM_iff
    (A : E →L[ℝ] F) (B : ℝ →L[ℝ] F)
    (C : E →L[ℝ] ℝ) (D : ℝ →L[ℝ] ℝ)
    (Z : E →L[ℝ] ℝ)
    (hD : Function.Surjective D)
    (htangent : ∀ u, C u + D (Z u) = 0) :
    Function.Surjective (implicitGraphBlockCLM A B C D) ↔
      Function.Surjective (graphReducedCLM A B Z) := by
  have hDinj : Function.Injective D :=
    continuousLinearMap_injective_of_surjective_of_finrank_eq D rfl hD
  constructor
  · intro h y
    obtain ⟨⟨u, v⟩, huv⟩ := h (y, 0)
    refine ⟨u, ?_⟩
    have htop := congrArg Prod.fst huv
    have hbottom := congrArg Prod.snd huv
    simp only [implicitGraphBlockCLM_apply] at htop hbottom
    have hvertical : v = Z u := by
      apply hDinj
      linarith [htangent u]
    simpa only [graphReducedCLM_apply, hvertical] using htop
  · intro h yz
    obtain ⟨v₀, hv₀⟩ := hD yz.2
    obtain ⟨u, hu⟩ := h (yz.1 - B v₀)
    refine ⟨(u, Z u + v₀), ?_⟩
    apply Prod.ext
    · simp only [implicitGraphBlockCLM_apply, map_add,
        graphReducedCLM_apply] at hu ⊢
      calc
        A u + (B (Z u) + B v₀) = (A u + B (Z u)) + B v₀ := by abel
        _ = (yz.1 - B v₀) + B v₀ := by rw [hu]
        _ = yz.1 := sub_add_cancel _ _
    · simp only [implicitGraphBlockCLM_apply, map_add]
      rw [hv₀]
      linarith [htangent u]

/-- The square system obtained by adjoining an arbitrary implicit scalar
graph equation.-/
def implicitGraphLiftSystem
    (Ftilde : E × ℝ → F) (h : E × ℝ → ℝ) :
    E × ℝ → F × ℝ :=
  fun p ↦ (Ftilde p, h p)

/-- The derivative of the implicit graph lift is the displayed block map.
@isnad1 id=eq.2h6v.s10.28f408ecd875 from=translated src=- shape=43a423cb vocab=ec899495
-/
theorem fderiv_implicitGraphLiftSystem
    {Ftilde : E × ℝ → F} {h : E × ℝ → ℝ}
    {x : E} {z : ℝ}
    (hF : DifferentiableAt ℝ Ftilde (x, z))
    (hh : DifferentiableAt ℝ h (x, z)) :
    fderiv ℝ (implicitGraphLiftSystem Ftilde h) (x, z) =
      implicitGraphBlockCLM
        (graphLiftXBlock (fderiv ℝ Ftilde (x, z)))
        (graphLiftZBlock (fderiv ℝ Ftilde (x, z)))
        (graphLiftXBlock (fderiv ℝ h (x, z)))
        (graphLiftZBlock (fderiv ℝ h (x, z))) := by
  have hlift := hF.hasFDerivAt.prodMk hh.hasFDerivAt
  change HasFDerivAt (implicitGraphLiftSystem Ftilde h)
    ((fderiv ℝ Ftilde (x, z)).prod (fderiv ℝ h (x, z))) (x, z)
    at hlift
  rw [hlift.fderiv]
  apply ContinuousLinearMap.ext
  rintro ⟨u, v⟩
  rw [implicitGraphBlockCLM_apply]
  apply Prod.ext
  · exact graphLift_blocks_apply (fderiv ℝ Ftilde (x, z)) u v
  · exact graphLift_blocks_apply (fderiv ℝ h (x, z)) u v

/-- Differentiating an exact implicit graph identity gives the tangent
relation between its horizontal and vertical derivative blocks.
@isnad1 id=eq.3h5v.s9.b4d8764dd18b from=translated src=- shape=5d75d133 vocab=babcd6eb
-/
theorem implicitGraph_tangent_identity
    {h : E × ℝ → ℝ} {zeta : E → ℝ} {x : E}
    (hh : DifferentiableAt ℝ h (x, zeta x))
    (hzeta : DifferentiableAt ℝ zeta x)
    (hgraph : (fun y ↦ h (y, zeta y)) =ᶠ[nhds x]
      (fun _ : E ↦ (0 : ℝ))) :
    ∀ u,
      graphLiftXBlock (fderiv ℝ h (x, zeta x)) u +
        graphLiftZBlock (fderiv ℝ h (x, zeta x))
          (fderiv ℝ zeta x u) = 0 := by
  have hderiv := fderiv_graphSubstitution
    (Ftilde := h) (zeta := zeta) hh hzeta
  have hzeroDeriv : fderiv ℝ (graphSubstitution h zeta) x = 0 := by
    have heq : graphSubstitution h zeta =ᶠ[nhds x]
        (fun _ : E ↦ (0 : ℝ)) := hgraph
    rw [heq.fderiv_eq]
    simp
  rw [hderiv] at hzeroDeriv
  intro u
  have hu := congrArg (fun T : E →L[ℝ] ℝ ↦ T u) hzeroDeriv
  simpa [graphReducedCLM_apply] using hu

/-- Adjoining a smooth implicit graph equation with nonzero vertical
derivative preserves regular-zero membership.
@isnad1 id=iff.5h7v.s9.e29101116b52 from=translated src=- shape=e5a0231f vocab=06dab4d4
-/
theorem mem_regularZeroSet_implicitGraphLift_iff
    {Omega : Set E} {Ftilde : E × ℝ → F}
    {h : E × ℝ → ℝ} {zeta : E → ℝ} {x : E}
    (hF : DifferentiableAt ℝ Ftilde (x, zeta x))
    (hh : DifferentiableAt ℝ h (x, zeta x))
    (hzeta : DifferentiableAt ℝ zeta x)
    (hgraph : (fun y ↦ h (y, zeta y)) =ᶠ[nhds x]
      (fun _ : E ↦ (0 : ℝ)))
    (hvertical : Function.Surjective
      (graphLiftZBlock (fderiv ℝ h (x, zeta x)))) :
    x ∈ regularZeroSet Omega (graphSubstitution Ftilde zeta) ↔
      (x, zeta x) ∈ regularZeroSet
        ((fun p : E × ℝ ↦ p.1) ⁻¹' Omega)
        (implicitGraphLiftSystem Ftilde h) := by
  have hsub := fderiv_graphSubstitution hF hzeta
  have hlift := fderiv_implicitGraphLiftSystem hF hh
  have htangent := implicitGraph_tangent_identity hh hzeta hgraph
  change (x ∈ Omega ∧ graphSubstitution Ftilde zeta x = 0 ∧
      Function.Surjective (fderiv ℝ (graphSubstitution Ftilde zeta) x)) ↔
    (x ∈ Omega ∧ implicitGraphLiftSystem Ftilde h (x, zeta x) = 0 ∧
      Function.Surjective
        (fderiv ℝ (implicitGraphLiftSystem Ftilde h) (x, zeta x)))
  rw [hsub, hlift,
    surjective_implicitGraphBlockCLM_iff _ _ _ _ _ hvertical htangent]
  have hgraphx : h (x, zeta x) = 0 := hgraph.self_of_nhds
  simp [graphSubstitution, implicitGraphLiftSystem, hgraphx]

end AbelFormalization
