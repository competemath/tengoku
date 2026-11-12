import Tengoku.AbelFormalization.AbelFormalization.ImplicitRegularZeroGraphLift

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-dimensional implicit graph lifts

This is the simultaneous-vector form of the implicit graph regularity
calculation.  It permits all finitely many bounded shift variables to be
adjoined in one square system.  Surjectivity of the vertical graph Jacobian
is enough because that block is an endomorphism of a finite-dimensional
space.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The tangent map of a finite-dimensional graph.-/
def finiteGraphTangentCLM (Z : E →L[ℝ] G) : E →L[ℝ] E × G :=
  (ContinuousLinearMap.id ℝ E).prod Z

/--
@isnad1 id=eq.0h4v.s8.57cef749902b from=translated src=- shape=d71c2429 vocab=6ee8375d
-/
@[simp]
theorem finiteGraphTangentCLM_apply (Z : E →L[ℝ] G) (u : E) :
    finiteGraphTangentCLM Z u = (u, Z u) :=
  rfl

/-- The four derivative blocks of an implicit vector graph lift.-/
def finiteImplicitGraphBlockCLM
    (A : E →L[ℝ] F) (B : G →L[ℝ] F)
    (C : E →L[ℝ] G) (D : G →L[ℝ] G) :
    (E × G) →L[ℝ] (F × G) :=
  (ContinuousLinearMap.coprod A B).prod
    (ContinuousLinearMap.coprod C D)

/--
@isnad1 id=eq.0h9v.s10.f13bec1ba576 from=translated src=- shape=90657c1b vocab=6d6f3b44
-/
@[simp]
theorem finiteImplicitGraphBlockCLM_apply
    (A : E →L[ℝ] F) (B : G →L[ℝ] F)
    (C : E →L[ℝ] G) (D : G →L[ℝ] G)
    (u : E) (v : G) :
    finiteImplicitGraphBlockCLM A B C D (u, v) =
      (A u + B v, C u + D v) := by
  simp [finiteImplicitGraphBlockCLM]

/-- The derivative induced on the graph.-/
def finiteGraphReducedCLM
    (A : E →L[ℝ] F) (B : G →L[ℝ] F)
    (Z : E →L[ℝ] G) : E →L[ℝ] F :=
  A + B.comp Z

/--
@isnad1 id=eq.0h7v.s9.9975b64abd5f from=translated src=- shape=373e097e vocab=cec8236e
-/
@[simp]
theorem finiteGraphReducedCLM_apply
    (A : E →L[ℝ] F) (B : G →L[ℝ] F)
    (Z : E →L[ℝ] G) (u : E) :
    finiteGraphReducedCLM A B Z u = A u + B (Z u) :=
  rfl

/-- With a surjective vertical endomorphism, the full block derivative is
surjective exactly when its restriction to the implicit graph tangent is.
@isnad1 id=iff.2h8v.s10.38c13780e9e6 from=translated src=- shape=6ae619af vocab=10e7cdf2
-/
theorem surjective_finiteImplicitGraphBlockCLM_iff
    [FiniteDimensional ℝ G]
    (A : E →L[ℝ] F) (B : G →L[ℝ] F)
    (C : E →L[ℝ] G) (D : G →L[ℝ] G)
    (Z : E →L[ℝ] G)
    (hD : Function.Surjective D)
    (htangent : ∀ u, C u + D (Z u) = 0) :
    Function.Surjective (finiteImplicitGraphBlockCLM A B C D) ↔
      Function.Surjective (finiteGraphReducedCLM A B Z) := by
  have hDinj : Function.Injective D :=
    continuousLinearMap_injective_of_surjective_of_finrank_eq D rfl hD
  constructor
  · intro h y
    obtain ⟨⟨u, v⟩, huv⟩ := h (y, 0)
    refine ⟨u, ?_⟩
    have htop := congrArg Prod.fst huv
    have hbottom := congrArg Prod.snd huv
    simp only [finiteImplicitGraphBlockCLM_apply] at htop hbottom
    have hvertical : v = Z u := by
      apply hDinj
      apply add_left_cancel (a := C u)
      exact hbottom.trans (htangent u).symm
    simpa only [finiteGraphReducedCLM_apply, hvertical] using htop
  · intro h yz
    obtain ⟨v₀, hv₀⟩ := hD yz.2
    obtain ⟨u, hu⟩ := h (yz.1 - B v₀)
    refine ⟨(u, Z u + v₀), ?_⟩
    apply Prod.ext
    · simp only [finiteImplicitGraphBlockCLM_apply, map_add,
        finiteGraphReducedCLM_apply] at hu ⊢
      calc
        A u + (B (Z u) + B v₀) = (A u + B (Z u)) + B v₀ := by abel
        _ = (yz.1 - B v₀) + B v₀ := by rw [hu]
        _ = yz.1 := sub_add_cancel _ _
    · simp only [finiteImplicitGraphBlockCLM_apply, map_add]
      rw [hv₀]
      simpa only [add_assoc, zero_add] using
        congrArg (fun z : G ↦ z + yz.2) (htangent u)

/-- Horizontal derivative block for a function on a product.-/
def finiteGraphLiftXBlock (T : (E × G) →L[ℝ] F) : E →L[ℝ] F :=
  T.comp (ContinuousLinearMap.inl ℝ E G)

/-- Vertical derivative block for a function on a product.-/
def finiteGraphLiftZBlock (T : (E × G) →L[ℝ] F) : G →L[ℝ] F :=
  T.comp (ContinuousLinearMap.inr ℝ E G)

/-- Product-domain continuous linear maps split into their two blocks.
@isnad1 id=eq.0h6v.s9.651266182ff8 from=translated src=- shape=62b54604 vocab=d1f9b6a4
-/
theorem finiteGraphLift_blocks_apply
    (T : (E × G) →L[ℝ] F) (u : E) (v : G) :
    T (u, v) = finiteGraphLiftXBlock T u + finiteGraphLiftZBlock T v := by
  rw [show (u, v) = (u, 0) + (0, v) by ext <;> simp]
  rw [map_add]
  rfl

/-- Substitution along a vector-valued graph.-/
def finiteGraphSubstitution (Ftilde : E × G → F) (zeta : E → G) :
    E → F :=
  fun x ↦ Ftilde (x, zeta x)

/-- The square system obtained by adjoining a vector implicit equation.-/
def finiteImplicitGraphLiftSystem
    (Ftilde : E × G → F) (h : E × G → G) :
    E × G → F × G :=
  fun p ↦ (Ftilde p, h p)

/-- The derivative after vector graph substitution.
@isnad1 id=eq.2h6v.s9.3e87cd4ca075 from=translated src=- shape=99b9a0ca vocab=35805e4b
-/
theorem fderiv_finiteGraphSubstitution
    {Ftilde : E × G → F} {zeta : E → G} {x : E}
    (hF : DifferentiableAt ℝ Ftilde (x, zeta x))
    (hzeta : DifferentiableAt ℝ zeta x) :
    fderiv ℝ (finiteGraphSubstitution Ftilde zeta) x =
      finiteGraphReducedCLM
        (finiteGraphLiftXBlock (fderiv ℝ Ftilde (x, zeta x)))
        (finiteGraphLiftZBlock (fderiv ℝ Ftilde (x, zeta x)))
        (fderiv ℝ zeta x) := by
  have hgraph : HasFDerivAt (fun y ↦ (y, zeta y))
      (finiteGraphTangentCLM (fderiv ℝ zeta x)) x :=
    (hasFDerivAt_id x).prodMk hzeta.hasFDerivAt
  have hcomp := hF.hasFDerivAt.comp x hgraph
  change HasFDerivAt (finiteGraphSubstitution Ftilde zeta)
    ((fderiv ℝ Ftilde (x, zeta x)).comp
      (finiteGraphTangentCLM (fderiv ℝ zeta x))) x at hcomp
  rw [hcomp.fderiv]
  ext u
  simp only [ContinuousLinearMap.comp_apply, finiteGraphTangentCLM_apply,
    finiteGraphReducedCLM_apply]
  exact finiteGraphLift_blocks_apply (fderiv ℝ Ftilde (x, zeta x)) u
    (fderiv ℝ zeta x u)

/-- The derivative of the simultaneous implicit graph lift.
@isnad1 id=eq.2h7v.s10.266387332ccb from=translated src=- shape=c0443c75 vocab=16b41d4e
-/
theorem fderiv_finiteImplicitGraphLiftSystem
    {Ftilde : E × G → F} {h : E × G → G} {x : E} {z : G}
    (hF : DifferentiableAt ℝ Ftilde (x, z))
    (hh : DifferentiableAt ℝ h (x, z)) :
    fderiv ℝ (finiteImplicitGraphLiftSystem Ftilde h) (x, z) =
      finiteImplicitGraphBlockCLM
        (finiteGraphLiftXBlock (fderiv ℝ Ftilde (x, z)))
        (finiteGraphLiftZBlock (fderiv ℝ Ftilde (x, z)))
        (finiteGraphLiftXBlock (fderiv ℝ h (x, z)))
        (finiteGraphLiftZBlock (fderiv ℝ h (x, z))) := by
  have hlift := hF.hasFDerivAt.prodMk hh.hasFDerivAt
  change HasFDerivAt (finiteImplicitGraphLiftSystem Ftilde h)
    ((fderiv ℝ Ftilde (x, z)).prod (fderiv ℝ h (x, z))) (x, z)
    at hlift
  rw [hlift.fderiv]
  apply ContinuousLinearMap.ext
  rintro ⟨u, v⟩
  rw [finiteImplicitGraphBlockCLM_apply]
  apply Prod.ext
  · exact finiteGraphLift_blocks_apply (fderiv ℝ Ftilde (x, z)) u v
  · exact finiteGraphLift_blocks_apply (fderiv ℝ h (x, z)) u v

/-- A local exact graph identity supplies the vector tangent relation.
@isnad1 id=eq.3h6v.s9.ee7d2c7339d6 from=translated src=- shape=60ab6e63 vocab=5c2ad1ba
-/
theorem finiteImplicitGraph_tangent_identity
    {h : E × G → G} {zeta : E → G} {x : E}
    (hh : DifferentiableAt ℝ h (x, zeta x))
    (hzeta : DifferentiableAt ℝ zeta x)
    (hgraph : (fun y ↦ h (y, zeta y)) =ᶠ[nhds x]
      (fun _ : E ↦ (0 : G))) :
    ∀ u,
      finiteGraphLiftXBlock (fderiv ℝ h (x, zeta x)) u +
        finiteGraphLiftZBlock (fderiv ℝ h (x, zeta x))
          (fderiv ℝ zeta x u) = 0 := by
  have hderiv := fderiv_finiteGraphSubstitution
    (Ftilde := h) (zeta := zeta) hh hzeta
  have heq : finiteGraphSubstitution h zeta =ᶠ[nhds x]
      (fun _ : E ↦ (0 : G)) := hgraph
  have hzeroDeriv : fderiv ℝ (finiteGraphSubstitution h zeta) x = 0 := by
    rw [heq.fderiv_eq]
    simp
  rw [hderiv] at hzeroDeriv
  intro u
  have hu := congrArg (fun T : E →L[ℝ] G ↦ T u) hzeroDeriv
  simpa [finiteGraphReducedCLM_apply] using hu

/-- Simultaneously adjoining finitely many implicit graph equations with a
surjective vertical Jacobian preserves regular-zero membership.
@isnad1 id=iff.5h8v.s9.949afcfd7f57 from=translated src=- shape=76f89f4d vocab=873aca5f
-/
theorem mem_regularZeroSet_finiteImplicitGraphLift_iff
    [FiniteDimensional ℝ G]
    {Omega : Set E} {Ftilde : E × G → F}
    {h : E × G → G} {zeta : E → G} {x : E}
    (hF : DifferentiableAt ℝ Ftilde (x, zeta x))
    (hh : DifferentiableAt ℝ h (x, zeta x))
    (hzeta : DifferentiableAt ℝ zeta x)
    (hgraph : (fun y ↦ h (y, zeta y)) =ᶠ[nhds x]
      (fun _ : E ↦ (0 : G)))
    (hvertical : Function.Surjective
      (finiteGraphLiftZBlock (fderiv ℝ h (x, zeta x)))) :
    x ∈ regularZeroSet Omega (finiteGraphSubstitution Ftilde zeta) ↔
      (x, zeta x) ∈ regularZeroSet
        ((fun p : E × G ↦ p.1) ⁻¹' Omega)
        (finiteImplicitGraphLiftSystem Ftilde h) := by
  have hsub := fderiv_finiteGraphSubstitution hF hzeta
  have hlift := fderiv_finiteImplicitGraphLiftSystem hF hh
  have htangent := finiteImplicitGraph_tangent_identity hh hzeta hgraph
  change (x ∈ Omega ∧ finiteGraphSubstitution Ftilde zeta x = 0 ∧
      Function.Surjective
        (fderiv ℝ (finiteGraphSubstitution Ftilde zeta) x)) ↔
    (x ∈ Omega ∧
      finiteImplicitGraphLiftSystem Ftilde h (x, zeta x) = 0 ∧
      Function.Surjective
        (fderiv ℝ (finiteImplicitGraphLiftSystem Ftilde h) (x, zeta x)))
  rw [hsub, hlift,
    surjective_finiteImplicitGraphBlockCLM_iff _ _ _ _ _
      hvertical htangent]
  have hgraphx : h (x, zeta x) = 0 := hgraph.self_of_nhds
  simp [finiteGraphSubstitution, finiteImplicitGraphLiftSystem, hgraphx]

end AbelFormalization
