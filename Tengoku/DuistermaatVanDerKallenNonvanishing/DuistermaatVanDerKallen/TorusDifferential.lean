import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.AffineTorus
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.ScalarLift
import Tengoku.Seed.Analysis.Calculus.FDeriv.WithLp
import Tengoku.Seed.Analysis.Calculus.Deriv.Inv
import Tengoku.Seed.Analysis.Calculus.ContDiff.WithLp
import Tengoku.Seed.Analysis.Calculus.ContDiff.Operations
import Tengoku.Seed.Analysis.InnerProductSpace.LinearMap
import Tengoku.Seed.Tactic.FunProp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The derivative of the proper affine-torus chart, its image tangent space,
and the induced Hermitian metric. Coordinate velocities have their induced
norm through the ambient L2 embedding; the ordinary coordinate sup norm is
used only for the chart's calculus, never as the proper radius or tangent norm. -/

open scoped BigOperators ComplexConjugate

namespace DuistermaatVanDerKallen

noncomputable section

/-- Derivative candidate of `z ↦ (z,z⁻¹)`.-/
def torusTangentMap {d : ℕ} (z : Fin d → ℂ) : (Fin d → ℂ) →L[ℂ] TorusAmbient d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (Sum.elim v fun i => -(z i)⁻¹ ^ 2 * v i)
      map_add' := by
        intro v w
        apply PiLp.ext
        intro i
        cases i <;> simp [mul_add]
      map_smul' := by
        intro c v
        apply PiLp.ext
        intro i
        cases i <;> simp [mul_left_comm] }

@[simp] theorem torusTangentMap_left {d : ℕ} (z v : Fin d → ℂ) (i : Fin d) :
    torusTangentMap z v (.inl i) = v i := rfl

@[simp] theorem torusTangentMap_right {d : ℕ} (z v : Fin d → ℂ) (i : Fin d) :
    torusTangentMap z v (.inr i) = -(z i)⁻¹ ^ 2 * v i := rfl

/-- The chart derivative is computed over ℂ at every point of the open torus.-/
theorem torusEmbed_hasFDerivAt {d : ℕ} {z : Fin d → ℂ} (hz : ∀ i, z i ≠ 0) :
    HasFDerivAt torusEmbed (torusTangentMap z) z := by
  apply HasFDerivWithinAt.hasFDerivAt (s := Set.univ) _ (by simp)
  rw [hasFDerivWithinAt_piLp]
  intro i
  cases i with
  | inl i =>
    change HasFDerivWithinAt (fun x : Fin d → ℂ => x i) _ Set.univ z
    have heq : (PiLp.proj 2 (fun _ : Fin d ⊕ Fin d => ℂ) (.inl i)).comp
        (torusTangentMap z) = ContinuousLinearMap.proj i := by ext v; rfl
    rw [heq]
    exact (hasFDerivAt_apply (𝕜 := ℂ) i z).hasFDerivWithinAt
  | inr i =>
    change HasFDerivWithinAt (fun x : Fin d → ℂ => (x i)⁻¹) _ Set.univ z
    have h := (hasFDerivAt_inv (hz i)).comp z (hasFDerivAt_apply (𝕜 := ℂ) i z)
    have heq : (PiLp.proj 2 (fun _ : Fin d ⊕ Fin d => ℂ) (.inr i)).comp
        (torusTangentMap z) =
        (ContinuousLinearMap.toSpanSingleton ℂ (-(z i ^ 2)⁻¹)).comp
          (ContinuousLinearMap.proj i) := by
      ext v
      simp [ContinuousLinearMap.comp_apply, inv_pow, mul_comm]
    rw [heq]
    exact h.hasFDerivWithinAt

/-- The nonvanishing-coordinate chart domain is open.-/
theorem torusDomain_isOpen (d : ℕ) :
    IsOpen {z : Fin d → ℂ | ∀ i, z i ≠ 0} := by
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_ne_fun (continuous_apply i) continuous_const

/-- The global chart is smooth over ℝ, as needed by real ODE theory.-/
theorem torusEmbed_contDiffAt_real {d : ℕ} {z : Fin d → ℂ}
    (hz : ∀ i, z i ≠ 0) : ContDiffAt ℝ ⊤ torusEmbed z := by
  rw [contDiffAt_piLp]
  intro i
  cases i with
  | inl i => exact contDiffAt_apply ℝ ℂ i z
  | inr i => exact (contDiffAt_apply ℝ ℂ i z).inv (hz i)

/-- The torus chart is a genuine global homeomorphism onto the closed model.-/
def torusChart (d : ℕ) : {z : Fin d → ℂ // ∀ i, z i ≠ 0} ≃ₜ affineTorus d where
  toFun z := ⟨torusEmbed z.val, embed_mem z.property⟩
  invFun x := ⟨fun i => x.val (.inl i), affineTorus_coordinate_ne_zero x.property⟩
  left_inv _z := rfl
  right_inv x := Subtype.ext (embed_coordinates x.property)
  continuous_toFun :=
    (ContinuousOn.domRestrict (fun _ hz =>
      (torusEmbed_contDiffAt_real hz).continuousAt.continuousWithinAt)).subtype_mk _
  continuous_invFun :=
    (continuous_pi fun i => (PiLp.continuous_apply 2 (fun _ : Fin d ⊕ Fin d => ℂ) (.inl i)).comp continuous_subtype_val).subtype_mk _

/-- The tangent subspace in the ambient induced metric.-/
def torusTangentSpace {d : ℕ} (z : Fin d → ℂ) : Submodule ℂ (TorusAmbient d) :=
  LinearMap.range (torusTangentMap z).toLinearMap

theorem mem_torusTangentSpace_iff {d : ℕ} (z : Fin d → ℂ) (v : TorusAmbient d) :
    v ∈ torusTangentSpace z ↔ ∀ i, v (.inr i) = -(z i)⁻¹ ^ 2 * v (.inl i) := by
  constructor
  · rintro ⟨w, rfl⟩ i
    rfl
  · intro h
    refine ⟨fun i => v (.inl i), ?_⟩
    apply PiLp.ext
    intro i
    cases i with
    | inl i => rfl
    | inr i => exact (h i).symm

/-- The derivative image is also the kernel of the linearized defining
equations `zᵢwᵢ = 1`, so it is the tangent space of the affine variety.-/
theorem mem_torusTangentSpace_iff_linearized {d : ℕ} {z : Fin d → ℂ}
    (hz : ∀ i, z i ≠ 0) (v : TorusAmbient d) :
    v ∈ torusTangentSpace z ↔
      ∀ i, (z i)⁻¹ * v (.inl i) + z i * v (.inr i) = 0 := by
  rw [mem_torusTangentSpace_iff]
  constructor
  · intro h i
    rw [h i]
    field_simp [hz i]
    ring
  · intro h i
    have heq := eq_neg_of_add_eq_zero_right (h i)
    calc
      v (.inr i) = (z i)⁻¹ * (z i * v (.inr i)) := by field_simp [hz i]
      _ = -(z i)⁻¹ ^ 2 * v (.inl i) := by rw [heq]; ring

/-- Positive diagonal coefficients of the induced Hermitian metric.-/
def torusWeight {d : ℕ} (z : Fin d → ℂ) (i : Fin d) : ℝ := 1 + ‖z i‖⁻¹ ^ 4

theorem torusWeight_pos {d : ℕ} (z : Fin d → ℂ) (i : Fin d) :
    0 < torusWeight z i := torus_weight_pos _

/-- Manuscript equation `eq:embedding-metric`.-/
theorem torusTangentMap_norm_sq {d : ℕ} (z v : Fin d → ℂ) :
    ‖torusTangentMap z v‖ ^ 2 = ∑ i, torusWeight z i * ‖v i‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [torusTangentMap_left, torusTangentMap_right, norm_mul, norm_neg,
    norm_pow, norm_inv, torusWeight]
  ring

/-- The ordinary scalar differential expressed through its coordinate partials.-/
def coordinateDifferential {d : ℕ} (g : Fin d → ℂ) : (Fin d → ℂ) →L[ℂ] ℂ :=
  ∑ i : Fin d, g i • ContinuousLinearMap.proj i

@[simp] theorem coordinateDifferential_apply {d : ℕ} (g v : Fin d → ℂ) :
    coordinateDifferential g v = ∑ i, g i * v i := by
  simp [coordinateDifferential, smul_eq_mul]

/-- Every complex linear scalar differential has this coordinate expression.-/
theorem coordinateDifferential_partials {d : ℕ} (D : (Fin d → ℂ) →L[ℂ] ℂ) :
    coordinateDifferential (fun i => D (Pi.single i 1)) = D := by
  ext v
  rw [coordinateDifferential_apply]
  conv_rhs => rw [pi_eq_sum_univ' v]
  simp [map_sum, map_smul, smul_eq_mul, mul_comm]

/-- A scalar coordinate differential restricted to the actual tangent subspace.-/
def restrictedDifferential {d : ℕ} (z g : Fin d → ℂ) : torusTangentSpace z →L[ℂ] ℂ :=
  (∑ i : Fin d, g i • (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d ⊕ Fin d => ℂ) (.inl i))).comp
    (torusTangentSpace z).subtypeL

@[simp] theorem restrictedDifferential_apply {d : ℕ} (z g : Fin d → ℂ)
    (v : torusTangentSpace z) :
    restrictedDifferential z g v = ∑ i, g i * v.val (.inl i) := by
  simp [restrictedDifferential, smul_eq_mul]

/-- Riesz vector in the tangent subspace, not the ambient gradient.-/
def tangentRieszVector {d : ℕ} (z g : Fin d → ℂ) : torusTangentSpace z :=
  ⟨torusTangentMap z (fun i => conj (g i) / (torusWeight z i : ℂ)),
    ⟨_, rfl⟩⟩

/-- The tangent Riesz vector represents the restricted coordinate differential.-/
theorem tangentRieszVector_inner {d : ℕ} (z g : Fin d → ℂ)
    (v : torusTangentSpace z) :
    inner ℂ (tangentRieszVector z g) v = restrictedDifferential z g v := by
  rw [Submodule.coe_inner, PiLp.inner_apply, Fintype.sum_sum_type,
    ← Finset.sum_add_distrib, restrictedDifferential_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hv := (mem_torusTangentSpace_iff z v.val).mp v.property i
  change inner ℂ (conj (g i) / (torusWeight z i : ℂ)) (v.val (.inl i)) +
    inner ℂ (-(z i)⁻¹ ^ 2 * (conj (g i) / (torusWeight z i : ℂ)))
      (v.val (.inr i)) = _
  rw [hv]
  simp only [RCLike.inner_apply', map_mul, map_neg, map_div₀, Complex.conj_conj,
    Complex.conj_ofReal]
  have hw : (1 : ℂ) + conj ((z i)⁻¹ ^ 2) * ((z i)⁻¹ ^ 2) =
      (torusWeight z i : ℂ) := by
    rw [Complex.conj_mul']
    simp [torusWeight, norm_pow, norm_inv, ← pow_mul]
  calc
    _ = ((1 + conj ((z i)⁻¹ ^ 2) * ((z i)⁻¹ ^ 2)) / (torusWeight z i : ℂ)) *
        g i * v.val (.inl i) := by ring
    _ = g i * v.val (.inl i) := by
      rw [hw, div_self (by exact_mod_cast (ne_of_gt (torusWeight_pos z i)))]
      ring

/-- Norm of the tangent Riesz representative.-/
theorem tangentRieszVector_norm_sq {d : ℕ} (z g : Fin d → ℂ) :
    ‖tangentRieszVector z g‖ ^ 2 = differentialNormSq g (torusWeight z) := by
  change ‖torusTangentMap z (fun i => conj (g i) / (torusWeight z i : ℂ))‖ ^ 2 = _
  rw [torusTangentMap_norm_sq]
  unfold differentialNormSq
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_div, Complex.norm_conj, Complex.norm_real,
    Real.norm_of_nonneg (torusWeight_pos z i).le, Complex.normSq_eq_norm_sq]
  field_simp

/-- Identification with the Riesz map on the tangent Hilbert space.-/
theorem restrictedDifferential_eq_innerSL {d : ℕ} (z g : Fin d → ℂ) :
    restrictedDifferential z g = innerSL ℂ (tangentRieszVector z g) := by
  ext v
  exact (tangentRieszVector_inner z g v).symm

/-- Manuscript equation `eq:lambda-formula`, as an operator norm on the
image of the genuine derivative of the proper torus chart.-/
theorem restrictedDifferential_norm_sq {d : ℕ} (z g : Fin d → ℂ) :
    ‖restrictedDifferential z g‖ ^ 2 = differentialNormSq g (torusWeight z) := by
  rw [restrictedDifferential_eq_innerSL, innerSL_apply_norm, tangentRieszVector_norm_sq]

/-- The unsquared differential norm, including the zero differential.-/
theorem restrictedDifferential_norm {d : ℕ} (z g : Fin d → ℂ) :
    ‖restrictedDifferential z g‖ = Real.sqrt (differentialNormSq g (torusWeight z)) := by
  rw [← restrictedDifferential_norm_sq]
  exact (Real.sqrt_sq (norm_nonneg (restrictedDifferential z g))).symm

/-- An ambient differential induces the same scalar differential precisely when
its pullback by the torus chart has the stated coordinate partials.-/
theorem restrictedDifferential_of_pullback {d : ℕ} (z g : Fin d → ℂ)
    (D : TorusAmbient d →L[ℂ] ℂ)
    (hD : D.comp (torusTangentMap z) = coordinateDifferential g) :
    D.comp (torusTangentSpace z).subtypeL = restrictedDifferential z g := by
  ext v
  obtain ⟨w, hw⟩ := v.property
  change D v.val = _
  rw [restrictedDifferential_apply, ← hw]
  simpa using congrArg (fun A : (Fin d → ℂ) →L[ℂ] ℂ => A w) hD

/-- Chain-rule identification for any differentiable ambient extension. The norm
in the conclusion belongs to its restriction to the torus tangent space.-/
theorem restrictedDifferential_of_hasFDerivAt {d : ℕ} {z g : Fin d → ℂ}
    (hz : ∀ i, z i ≠ 0) {F : TorusAmbient d → ℂ} {D : TorusAmbient d →L[ℂ] ℂ}
    (hF : HasFDerivAt F D (torusEmbed z))
    (hf : HasFDerivAt (F ∘ torusEmbed) (coordinateDifferential g) z) :
    D.comp (torusTangentSpace z).subtypeL = restrictedDifferential z g :=
  restrictedDifferential_of_pullback z g D
    ((hF.comp z (torusEmbed_hasFDerivAt hz)).unique hf)

/-- Norm formula for the restriction of an actual ambient derivative.-/
theorem restricted_fderiv_norm_sq {d : ℕ} {z g : Fin d → ℂ}
    (hz : ∀ i, z i ≠ 0) {F : TorusAmbient d → ℂ} {D : TorusAmbient d →L[ℂ] ℂ}
    (hF : HasFDerivAt F D (torusEmbed z))
    (hf : HasFDerivAt (F ∘ torusEmbed) (coordinateDifferential g) z) :
    ‖D.comp (torusTangentSpace z).subtypeL‖ ^ 2 =
      ∑ i, Complex.normSq (g i) / (1 + ‖z i‖⁻¹ ^ 4) := by
  rw [restrictedDifferential_of_hasFDerivAt hz hF hf, restrictedDifferential_norm_sq]
  rfl

end
end DuistermaatVanDerKallen
