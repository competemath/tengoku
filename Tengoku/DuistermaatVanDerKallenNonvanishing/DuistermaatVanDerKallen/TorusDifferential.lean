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

/--
@isnad1 id=eq.0h4v.s9.6b7699fecc71 from=translated src=- shape=4f1e62a9 vocab=e5d0942b
-/
@[simp] theorem torusTangentMap_left {d : ℕ} (z v : Fin d → ℂ) (i : Fin d) :
    torusTangentMap z v (.inl i) = v i := rfl

/--
@isnad1 id=eq.0h4v.s9.df2c7d3fbeb6 from=translated src=- shape=b9a36567 vocab=468bdf87
-/
@[simp] theorem torusTangentMap_right {d : ℕ} (z v : Fin d → ℂ) (i : Fin d) :
    torusTangentMap z v (.inr i) = -(z i)⁻¹ ^ 2 * v i := rfl

/-- The chart derivative is computed over ℂ at every point of the open torus.
@isnad1 id=hasfderi.1h2v.s7.9e422599a437 from=translated src=- shape=7cc6652e vocab=15c7be31
-/
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

/-- The nonvanishing-coordinate chart domain is open.
@isnad1 id=isopen.0h1v.s5.1010caadab99 from=translated src=- shape=eeccade8 vocab=e153a78e
-/
theorem torusDomain_isOpen (d : ℕ) :
    IsOpen {z : Fin d → ℂ | ∀ i, z i ≠ 0} := by
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_ne_fun (continuous_apply i) continuous_const

/-- The global chart is smooth over ℝ, as needed by real ODE theory.
@isnad1 id=contdiff.1h2v.s7.5eab9f6f9415 from=translated src=- shape=85fd8419 vocab=7cfed2dc
-/
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

/--
@isnad1 id=iff.0h3v.s9.8c2b204e3e04 from=translated src=- shape=ca0f673b vocab=4e2e83e0
-/
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
equations `zᵢwᵢ = 1`, so it is the tangent space of the affine variety.
@isnad1 id=iff.1h3v.s9.a6b3854532da from=translated src=- shape=b7ddd314 vocab=5c8d35bb
-/
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

/--
@isnad1 id=lt.0h3v.s4.492cc87dfc89 from=translated src=- shape=beb0885f vocab=1919341c
-/
theorem torusWeight_pos {d : ℕ} (z : Fin d → ℂ) (i : Fin d) :
    0 < torusWeight z i := torus_weight_pos _

/-- Manuscript equation `eq:embedding-metric`.
@isnad1 id=eq.0h3v.s9.a3404673d582 from=translated src=- shape=3a6df293 vocab=2fc4cadf
-/
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

/--
@isnad1 id=eq.0h3v.s7.e629f8b7472c from=translated src=- shape=622bf701 vocab=5b29e72b
-/
@[simp] theorem coordinateDifferential_apply {d : ℕ} (g v : Fin d → ℂ) :
    coordinateDifferential g v = ∑ i, g i * v i := by
  simp [coordinateDifferential, smul_eq_mul]

/-- Every complex linear scalar differential has this coordinate expression.
@isnad1 id=eq.0h2v.s8.cb7413294c55 from=translated src=- shape=f771a07a vocab=489be706
-/
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

/--
@isnad1 id=eq.0h4v.s11.cba8e5818a7a from=translated src=- shape=7ad4fce0 vocab=8faa212c
-/
@[simp] theorem restrictedDifferential_apply {d : ℕ} (z g : Fin d → ℂ)
    (v : torusTangentSpace z) :
    restrictedDifferential z g v = ∑ i, g i * v.val (.inl i) := by
  simp [restrictedDifferential, smul_eq_mul]

/-- Riesz vector in the tangent subspace, not the ambient gradient.-/
def tangentRieszVector {d : ℕ} (z g : Fin d → ℂ) : torusTangentSpace z :=
  ⟨torusTangentMap z (fun i => conj (g i) / (torusWeight z i : ℂ)),
    ⟨_, rfl⟩⟩

/-- The tangent Riesz vector represents the restricted coordinate differential.
@isnad1 id=eq.0h4v.s12.f538779920ea from=translated src=- shape=3d7bf4ef vocab=2afd1164
-/
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

/-- Norm of the tangent Riesz representative.
@isnad1 id=eq.0h3v.s9.e718ad4a2e24 from=translated src=- shape=0b8a83bd vocab=692b4001
-/
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

/-- Identification with the Riesz map on the tangent Hilbert space.
@isnad1 id=eq.0h3v.s15.a29f0447de64 from=translated src=- shape=67dd2f08 vocab=bfb44aab
-/
theorem restrictedDifferential_eq_innerSL {d : ℕ} (z g : Fin d → ℂ) :
    restrictedDifferential z g = innerSL ℂ (tangentRieszVector z g) := by
  ext v
  exact (tangentRieszVector_inner z g v).symm

/-- Manuscript equation `eq:lambda-formula`, as an operator norm on the
image of the genuine derivative of the proper torus chart.
@isnad1 id=eq.0h3v.s10.b69a200d0d4a from=translated src=- shape=0612e3e8 vocab=6190b367
-/
theorem restrictedDifferential_norm_sq {d : ℕ} (z g : Fin d → ℂ) :
    ‖restrictedDifferential z g‖ ^ 2 = differentialNormSq g (torusWeight z) := by
  rw [restrictedDifferential_eq_innerSL, innerSL_apply_norm, tangentRieszVector_norm_sq]

/-- The unsquared differential norm, including the zero differential.
@isnad1 id=eq.0h3v.s10.7345e5666a78 from=translated src=- shape=da4d2556 vocab=1ca4674e
-/
theorem restrictedDifferential_norm {d : ℕ} (z g : Fin d → ℂ) :
    ‖restrictedDifferential z g‖ = Real.sqrt (differentialNormSq g (torusWeight z)) := by
  rw [← restrictedDifferential_norm_sq]
  exact (Real.sqrt_sq (norm_nonneg (restrictedDifferential z g))).symm

/-- An ambient differential induces the same scalar differential precisely when
its pullback by the torus chart has the stated coordinate partials.
@isnad1 id=eq.1h4v.s11.19fccb119d08 from=translated src=- shape=35307bd4 vocab=594966ee
-/
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
in the conclusion belongs to its restriction to the torus tangent space.
@isnad1 id=eq.3h5v.s11.c34074db2884 from=translated src=- shape=22d2ac01 vocab=4395f3ea
-/
theorem restrictedDifferential_of_hasFDerivAt {d : ℕ} {z g : Fin d → ℂ}
    (hz : ∀ i, z i ≠ 0) {F : TorusAmbient d → ℂ} {D : TorusAmbient d →L[ℂ] ℂ}
    (hF : HasFDerivAt F D (torusEmbed z))
    (hf : HasFDerivAt (F ∘ torusEmbed) (coordinateDifferential g) z) :
    D.comp (torusTangentSpace z).subtypeL = restrictedDifferential z g :=
  restrictedDifferential_of_pullback z g D
    ((hF.comp z (torusEmbed_hasFDerivAt hz)).unique hf)

/-- Norm formula for the restriction of an actual ambient derivative.
@isnad1 id=eq.3h5v.s11.6b1e5a11855b from=translated src=- shape=24b17169 vocab=1c825a12
-/
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
