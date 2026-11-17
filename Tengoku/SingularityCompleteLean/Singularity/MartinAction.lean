import Tengoku.SingularityCompleteLean.Singularity.MartinBoundary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The group action on the constructed Martin boundary

Normalized precomposition extends left translation of finite poles. Positivity
of the constructed kernels makes the normalizers nonzero, and the resulting
maps are homeomorphisms of the actual abstract Martin boundary.
-/

noncomputable section
open Set
open scoped Topology

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- Normalized precomposition by left multiplication, based at o.-/
def martinTranslate (o g : Γ) (H : Γ → ℝ) : Γ → ℝ :=
  fun z => H (g⁻¹ * z) / H (g⁻¹ * o)

/-- Normalization makes the identity group element act trivially.
@isnad1 id=eq.1h3v.s5.156c5e3063ee from=translated src=- shape=1e089e05 vocab=1e763828
-/
theorem martinTranslate_one (o : Γ) (H : Γ → ℝ) (ho : H o = 1) :
    martinTranslate o 1 H = H := by
  ext z
  simp [martinTranslate, ho]

/-- The normalized maps obey the left-action multiplication law.
@isnad1 id=eq.1h5v.s6.4b40a0c63823 from=translated src=- shape=0bb48c6e vocab=5e4d792c
-/
theorem martinTranslate_mul (o g h : Γ) (H : Γ → ℝ) (hH : H (h⁻¹ * o) ≠ 0) :
    martinTranslate o g (martinTranslate o h H) = martinTranslate o (g * h) H := by
  ext z
  simp only [martinTranslate, mul_inv_rev, mul_assoc]
  exact div_div_div_cancel_right₀ hH _ _

/-- The harmonic equation transforms equivariantly under normalized precomposition.
@isnad1 id=eq.0h7v.s6.2aa8b022dbbc from=translated src=- shape=027001a3 vocab=d04733cd
-/
theorem martinDefect_translate (s : Finset Γ) (μ : Γ → ℝ) (o g z : Γ) (H : Γ → ℝ) :
    martinDefect s μ z (martinTranslate o g H) = martinDefect s μ (g⁻¹ * z) H / H (g⁻¹ * o) := by
  simp only [martinDefect, martinTranslate, sub_div, Finset.sum_div, mul_div_assoc, mul_assoc]

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

include hpos hgen hgap in
/-- The normalized action extends left translation of actual finite-state columns.
@isnad1 id=eq.3h6v.s12.f8fa3523a58f from=translated src=- shape=44a116a0 vocab=2dcf122d
-/
theorem martinTranslate_embedding (o g y : Γ) :
    martinTranslate o g (martinEmbedding s μ o y) = martinEmbedding s μ o (g * y) := by
  ext z
  simp only [martinTranslate, martinEmbedding, martinQuotient]
  rw [div_div_div_cancel_right₀ (walkGreen_ne_zero s μ hpos hgen hgap o y)]
  have hz := walkGreen_left s μ g (g⁻¹ * z) y
  have ho := walkGreen_left s μ g (g⁻¹ * o) y
  simp only [mul_inv_cancel_left] at hz ho
  rw [hz, ho]

include hpos hgen hgap in
/-- The action is continuous wherever the proved coordinate lower bounds apply.
@isnad1 id=continuo.3h5v.s12.d2d3b7284fc8 from=translated src=- shape=c6ca17f0 vocab=20c215c4
-/
theorem continuousOn_martinTranslate (o g : Γ) :
    ContinuousOn (martinTranslate o g) (martinClosure s μ o) := by
  apply continuousOn_pi.mpr
  intro z
  exact (continuous_apply (g⁻¹ * z)).continuousOn.div
    (continuous_apply (g⁻¹ * o)).continuousOn
    (fun H hH => ne_of_gt (martinClosure_pos s μ hpos hgen hgap o hH (g⁻¹ * o)))

include hpos hgen hgap in
/-- The action preserves the compactification carrier.
@isnad1 id=mem.4h6v.s12.84ba7c90c69a from=translated src=- shape=7a31b88d vocab=406cc8c6
-/
theorem martinTranslate_mem_closure (o g : Γ) {H : Γ → ℝ}
    (hH : H ∈ martinClosure s μ o) : martinTranslate o g H ∈ martinClosure s μ o := by
  have hm : MapsTo (martinTranslate o g) (range (martinEmbedding s μ o))
      (range (martinEmbedding s μ o)) := by
    rintro f ⟨y, rfl⟩
    exact ⟨g * y, (martinTranslate_embedding s μ hpos hgen hgap o g y).symm⟩
  exact hm.closure_of_continuousOn (continuousOn_martinTranslate s μ hpos hgen hgap o g) hH

include hpos hgen hgap in
/-- Harmonicity and closure membership show that the abstract boundary is preserved.
@isnad1 id=mem.4h6v.s12.b6a5355ad2f1 from=translated src=- shape=7a31b88d vocab=918b00c1
-/
theorem martinTranslate_mem_boundary (o g : Γ) {H : Γ → ℝ}
    (hH : H ∈ martinBoundary s μ o) : martinTranslate o g H ∈ martinBoundary s μ o := by
  apply (martinBoundary_iff_harmonic s μ hpos hgen hgap o _).mpr
  refine ⟨martinTranslate_mem_closure s μ hpos hgen hgap o g hH.1, ?_⟩
  intro z
  rw [martinDefect_translate,
    ((martinBoundary_iff_harmonic s μ hpos hgen hgap o H).mp hH).2, zero_div]

/-- A group element acts on the actual subtype of Martin-boundary points.-/
def martinBoundaryMap (o g : Γ) (ξ : martinBoundary s μ o) : martinBoundary s μ o :=
  ⟨martinTranslate o g ξ.val, martinTranslate_mem_boundary s μ hpos hgen hgap o g ξ.property⟩

/--
@isnad1 id=eq.3h5v.s12.368aee6079c1 from=translated src=- shape=fa134038 vocab=33561846
-/
theorem martinBoundaryMap_one (o : Γ) (ξ : martinBoundary s μ o) :
    martinBoundaryMap s μ hpos hgen hgap o 1 ξ = ξ := by
  apply Subtype.ext
  exact martinTranslate_one o ξ.val (martinClosure_base s μ hpos hgen hgap o ξ.property.1)

/--
@isnad1 id=eq.3h7v.s12.4af43438bcbf from=translated src=- shape=38a8f126 vocab=47b03b9a
-/
theorem martinBoundaryMap_mul (o g h : Γ) (ξ : martinBoundary s μ o) :
    martinBoundaryMap s μ hpos hgen hgap o g (martinBoundaryMap s μ hpos hgen hgap o h ξ) =
      martinBoundaryMap s μ hpos hgen hgap o (g * h) ξ := by
  apply Subtype.ext
  exact martinTranslate_mul o g h ξ.val
    (ne_of_gt (martinClosure_pos s μ hpos hgen hgap o ξ.property.1 (h⁻¹ * o)))

/--
@isnad1 id=continuo.3h5v.s12.20fb94985087 from=translated src=- shape=ce8bce10 vocab=74f1077f
-/
theorem continuous_martinBoundaryMap (o g : Γ) :
    Continuous (martinBoundaryMap s μ hpos hgen hgap o g) := by
  apply Continuous.subtype_mk
  exact ((continuousOn_martinTranslate s μ hpos hgen hgap o g).mono
    (fun _ h => h.1)).domRestrict

/-- Every group element acts by a homeomorphism, with inverse given by its group inverse.-/
def martinBoundaryHomeomorph (o g : Γ) : martinBoundary s μ o ≃ₜ martinBoundary s μ o where
  toFun := martinBoundaryMap s μ hpos hgen hgap o g
  invFun := martinBoundaryMap s μ hpos hgen hgap o g⁻¹
  left_inv ξ := by rw [martinBoundaryMap_mul, inv_mul_cancel, martinBoundaryMap_one]
  right_inv ξ := by rw [martinBoundaryMap_mul, mul_inv_cancel, martinBoundaryMap_one]
  continuous_toFun := continuous_martinBoundaryMap s μ hpos hgen hgap o g
  continuous_invFun := continuous_martinBoundaryMap s μ hpos hgen hgap o g⁻¹

/-- The verified maps form an actual group action on the abstract boundary.-/
@[instance_reducible]
def martinBoundaryMulAction (o : Γ) : MulAction Γ (martinBoundary s μ o) where
  smul g ξ := martinBoundaryMap s μ hpos hgen hgap o g ξ
  one_smul := martinBoundaryMap_one s μ hpos hgen hgap o
  mul_smul g h ξ := (martinBoundaryMap_mul s μ hpos hgen hgap o g h ξ).symm

/-- The positive normalization factor for the boundary action.-/
def martinBoundaryCocycle (o g : Γ) (ξ : martinBoundary s μ o) : ℝ :=
  martinBoundaryKernel s μ o (g⁻¹ * o) ξ

omit [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] in
/--
@isnad1 id=continuo.0h5v.s6.090b70e18618 from=translated src=- shape=30b91784 vocab=1e03d432
-/
theorem continuous_martinBoundaryCocycle (o g : Γ) : Continuous (martinBoundaryCocycle s μ o g) :=
  continuous_martinBoundaryKernel s μ o (g⁻¹ * o)

end Singularity
