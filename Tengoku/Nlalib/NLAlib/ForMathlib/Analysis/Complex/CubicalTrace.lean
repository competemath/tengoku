import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Complex.CubicalCauchy
import Tengoku.Seed.Topology.Order.Compact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The compact trace and actual maximum norm of a finite contour chain

The trace is the finite union of the images of its active continuous edges.
The maximum norm uses zero for the empty chain and is an actual attained
maximum on every nonempty trace. Corners and stationary points are allowed.
-/

noncomputable section
open Set Finset
open scoped unitInterval
namespace Complex

/-- The actual ambient trace of all nonzero edges in a finite signed chain.-/
def cubicalTrace {Ω : Set ℂ} (Γ : Cubical.OneChain Ω) : Set ℂ :=
  ⋃ γ ∈ Γ.support, range (fun r : I => (γ r : ℂ))

/-- Every point of an active edge belongs to the actual contour trace.
@isnad1 id=mem.1h4v.s9.7962f15c1b55 from=translated src=- shape=0fd03d2e vocab=3525692c
-/
theorem mem_cubicalTrace {Ω : Set ℂ} {Γ : Cubical.OneChain Ω}
    {γ : C(I, Ω)} (hγ : γ ∈ Γ.support) (r : I) : (γ r : ℂ) ∈ cubicalTrace Γ := by
  exact mem_iUnion.mpr ⟨γ, mem_iUnion.mpr ⟨hγ, mem_range_self r⟩⟩

/-- The actual trace is compact, without any differentiability requirement.
@isnad1 id=iscompac.0h2v.s5.d81ac5a479ce from=translated src=- shape=0a46c1c8 vocab=23cf46bf
-/
theorem isCompact_cubicalTrace {Ω : Set ℂ} (Γ : Cubical.OneChain Ω) :
    IsCompact (cubicalTrace Γ) :=
  Γ.support.isCompact_biUnion (fun γ _ =>
    isCompact_range (continuous_subtype_val.comp γ.continuous))

/-- The trace of a chain in a domain lies in that actual domain.
@isnad1 id=le.0h2v.s5.1753e7885061 from=translated src=- shape=fcde88ce vocab=c7ad73b2
-/
theorem cubicalTrace_subset {Ω : Set ℂ} (Γ : Cubical.OneChain Ω) : cubicalTrace Γ ⊆ Ω := by
  intro z hz
  obtain ⟨γ, hz⟩ := mem_iUnion.mp hz
  obtain ⟨_, r, rfl⟩ := mem_iUnion.mp hz
  exact (γ r).property

/-- The actual maximum norm on the compact contour trace, with value zero
for the empty trace. Continuity on the trace ensures finiteness and attainment.-/
def cubicalMaxNorm {Ω : Set ℂ} (Γ : Cubical.OneChain Ω) (f : ℂ → ℂ) : ℝ :=
  sSup (insert 0 ((fun z => ‖f z‖) '' cubicalTrace Γ))

private theorem bddAbove_insert_norm_image_cubicalTrace {Ω : Set ℂ}
    (Γ : Cubical.OneChain Ω) {f : ℂ → ℂ} (hf : ContinuousOn f (cubicalTrace Γ)) :
    BddAbove (insert 0 ((fun z => ‖f z‖) '' cubicalTrace Γ)) :=
  bddAbove_insert.mpr ((isCompact_cubicalTrace Γ).bddAbove_image hf.norm)

/-- The actual maximum norm is nonnegative, including an empty contour.
@isnad1 id=le.1h3v.s6.a0e5854f0be0 from=translated src=- shape=3bf26a8e vocab=a5de82c3
-/
theorem cubicalMaxNorm_nonneg {Ω : Set ℂ} (Γ : Cubical.OneChain Ω)
    {f : ℂ → ℂ} (hf : ContinuousOn f (cubicalTrace Γ)) : 0 ≤ cubicalMaxNorm Γ f :=
  le_csSup (bddAbove_insert_norm_image_cubicalTrace Γ hf) (mem_insert 0 _)

/-- The actual maximum norm bounds every integrand value on the trace.
@isnad1 id=le.2h4v.s6.d84a57d0ff65 from=translated src=- shape=0cb6cc30 vocab=2a616aff
-/
theorem norm_le_cubicalMaxNorm {Ω : Set ℂ} (Γ : Cubical.OneChain Ω)
    {f : ℂ → ℂ} (hf : ContinuousOn f (cubicalTrace Γ)) {z : ℂ} (hz : z ∈ cubicalTrace Γ) :
    ‖f z‖ ≤ cubicalMaxNorm Γ f :=
  le_csSup (bddAbove_insert_norm_image_cubicalTrace Γ hf) (mem_insert_of_mem 0 (mem_image_of_mem _ hz))

/-- On every nonempty contour trace the maximum norm is attained at an
actual point of the trace.
@isnad1 id=ex.2h3v.s6.00906976e65a from=translated src=- shape=29c9db76 vocab=07a840a0
-/
theorem exists_norm_eq_cubicalMaxNorm {Ω : Set ℂ} (Γ : Cubical.OneChain Ω)
    {f : ℂ → ℂ} (hf : ContinuousOn f (cubicalTrace Γ)) (hΓ : (cubicalTrace Γ).Nonempty) :
    ∃ z ∈ cubicalTrace Γ, ‖f z‖ = cubicalMaxNorm Γ f := by
  obtain ⟨z, hz, hmax⟩ := (isCompact_cubicalTrace Γ).exists_isMaxOn hΓ hf.norm
  refine ⟨z, hz, le_antisymm (norm_le_cubicalMaxNorm Γ hf hz) ?_⟩
  unfold cubicalMaxNorm
  apply csSup_le (Set.insert_nonempty 0 _)
  intro v hv
  rcases mem_insert_iff.mp hv with rfl | hv
  · exact norm_nonneg _
  · obtain ⟨w, hw, rfl⟩ := hv
    exact hmax hw

end Complex
