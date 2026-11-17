import Tengoku.SingularityCompleteLean.Singularity.MartinBoundary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite points and escaping approximation of the Martin boundary

Finite poles are isolated in the constructed compactification. Every boundary
point is approached by a sequence of finite poles escaping each fixed state.
For an infinite group the boundary is nonempty.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- A finite state regarded as an actual point of the compactification.-/
def martinFinitePoint (s : Finset Γ) (μ : Γ → ℝ) (o y : Γ) : martinClosure s μ o :=
  ⟨martinEmbedding s μ o y, martinEmbedding_mem_closure s μ o y⟩

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

omit [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] in
include hgen in
/-- Every abstract boundary point has a finite-pole approximation escaping every state.
@isnad1 id=ex.1h5v.s7.3b874d22d419 from=translated src=- shape=b2937aca vocab=0d1db57d
-/
theorem martinBoundary_escaping_approximation (o : Γ) (ξ : martinBoundary s μ o) :
    ∃ y : ℕ → Γ, (∀ z, ∀ᶠ n in atTop, z ≠ y n) ∧
      ∀ z, Tendsto (fun n => martinQuotient s μ o z (y n)) atTop (𝓝 (martinBoundaryKernel s μ o z ξ)) := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  obtain ⟨f, hf, ht⟩ := mem_closure_iff_seq_limit.mp ξ.property.1
  choose y hy using hf
  have he : (fun n => martinEmbedding s μ o (y n)) = f := funext hy
  have ht' : Tendsto (fun n => martinEmbedding s μ o (y n)) atTop (𝓝 ξ.val) := by
    rw [he]
    exact ht
  refine ⟨y, ?_, tendsto_pi_nhds.mp ht'⟩
  intro z
  have hne : ξ.val ≠ martinEmbedding s μ o z := fun h => ξ.property.2 ⟨z, h.symm⟩
  have hopen : IsOpen {H : Γ → ℝ | H ≠ martinEmbedding s μ o z} :=
    isOpen_ne_fun continuous_id continuous_const
  have hev := ht'.eventually (hopen.mem_nhds hne)
  filter_upwards [hev] with n hn
  intro hzn
  exact hn (by rw [← hzn])

include hpos hgen hgap in
/-- A pointwise harmonic limit of finite columns belongs to the actual Martin boundary.
@isnad1 id=mem.5h8v.s12.75041963edff from=translated src=- shape=3e9b1a12 vocab=8925f8bc
-/
theorem martin_limit_mem_boundary {α : Type*} {l : Filter α} [l.NeBot]
    (o : Γ) (y : α → Γ) (H : Γ → ℝ)
    (hescape : ∀ z, ∀ᶠ n in l, z ≠ y n)
    (hpoint : ∀ z, Tendsto (fun n => martinQuotient s μ o z (y n)) l (𝓝 (H z))) :
    H ∈ martinBoundary s μ o := by
  apply (martinBoundary_iff_harmonic s μ hpos hgen hgap o H).mpr
  constructor
  · exact mem_closure_of_tendsto (tendsto_pi_nhds.mpr hpoint)
      (Eventually.of_forall (fun n => ⟨y n, rfl⟩))
  · intro z
    exact sub_eq_zero.mpr (martin_limit_harmonic s μ hgap o y H hescape hpoint z)

end Singularity
