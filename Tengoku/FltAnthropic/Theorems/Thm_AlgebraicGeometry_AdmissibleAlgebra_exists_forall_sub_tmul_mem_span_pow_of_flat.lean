import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_AdmissibleAlgebra_exists_forall_sub_tmul_mem_span_pow_of_flat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_AdmissibleAlgebra_exists_forall_sub_tmul_mem_span_pow_of_flat.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open TensorProduct

/--
@isnad1 id=ex.6h4v.s14.f3fbe1754371 from=translated src=- shape=ae15f711 vocab=159fef2e
-/
theorem AlgebraicGeometry.AdmissibleAlgebra.exists_forall_sub_tmul_mem_span_pow_of_flat
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (R : Type) [CommRing R] [Algebra 𝒪 R]
    (hRc : IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R)
    (hRtf : ∀ x : R, algebraMap 𝒪 R π * x = 0 → x = 0)
    (hRft : Algebra.FiniteType 𝒪 (R ⧸ Ideal.span {algebraMap 𝒪 R π}))
    (G : Type) [Group G] [Finite G] [MulSemiringAction G R] [SMulCommClass G 𝒪 R] :
    ∃ e : ℕ, ∀ (A' : Type) [CommRing A'] [Algebra ↥(FixedPoints.subalgebra 𝒪 R G) A']
      [Module.Flat ↥(FixedPoints.subalgebra 𝒪 R G) A']
      (ρ : G → (R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A' →+ R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A'))
      (_hρ : ∀ (g : G) (r : R) (s : A'), ρ g (r ⊗ₜ s) = (g • r) ⊗ₜ s)
      (m : ℕ) (x : R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A'),
      (∀ g : G, ρ g x - x ∈ Ideal.span {(algebraMap 𝒪 R π ^ (m + e)) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')}) →
      ∃ w : A', x - (1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w ∈
        Ideal.span {(algebraMap 𝒪 R π ^ m) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')} := by exact @_root_.P2MW.S_AlgebraicGeometry_AdmissibleAlgebra_exists_forall_sub_tmul_mem_span_pow_of_flat.solution 𝒪 _ _ hdvr π hπ hcomplete R _ _ hRc hRtf hRft G _ _ _ _
