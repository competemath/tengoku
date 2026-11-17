import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_isReduced_of_mem_nonZeroDivisors_of_isReduced_basicOpen

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_isIntegral_of_mem_nonZeroDivisors_of_isIntegral_basicOpen.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_isIntegral_of_mem_nonZeroDivisors_of_isIntegral_basicOpen

set_option autoImplicit false

open _root_.CategoryTheory open _root_.CategoryTheory.Limits open _root_.AlgebraicGeometry open _root_.TopologicalSpace open _root_.Opposite

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.basicOpen_res basicOpen_eq_bot_iff Scheme.Opens.range_ι Spec IsIntegral Scheme IsReduced Scheme.isBasis_affineOpens IsAffineOpen Scheme.Opens isIntegral_of_irreducibleSpace_of_isReduced isReduced_of_mem_nonZeroDivisors_of_isReduced_basicOpen)
namespace IntegralBasicOpen
open _root_.AlgebraicGeometry

/--
@isnad1 id=nonempty.3h4v.s11.447ba01c95c4 from=translated src=- shape=73d2c0f7 vocab=686d0f4c
-/
theorem basicOpen_nonempty_of_mem_nonZeroDivisors {Y : Scheme} {U : Y.Opens} (hU : IsAffineOpen U)
    {x : Y} (hx : x ∈ U) (f : Γ(Y, U)) (hf : f ∈ nonZeroDivisors Γ(Y, U)) :
    ((Y.basicOpen f : Y.Opens) : Set Y).Nonempty := by
  classical

  haveI : Nontrivial Γ(Y, U) := (Y.presheaf.germ U x hx).hom.domain_nontrivial

  have hnil : ¬ IsNilpotent f := by
    rintro ⟨n, hn⟩
    have h := pow_mem hf n
    rw [hn] at h
    exact zero_notMem_nonZeroDivisors h

  have hne : PrimeSpectrum.basicOpen f ≠ ⊥ := by
    rwa [Ne, PrimeSpectrum.basicOpen_eq_bot_iff]
  have hne' : ((PrimeSpectrum.basicOpen f : Opens (PrimeSpectrum Γ(Y, U))) : Set (PrimeSpectrum Γ(Y, U))).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr fun h => hne (Opens.coe_eq_empty.mp h)
  obtain ⟨q, hq⟩ := hne'
  refine ⟨hU.fromSpec.base q, ?_⟩
  rw [← hU.fromSpec_image_basicOpen f]
  exact ⟨q, hq, rfl⟩

/--
@isnad1 id=dense.1h2v.s12.a56cf76a6f7e from=translated src=- shape=d3e823fc vocab=96dbad99
-/
theorem dense_basicOpen_of_mem_nonZeroDivisors {Y : Scheme} (p : Γ(Y, ⊤))
    (hreg : ∀ U : Y.Opens, IsAffineOpen U → Y.presheaf.map (homOfLE le_top).op p ∈ nonZeroDivisors Γ(Y, U)) :
    Dense ((Y.basicOpen p : Y.Opens) : Set Y) := by
  rw [dense_iff_inter_open]
  intro W hW ⟨x, hx⟩

  obtain ⟨U, hUaff, hxU, hUW⟩ := (Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Y)) (show x ∈ (⟨W, hW⟩ : Opens Y) from hx)
  have hU : IsAffineOpen U := hUaff

  obtain ⟨y, hy⟩ := basicOpen_nonempty_of_mem_nonZeroDivisors hU hxU _ (hreg U hU)
  rw [Scheme.basicOpen_res] at hy
  exact ⟨y, hUW hy.1, hy.2⟩

end AlgebraicGeometry.IntegralBasicOpen

open AlgebraicGeometry.IntegralBasicOpen in

/--
@isnad1 id=isintegr.1h2v.s12.46cfb5b6b526 from=translated src=- shape=23272e67 vocab=b8393f97
-/
theorem solution {Y : Scheme} (p : Γ(Y, ⊤))
    (hreg : ∀ U : Y.Opens, IsAffineOpen U → Y.presheaf.map (homOfLE le_top).op p ∈ nonZeroDivisors Γ(Y, U))
    [hint : IsIntegral (Y.basicOpen p : Scheme)] : IsIntegral Y := by
  haveI : IsReduced Y := AlgebraicGeometry.isReduced_of_mem_nonZeroDivisors_of_isReduced_basicOpen p hreg
  have hirr : IsIrreducible ((Y.basicOpen p : Y.Opens) : Set Y) := by
    rw [← Scheme.Opens.range_ι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (Y.basicOpen p).ι.base.hom.continuous.continuousOn
  haveI : IrreducibleSpace Y := by
    have h := hirr.closure
    rw [(dense_basicOpen_of_mem_nonZeroDivisors p hreg).closure_eq] at h
    exact (irreducibleSpace_def Y).mpr h
  exact isIntegral_of_irreducibleSpace_of_isReduced Y
