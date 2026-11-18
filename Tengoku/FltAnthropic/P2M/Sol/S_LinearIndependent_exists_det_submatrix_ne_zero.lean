import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LinearIndependent_exists_det_submatrix_ne_zero.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LinearIndependent_exists_det_submatrix_ne_zero

set_option autoImplicit false
open Matrix

namespace FltWs24
namespace Cart

section Field
variable {k : Type*} [Field k] {ι : Type*} {n : ℕ}

def colAt (f : Fin n → ι → k) (i : ι) : Fin n → k := fun j => f j i

theorem span_range_colAt_eq_top (f : Fin n → ι → k) (hf : LinearIndependent k f) :
    Submodule.span k (Set.range (colAt f)) = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)

  set c : Fin n → k := fun j => φ (Pi.single j 1) with hc
  have hφ : ∀ v : Fin n → k, φ v = ∑ j, v j * c j := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ φ v]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul]
    congr 2
    ext i
    simp [Pi.single_apply, eq_comm]

  have hsum : ∑ j, c j • f j = 0 := by
    ext i
    have hi : φ (colAt f i) = 0 := hle (Submodule.subset_span ⟨i, rfl⟩)
    rw [hφ] at hi
    simpa [colAt, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using hi
  have hc0 : ∀ j, c j = 0 := Fintype.linearIndependent_iff.mp hf c hsum
  apply hφ0
  apply LinearMap.pi_ext'
  intro j
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single, LinearMap.zero_comp,
    LinearMap.zero_apply]
  have := hc0 j
  simp only [hc] at this
  simpa using this

theorem exists_submatrix_det_ne_zero_of_linearIndependent (f : Fin n → ι → k) (hf : LinearIndependent k f) :
    ∃ s : Fin n → ι, Function.Injective s ∧ (Matrix.of fun l j => f j (s l)).det ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' k (colAt f)
  rw [span_range_colAt_eq_top f hf] at hspan

  let b : Module.Basis κ k (Fin n → k) := Module.Basis.mk hli (by rw [hspan])
  let e : Fin n ≃ κ := (b.indexEquiv (Pi.basisFun k (Fin n))).symm
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩

  have hrows : LinearIndependent k (Matrix.of fun l j => f j ((a ∘ e) l)).row := by
    have h2 : LinearIndependent k (colAt f ∘ a ∘ e) := (hli.comp e e.injective)
    convert h2 using 1
    rfl
  have hU : IsUnit (Matrix.of fun l j => f j ((a ∘ e) l)) := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hU).ne_zero

end Field

section LocalRing
variable {A : Type*} [CommRing A] [IsLocalRing A] {ι : Type*} {n : ℕ}

end LocalRing

end FltWs24.Cart

theorem solution
    {k : Type*} [Field k] {ι : Type*} {n : ℕ}
    (f : Fin n → ι → k) (hf : LinearIndependent k f) :
    ∃ s : Fin n → ι, Function.Injective s ∧ (Matrix.of fun l j => f j (s l)).det ≠ 0 :=
  FltWs24.Cart.exists_submatrix_det_ne_zero_of_linearIndependent f hf
