import Tengoku.Nlalib.NLAlib.Polynomial.BestApproximation.RootSampleLower
import Tengoku.Nlalib.NLAlib.Polynomial.BestApproximation.LebesgueAffine
import Tengoku.Nlalib.NLAlib.ForMathlib.LinearAlgebra.LagrangeReindex
import Tengoku.Seed.Order.Fin.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # A canonical reference grid with all peaks above the sharp lower constant

Reverse the Chebyshev root grid, stretch its extreme hull to the unit interval,
and transplant the explicit finite gap witnesses. This is the concrete reference
configuration consumed by the global peak comparison.
-/
noncomputable section
open Real Set Polynomial Finset
namespace NLAlib

/-- Reindexing a finite grid preserves its actual Lebesgue function.
Source: the finite Lagrange cardinal product; reference-grid helper.
@isnad1 id=eq.0h5v.s5.f7af5057212c from=translated src=- shape=94edaf22 vocab=7dd11f8b
-/
theorem lebesgueFunction_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (v : ι → ℝ) (e : κ ≃ ι) (x : ℝ) :
    lebesgueFunction (v ∘ e) x = lebesgueFunction v x := by
  unfold lebesgueFunction
  simp_rw [lagrange_basis_univ_comp_equiv]
  exact e.sum_comp (fun i => |(Lagrange.basis univ v i).eval x|)

/-- The actual Chebyshev zeros strictly decrease with their indices.
Source: the root-angle formula and strict cosine monotonicity.
@isnad1 id=strictan.0h1v.s3.118c26b49c6d from=translated src=- shape=64d36d98 vocab=f134e096
-/
theorem strictAnti_chebyshevZero (N : ℕ) : StrictAnti (chebyshevZero N) := by
  intro i j hij
  have hNR : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hθi := chebyshev_root_angle_mem_Ioo i
  have hθj := chebyshev_root_angle_mem_Ioo j
  rw [chebyshevZero_eq_cos_half_index, chebyshevZero_eq_cos_half_index]
  apply strictAntiOn_cos ⟨hθi.1.le, hθi.2.le⟩ ⟨hθj.1.le, hθj.2.le⟩
  apply div_lt_div_of_pos_right _ hNR
  apply mul_lt_mul_of_pos_right _ pi_pos
  have hijR : (i : ℝ) < j := by exact_mod_cast hij
  linarith

/-- A stretched, increasing Chebyshev-root grid is a concrete canonical node
configuration whose every gap peak exceeds the sharp universal logarithmic constant.
Source: focused reroutes, the reference-grid input to Bernstein–Erdős peak comparison.
The construction includes the zero-dimensional two-node case.
@isnad1 id=ex.0h1v.s7.91a4085909f2 from=translated src=- shape=5b9324a8 vocab=776ce977
-/
theorem exists_canonical_reference_grid_logarithmic_lower_lt_peaks (n : ℕ) :
    ∃ t ∈ interiorNodeSimplex n, ∀ i : Fin (n + 1),
      (2 / π) * (log (n + 2 : ℕ) + eulerMascheroniConstant + log (4 / π)) <
        interpolationGapPeak n t i := by
  let v : Fin (n + 2) → ℝ := fun j => chebyshevZero (n + 2) j.rev
  have hv : StrictMono v := by
    intro i j hij
    exact strictAnti_chebyshevZero (n + 2) (Fin.rev_strictAnti hij)
  obtain ⟨t, ht, α, hα, β, hrep⟩ := exists_canonical_nodes_affine v hv
  refine ⟨t, ht, fun i => ?_⟩
  let k := n + 1 - (i : ℕ)
  have hk0 : 1 ≤ k := by dsimp [k]; omega
  have hkN : k < n + 2 := by dsimp [k]; omega
  obtain ⟨y, hy, hbound⟩ := exists_mem_chebyshevZero_gap_logarithmic_lower_lt
    (show 2 ≤ n + 2 by omega) hk0 hkN
  have hleft : v i.castSucc = chebyshevZero (n + 2) ⟨k, hkN⟩ := by
    change chebyshevZero (n + 2) i.castSucc.rev = _
    apply congrArg (chebyshevZero (n + 2))
    apply Fin.ext
    simp only [Fin.val_rev, Fin.val_castSucc]
    dsimp [k]
    omega
  have hright : v i.succ = chebyshevZero (n + 2) ⟨k - 1, by omega⟩ := by
    change chebyshevZero (n + 2) i.succ.rev = _
    apply congrArg (chebyshevZero (n + 2))
    apply Fin.ext
    simp only [Fin.val_rev, Fin.val_succ]
    dsimp [k]
    omega
  have hyv : y ∈ Ioo (v i.castSucc) (v i.succ) := by rwa [hleft, hright]
  let z := (y - β) / α
  have hz : z ∈ Icc (canonicalIntervalNodes n t i.castSucc) (canonicalIntervalNodes n t i.succ) := by
    have hL := hrep i.castSucc
    have hR := hrep i.succ
    constructor
    · apply (le_div_iff₀ hα).mpr
      linarith [hyv.1]
    · apply (div_le_iff₀ hα).mpr
      linarith [hyv.2]
  have hleb : lebesgueFunction (canonicalIntervalNodes n t) z = lebesgueFunction (chebyshevZero (n + 2)) y := by
    have hnodes : (fun j => α * canonicalIntervalNodes n t j + β) = v := funext hrep
    have heq : α * z + β = y := by dsimp [z]; field_simp; ring
    have h := lebesgueFunction_affine (canonicalIntervalNodes n t) z α β hα.ne'
    rw [hnodes, heq] at h
    have hreindex := lebesgueFunction_comp_equiv (chebyshevZero (n + 2)) Fin.revPerm y
    change lebesgueFunction v y = lebesgueFunction (chebyshevZero (n + 2)) y at hreindex
    exact h.symm.trans hreindex
  calc
    _ < lebesgueFunction (canonicalIntervalNodes n t) z := by rw [hleb]; exact hbound
    _ ≤ interpolationGapPeak n t i := lebesgueFunction_le_lebesgueConstant _ hz

end NLAlib
