import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
U1 — REGISTRAZIONE DIMENSION-FREE (branch platonici-unicita-registration, 20 lug 2026).

Generalizza `isometria_da_gram` (Registro.lean, `E 3`) a dimensione arbitraria `E n`:
due famiglie di vettori con la STESSA matrice di Gram e span pieno sono legate da una
isometria lineare che le registra vettore per vettore.  La prova è dimension-free
(combinazioni lineari finite, uguaglianza dei kernel, `isometryOfInner`); `E 3` era
usato solo come tipo.  Infrastruttura per l'unicità dei politopi regolari in `d ≥ 5`.
-/
namespace Tengoku.LeanEvalPlatonicClassification end Tengoku.LeanEvalPlatonicClassification open Tengoku.LeanEvalPlatonicClassification
open Set Real
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

variable {n ι : ℕ}

/-- Le relazioni lineari si trasportano lungo l'uguaglianza delle Gram.-/
theorem relazioni_trasportate_da_gram_dim {u w : Fin ι → E n}
    (hgram : ∀ i j, ⟪u i, u j⟫ = ⟪w i, w j⟫)
    (a : Fin ι → ℝ) (h : ∑ i, a i • u i = 0) :
    ∑ i, a i • w i = 0 := by
  classical
  have hinter : ⟪∑ i, a i • w i, ∑ j, a j • w j⟫ = ⟪∑ i, a i • u i, ∑ j, a j • u j⟫ := by
    simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, ← hgram]
  have hnorm : ‖∑ i, a i • w i‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq, hinter, h]; simp
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)

/-- I prodotti interni di combinazioni lineari coincidono sotto Gram uguali.-/
theorem inner_somme_da_gram_dim {u w : Fin ι → E n}
    (hgram : ∀ i j, ⟪u i, u j⟫ = ⟪w i, w j⟫) (a b : Fin ι → ℝ) :
    ⟪∑ i, a i • w i, ∑ j, b j • w j⟫ = ⟪∑ i, a i • u i, ∑ j, b j • u j⟫ := by
  classical
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, ← hgram]

/-- Lo span pieno si trasporta lungo l'uguaglianza delle Gram.-/
theorem span_trasportato_da_gram_dim {u w : Fin ι → E n}
    (hspanU : Submodule.span ℝ (Set.range u) = ⊤)
    (hgram : ∀ i j, ⟪u i, u j⟫ = ⟪w i, w j⟫) :
    Submodule.span ℝ (Set.range w) = ⊤ := by
  classical
  let lu : (Fin ι → ℝ) →ₗ[ℝ] E n := Fintype.linearCombination ℝ u
  let lw : (Fin ι → ℝ) →ₗ[ℝ] E n := Fintype.linearCombination ℝ w
  have hker : LinearMap.ker lu = LinearMap.ker lw := by
    ext a
    simp only [LinearMap.mem_ker]
    constructor
    · intro ha
      apply relazioni_trasportate_da_gram_dim hgram a
      simpa only [lu, Fintype.linearCombination_apply] using ha
    · intro ha
      apply relazioni_trasportate_da_gram_dim (fun i j => (hgram i j).symm) a
      simpa only [lw, Fintype.linearCombination_apply] using ha
  have hru := lu.finrank_range_add_finrank_ker
  have hrw := lw.finrank_range_add_finrank_ker
  have hrange : Module.finrank ℝ lu.range = Module.finrank ℝ lw.range := by
    rw [hker] at hru; omega
  have htopU : LinearMap.range lu = ⊤ := by
    simpa only [lu, Fintype.range_linearCombination] using hspanU
  have hfinW : Module.finrank ℝ lw.range = Module.finrank ℝ (E n) := by
    rw [← hrange, htopU]; simp
  have htopW : LinearMap.range lw = ⊤ := Submodule.eq_top_of_finrank_eq hfinW
  simpa only [lw, Fintype.range_linearCombination] using htopW

/-- **U1 — registrazione dei sistemi semplici**: due famiglie di vettori in `E n` con
la stessa matrice di Gram e span pieno sono registrate da una isometria lineare.-/
theorem isometria_da_gram_dim {u w : Fin ι → E n}
    (hspanU : Submodule.span ℝ (Set.range u) = ⊤)
    (hspanW : Submodule.span ℝ (Set.range w) = ⊤)
    (hgram : ∀ i j, ⟪u i, u j⟫ = ⟪w i, w j⟫) :
    ∃ L : E n ≃ₗᵢ[ℝ] E n, ∀ i, L (u i) = w i := by
  classical
  let lu : (Fin ι → ℝ) →ₗ[ℝ] E n := Fintype.linearCombination ℝ u
  let lw : (Fin ι → ℝ) →ₗ[ℝ] E n := Fintype.linearCombination ℝ w
  have hker : LinearMap.ker lu = LinearMap.ker lw := by
    ext a
    simp only [LinearMap.mem_ker]
    constructor
    · intro ha
      apply relazioni_trasportate_da_gram_dim hgram a
      simpa only [lu, Fintype.linearCombination_apply] using ha
    · intro ha
      apply relazioni_trasportate_da_gram_dim (fun i j => (hgram i j).symm) a
      simpa only [lw, Fintype.linearCombination_apply] using ha
  have hsurjU : Function.Surjective lu :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination ℝ u).mp hspanU
  have hsurjW : Function.Surjective lw :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination ℝ w).mp hspanW
  let eu := LinearMap.quotKerEquivOfSurjective lu hsurjU
  let ew := LinearMap.quotKerEquivOfSurjective lw hsurjW
  let eqker := Submodule.quotEquivOfEq (LinearMap.ker lu) (LinearMap.ker lw) hker
  let e : E n ≃ₗ[ℝ] E n := eu.symm.trans (eqker.trans ew)
  have he_total : ∀ a : Fin ι → ℝ, e (lu a) = lw a := by
    intro a; simp [e, eu, ew, eqker]
  have he_inner : ∀ x y : E n, ⟪e x, e y⟫ = ⟪x, y⟫ := by
    intro x y
    obtain ⟨a, rfl⟩ := hsurjU x
    obtain ⟨b, rfl⟩ := hsurjU y
    rw [he_total, he_total]
    exact inner_somme_da_gram_dim hgram a b
  let L : E n ≃ₗᵢ[ℝ] E n := e.isometryOfInner he_inner
  refine ⟨L, ?_⟩
  intro i
  let a : Fin ι → ℝ := Pi.single i 1
  have hua : lu a = u i := by simp [lu, a, Fintype.linearCombination_apply]
  have hwa : lw a = w i := by simp [lw, a, Fintype.linearCombination_apply]
  change e (u i) = w i
  rw [← hua, he_total, hwa]

end LeanEval.Geometry.PlatonicClassification
-- Tengoku: root names of this library moved to Tengoku.LeanEvalPlatonicClassification so they do not collide with other libraries (generated)
