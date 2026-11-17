import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_WindingDatum
import Tengoku.FltAnthropic.Theorems.Thm_AutomorphicForm_WindingDatum_exists_forall_summable_norm_fibreTerm_and_norm_fibreCoeff_le

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_WindingDatum_sum_mul_coeff_eq_tsum_mul_tsum.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_WindingDatum_sum_mul_coeff_eq_tsum_mul_tsum

set_option autoImplicit false

open MeasureTheory

namespace AutomorphicForm
export _root_.AutomorphicForm (WindingDatum WindingDatum.fibreTerm WindingDatum.coeff WindingDatum.exists_forall_summable_norm_fibreTerm_and_norm_fibreCoeff_le)
namespace WindingDatum
export _root_.AutomorphicForm.WindingDatum (fibreTerm fibreCoeff coeff lam χ θ₀ m Ψ x₀ hsub n₀ sub exists_forall_summable_norm_fibreTerm_and_norm_fibreCoeff_le)
namespace PairingUnfold
open _root_.AutomorphicForm.WindingDatum open _root_.AutomorphicForm

variable {r d c : ℕ} (𝒟 : AutomorphicForm.WindingDatum r d c)

noncomputable def classTerm (G : (Fin d → ℤ) → ℂ) (i : ℕ) (γ : 𝒟.sub i) : ℂ :=
  G ((γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + 𝒟.n₀ i) *
    (𝒟.Ψ i (𝒟.x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) *
      ∏ j, fourier (𝒟.m i j) (𝒟.θ₀ i j + 𝒟.χ ⟨(γ : (Fin r → ℝ) × (Fin d → ℤ)), 𝒟.hsub i γ.2⟩ j))

/--
@isnad1 id=eq.1h8v.s8.9fc273cf44e6 from=translated src=- shape=2b1ffab4 vocab=ca4d861e
-/
theorem sum_mul_fibreTerm (B : Finset (Fin d → ℤ)) (G : (Fin d → ℤ) → ℂ) (hG : ∀ n ∉ B, G n = 0)
    (i : ℕ) (γ : 𝒟.sub i) :
    ∑ n ∈ B, G n * 𝒟.fibreTerm i n γ = classTerm 𝒟 G i γ := by
  classical
  unfold AutomorphicForm.WindingDatum.fibreTerm classTerm
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [hG _ h, zero_mul]

/--
@isnad1 id=le.1h8v.s8.14019abc6648 from=translated src=- shape=6b2d20ff vocab=ed83653c
-/
theorem norm_classTerm_le (B : Finset (Fin d → ℤ)) (G : (Fin d → ℤ) → ℂ) (hG : ∀ n ∉ B, G n = 0)
    (i : ℕ) (γ : 𝒟.sub i) :
    ‖classTerm 𝒟 G i γ‖ ≤ ∑ n ∈ B, ‖G n‖ * ‖𝒟.fibreTerm i n γ‖ := by
  rw [← sum_mul_fibreTerm 𝒟 B G hG i γ]
  refine (norm_sum_le _ _).trans ?_
  exact Finset.sum_le_sum fun n _ => (norm_mul_le _ _)

/--
@isnad1 id=and.1h6v.s10.4a9a07987b13 from=translated src=- shape=a7bfab66 vocab=afce6acf
-/
theorem main (B : Finset (Fin d → ℤ)) (G : (Fin d → ℤ) → ℂ) (hG : ∀ n ∉ B, G n = 0) :
    (∀ i : ℕ, Summable fun γ : 𝒟.sub i => ‖classTerm 𝒟 G i γ‖) ∧
    (Summable fun i : ℕ => ‖𝒟.lam i * ∑' γ : 𝒟.sub i, classTerm 𝒟 G i γ‖) ∧
    ∑ n ∈ B, G n * 𝒟.coeff n = ∑' i : ℕ, 𝒟.lam i * ∑' γ : 𝒟.sub i, classTerm 𝒟 G i γ := by
  obtain ⟨K, hK0, hfin, hsumi⟩ :=
    AutomorphicForm.WindingDatum.exists_forall_summable_norm_fibreTerm_and_norm_fibreCoeff_le 𝒟

  have hcls : ∀ i : ℕ, Summable fun γ : 𝒟.sub i => ‖classTerm 𝒟 G i γ‖ := by
    intro i
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_classTerm_le 𝒟 B G hG i)
      (summable_sum fun n _ => ((hfin i n).1.mul_left ‖G n‖))
  have hclsC : ∀ i : ℕ, Summable fun γ : 𝒟.sub i => classTerm 𝒟 G i γ := fun i => (hcls i).of_norm

  have hinner : ∀ i : ℕ, ∑' γ : 𝒟.sub i, classTerm 𝒟 G i γ = ∑ n ∈ B, G n * 𝒟.fibreCoeff i n := by
    intro i
    have hs : ∀ n ∈ B, Summable fun γ : 𝒟.sub i => G n * 𝒟.fibreTerm i n γ :=
      fun n _ => ((hfin i n).1.of_norm).mul_left (G n)
    calc ∑' γ : 𝒟.sub i, classTerm 𝒟 G i γ
          = ∑' γ : 𝒟.sub i, ∑ n ∈ B, G n * 𝒟.fibreTerm i n γ :=
            tsum_congr fun γ => (sum_mul_fibreTerm 𝒟 B G hG i γ).symm
      _ = ∑ n ∈ B, ∑' γ : 𝒟.sub i, G n * 𝒟.fibreTerm i n γ := Summable.tsum_finsetSum hs
      _ = ∑ n ∈ B, G n * 𝒟.fibreCoeff i n := by
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [tsum_mul_left]; rfl

  have hout : Summable fun i : ℕ => ‖𝒟.lam i * ∑' γ : 𝒟.sub i, classTerm 𝒟 G i γ‖ := by
    have hb : ∀ i : ℕ, ‖𝒟.lam i * ∑' γ : 𝒟.sub i, classTerm 𝒟 G i γ‖ ≤
        ∑ n ∈ B, ‖G n‖ * ‖𝒟.lam i * 𝒟.fibreCoeff i n‖ := by
      intro i
      rw [hinner i, Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
      rw [mul_left_comm, norm_mul]
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb
      (summable_sum fun n _ => (hsumi n).mul_left ‖G n‖)
  refine ⟨hcls, hout, ?_⟩

  have hs2 : ∀ n ∈ B, Summable fun i : ℕ => G n * (𝒟.lam i * 𝒟.fibreCoeff i n) :=
    fun n _ => ((hsumi n).of_norm).mul_left (G n)
  calc ∑ n ∈ B, G n * 𝒟.coeff n
        = ∑ n ∈ B, ∑' i : ℕ, G n * (𝒟.lam i * 𝒟.fibreCoeff i n) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          unfold AutomorphicForm.WindingDatum.coeff
          rw [tsum_mul_left]
    _ = ∑' i : ℕ, ∑ n ∈ B, G n * (𝒟.lam i * 𝒟.fibreCoeff i n) := (Summable.tsum_finsetSum hs2).symm
    _ = ∑' i : ℕ, 𝒟.lam i * ∑' γ : 𝒟.sub i, classTerm 𝒟 G i γ := by
          refine tsum_congr fun i => ?_
          rw [hinner i, Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          ring

end AutomorphicForm.WindingDatum.PairingUnfold

/--
@isnad1 id=and.1h6v.s13.90f2b8fbaa26 from=translated src=- shape=aceded27 vocab=f49b43c8
-/
theorem solution
    {r d c : ℕ} (𝒟 : AutomorphicForm.WindingDatum r d c) (B : Finset (Fin d → ℤ)) (G : (Fin d → ℤ) → ℂ)
    (hG : ∀ n ∉ B, G n = 0) :
    (∀ i : ℕ, Summable fun γ : 𝒟.sub i =>
        ‖G ((γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + 𝒟.n₀ i) *
          (𝒟.Ψ i (𝒟.x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) *
            ∏ j, fourier (𝒟.m i j) (𝒟.θ₀ i j + 𝒟.χ ⟨(γ : (Fin r → ℝ) × (Fin d → ℤ)), 𝒟.hsub i γ.2⟩ j))‖) ∧
    (Summable fun i : ℕ => ‖𝒟.lam i * ∑' γ : 𝒟.sub i,
        G ((γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + 𝒟.n₀ i) *
          (𝒟.Ψ i (𝒟.x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) *
            ∏ j, fourier (𝒟.m i j) (𝒟.θ₀ i j + 𝒟.χ ⟨(γ : (Fin r → ℝ) × (Fin d → ℤ)), 𝒟.hsub i γ.2⟩ j))‖) ∧
    ∑ n ∈ B, G n * 𝒟.coeff n = ∑' i : ℕ, 𝒟.lam i * ∑' γ : 𝒟.sub i,
        G ((γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + 𝒟.n₀ i) *
          (𝒟.Ψ i (𝒟.x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) *
            ∏ j, fourier (𝒟.m i j) (𝒟.θ₀ i j + 𝒟.χ ⟨(γ : (Fin r → ℝ) × (Fin d → ℤ)), 𝒟.hsub i γ.2⟩ j)) :=
  AutomorphicForm.WindingDatum.PairingUnfold.main 𝒟 B G hG
