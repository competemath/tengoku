import Tengoku.OpenaiMath.OAI.Analysis.Unitarizability.FrameSelection
import Tengoku.OpenaiMath.OAI.Analysis.Unitarizability.ComplexFrames

namespace OAI

/-! Frame existence with prescribed dimensions and bounds for all small subfamilies. -/
noncomputable section
namespace Dixmier
namespace SignMatrix
open Finset
variable {I J L K : Type*} [Fintype I] [Fintype J] [Fintype L] [Fintype K]
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq J := Classical.decEq J
local instance : DecidableEq L := Classical.decEq L
local instance : DecidableEq K := Classical.decEq K

def extendVector (e : J ↪ L) (z : EuclideanSpace ℝ J) : EuclideanSpace ℝ L :=
  WithLp.toLp 2 (extend e z)

theorem extendVector_norm (e : J ↪ L) (z : EuclideanSpace ℝ J) : ‖extendVector e z‖ = ‖z‖ := by
  have h : ‖extendVector e z‖^2 = ‖z‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq, extendVector, Real.norm_eq_abs, sq_abs]
    exact sum_extend_sq e z
  nlinarith [norm_nonneg (extendVector e z), norm_nonneg z]

omit [Fintype I] in
theorem synthesis_extendVector (σ : K × I → Bool) (e : L ↪ I) (f : J ↪ L)
    (z : EuclideanSpace ℝ J) : synthesis σ e (extendVector f z) = synthesis σ (f.trans e) z := by
  simp only [synthesis_apply, extendVector]
  rw [sum_on_embedding f _ (fun i hi => by rw [extend_off f z i hi]; simp)]
  simp only [extend_apply, Function.Embedding.trans_apply]

omit [Fintype I] in
theorem synthesis_restrict_norm (σ : K × I → Bool) (e : L ↪ I) (f : J ↪ L) :
    ‖synthesis σ (f.trans e)‖ ≤ ‖synthesis σ e‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro z
  rw [← synthesis_extendVector]
  exact ((synthesis σ e).le_opNorm _).trans_eq (by rw [extendVector_norm])

/-- Extend each smaller subset to size p, then restrict a coordinate synthesis operator. -/
theorem all_subfamilies {k p : ℕ} (hp : p ≤ Fintype.card I) (σ : Fin k × I → Bool)
    (hσ : ∀ e : Fin p ↪ I, ‖synthesis σ e‖ ≤ 10) :
    ∀ J : Finset I, J.card ≤ p →
      ‖FiniteSynthesis.synthesis (fun i => ComplexFrames.ofReal (vector σ i)) J‖ ≤ 10 := by
  classical
  intro J hJ
  obtain ⟨L, hJL, hLu, hLc⟩ := Finset.exists_subsuperset_card_eq (s := J) (t := univ)
    (Finset.subset_univ _) hJ (by simpa using hp)
  let eL : L ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
  let q : L ≃ Fin p := L.equivFinOfCardEq hLc
  let e : Fin p ↪ I := q.symm.toEmbedding.trans eL
  have he : q.toEmbedding.trans e = eL := by ext i; simp [e]
  have hL : ‖synthesis σ eL‖ ≤ 10 := by
    have h := synthesis_restrict_norm σ e q.toEmbedding
    rw [he] at h
    exact h.trans (hσ e)
  let f : J ↪ L := ⟨fun i => ⟨i.1, hJL i.2⟩, by intro a b h; exact Subtype.ext (congrArg (fun x : L => (x : I)) h)⟩
  let eJ : J ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
  have hf : f.trans eL = eJ := by ext i; rfl
  have hJnorm : ‖synthesis σ eJ‖ ≤ 10 := by
    have h := synthesis_restrict_norm σ eL f
    rw [hf] at h
    exact h.trans hL
  apply ComplexFrames.synthesis_bound _ J (by norm_num : (0 : ℝ) ≤ 10)
  intro z
  have h := (synthesis σ eJ).le_of_opNorm_le hJnorm z
  simpa only [synthesis_apply, eJ, Function.Embedding.coeFn_mk] using h

end SignMatrix
end Dixmier

end

end OAI
