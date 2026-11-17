import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.AdiacenzaUnica
import Tengoku.LeanEvalPlatonicClassification.Submission.Trasportatore
import Tengoku.LeanEvalPlatonicClassification.Submission.RelazioniCoxeter
import Tengoku.LeanEvalPlatonicClassification.Submission.Iperpiano

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
MOTORE COXETER, PASSO 18 — I NORMALI DELLE RIFLESSIONI (19 lug 2026).

Dall'iperpiano dei punti fissi si estrae il NORMALE UNITARIO `αᵢ`: il
generatore della retta ortogonale alla giacitura dell'iperpiano. È il
vettore su cui si costruirà la matrice di Gram.

L'iperpiano è descritto in forma implicita: `rᵢ x = x ↔ ⟪αᵢ, x − p⟫ = 0`.
-/
namespace Tengoku.LeanEvalPlatonicClassification end Tengoku.LeanEvalPlatonicClassification open Tengoku.LeanEvalPlatonicClassification
open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Una retta ortogonale a un iperpiano contiene un vettore unitario.-/
theorem esiste_unitario_ortogonale {W : Submodule ℝ (E n)}
    (hW : Module.finrank ℝ W + 1 = n) :
    ∃ α : E n, ‖α‖ = 1 ∧ α ∈ Wᗮ ∧ Wᗮ = ℝ ∙ α := by
  have hrank : Module.finrank ℝ (Wᗮ : Submodule ℝ (E n)) = 1 := by
    have hsum := Submodule.finrank_add_finrank_orthogonal (K := W) (𝕜 := ℝ)
    have hn : Module.finrank ℝ (E n) = n := by simp
    omega
  obtain ⟨v, hv⟩ := finrank_eq_one_iff'.mp hrank
  obtain ⟨hvne, hspan⟩ := hv
  have hvnorm : ‖(v : E n)‖ ≠ 0 := by
    simpa using fun hc => hvne (Subtype.ext (by simpa using hc))
  refine ⟨‖(v : E n)‖⁻¹ • (v : E n), ?_, ?_, ?_⟩
  · rw [norm_smul]
    simp [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), hvnorm]
  · exact Submodule.smul_mem _ _ v.2
  · apply le_antisymm
    · intro w hw
      obtain ⟨c, hc⟩ := hspan ⟨w, hw⟩
      refine Submodule.mem_span_singleton.mpr ⟨c * ‖(v : E n)‖, ?_⟩
      have hcv : c • (v : E n) = w := congrArg Subtype.val hc
      rw [mul_smul, smul_inv_smul₀ hvnorm]
      exact hcv
    · rw [Submodule.span_singleton_le_iff_mem]
      exact Submodule.smul_mem _ _ v.2

end LeanEval.Geometry.PlatonicClassification
-- Tengoku: root names of this library moved to Tengoku.LeanEvalPlatonicClassification so they do not collide with other libraries (generated)
