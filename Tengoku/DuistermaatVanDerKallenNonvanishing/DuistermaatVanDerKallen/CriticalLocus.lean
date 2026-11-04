import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.SpherePathChain
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.AffineSemialgebraic
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.UniformGradient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The actual critical locus and constancy along finite C1 chains. -/

namespace DuistermaatVanDerKallen
noncomputable section

/--
@isnad1 id=iff.0h3v.s5.5c8a9fe6bc89 from=translated src=- shape=9f222f90 vocab=fe657ade
-/
theorem ambientDifferentialNorm_eq_zero_iff {d : ℕ} (g : Fin d → AmbientPolynomial d)
    (x : TorusAmbient d) :
    ambientDifferentialNorm g x = 0 ↔ ∀ i, ambientEval (g i) x = 0 := by
  have hb (i : Fin d) : 0 < (1 : ℝ) + ‖x (.inr i)‖ ^ 4 := by positivity
  have hn (i : Fin d) : 0 ≤ Complex.normSq (ambientEval (g i) x) /
      (1 + ‖x (.inr i)‖ ^ 4) := div_nonneg (Complex.normSq_nonneg _) (hb i).le
  unfold ambientDifferentialNorm differentialNormSq
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg (fun i _ => hn i)),
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)]
  simp only [Finset.mem_univ, true_implies]
  apply forall_congr'
  intro i
  simp [div_eq_zero_iff, ne_of_gt (hb i)]

def criticalTorusLocus {d : ℕ} (p : AmbientPolynomial d) : Set (TorusAmbient d) :=
  {x | x ∈ affineTorus d ∧ ambientDifferentialNorm (torusPartial p) x = 0}

/--
@isnad1 id=iscomple.0h2v.s6.196d231bf0bd from=translated src=- shape=c6a0d7c2 vocab=d7461b4c
-/
theorem isComplexSemialgebraic_criticalTorusLocus {d : ℕ} (p : AmbientPolynomial d) :
    IsComplexSemialgebraic {x : (Fin d ⊕ Fin d) → ℂ |
      WithLp.toLp 2 x ∈ criticalTorusLocus p} := by
  have h := (isComplexSemialgebraic_affineTorus d).inter
    (isComplexSemialgebraic_ambientDifferentialNorm_le (torusPartial p) (le_refl 0))
  convert h using 1
  ext x
  simp only [criticalTorusLocus, Set.mem_ofPred_eq, Set.mem_inter_iff]
  apply and_congr_right
  intro _
  exact ⟨fun h => h.le, fun h => le_antisymm h (Real.sqrt_nonneg _)⟩

/--
@isnad1 id=eq.0h2v.s6.d53bce0c07b6 from=translated src=- shape=02ad9b44 vocab=5d7100c9
-/
theorem ordinaryCriticalValues_eq_criticalTorusLocus_range {d : ℕ} (p : AmbientPolynomial d) :
    ordinaryCriticalValues (fun x : affineTorus d => ambientEval p x.val)
      (fun x => ambientDifferentialNorm (torusPartial p) x.val) =
      Set.range (fun x : criticalTorusLocus p => ambientEval p x.val) := by
  ext c
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x.val, x.property, hx⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x.val, x.property.1⟩, x.property.2, rfl⟩

end
end DuistermaatVanDerKallen
