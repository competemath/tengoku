import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.PolynomialCalculus
import Tengoku.Seed.Analysis.Calculus.Deriv.Mul
import Tengoku.Seed.Analysis.Calculus.Deriv.Comp
import Tengoku.Seed.Analysis.Calculus.MeanValue
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tangency and integration along paths in the exact small-gradient sphere
family. The derivative bound uses the restricted induced-metric norm. -/

namespace DuistermaatVanDerKallen
noncomputable section

theorem curve_derivative_mem_torusTangentSpace {d : ℕ} {γ : ℝ → TorusAmbient d}
    {v : TorusAmbient d} {S : Set ℝ} {t : ℝ} (ht : t ∈ S)
    (hS : UniqueDiffWithinAt ℝ S t) (hγ : HasDerivWithinAt γ v S t)
    (hX : ∀ s ∈ S, γ s ∈ affineTorus d) :
    v ∈ torusTangentSpace (fun i => γ t (.inl i)) := by
  have hz := affineTorus_coordinate_ne_zero (hX t ht)
  rw [mem_torusTangentSpace_iff_linearized hz]
  intro i
  have hc (j : Fin d ⊕ Fin d) : HasDerivWithinAt (fun s => γ s j) (v j) S t :=
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d ⊕ Fin d => ℂ) j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hγ
  have hp := (hc (.inl i)).mul (hc (.inr i))
  have hconst : HasDerivWithinAt (fun s => γ s (.inl i) * γ s (.inr i)) 0 S t :=
    (hasDerivWithinAt_const t S (1 : ℂ)).congr (fun s hs => hX s hs i) (hX t ht i)
  have he := (hp.derivWithin hS).symm.trans (hconst.derivWithin hS)
  rw [← affineTorus_inverse_coordinate (hX t ht) i]
  simpa [mul_comm] using he

end
end DuistermaatVanDerKallen
