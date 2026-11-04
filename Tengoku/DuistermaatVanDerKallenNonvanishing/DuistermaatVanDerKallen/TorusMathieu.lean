import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.TorusCoefficients
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.Targets

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The finite-Fourier compact-torus Mathieu consequence with the unproved
minimal nonvanishing theorem retained as an explicit premise. -/

open MeasureTheory
namespace DuistermaatVanDerKallen
noncomputable section

/-- A finite Fourier sum on the standard compact torus, represented by its
finite Laurent coefficient family.-/
def IsFiniteFourierSum {d : ℕ} (F : PhaseTorus d → ℂ) : Prop :=
  ∃ f : MultiLaurent d, F = fun x => laurentEval f (torusPoint (fun _ => 1) x)

/-- The Laurent representation is exactly a finite sum of the standard integer
characters, so the definition contains no extra analytic restriction.
@isnad1 id=iff.0h2v.s6.536f3e42f4e7 from=translated src=- shape=45fcf18b vocab=dc2bd0e9
-/
theorem isFiniteFourierSum_iff_coefficients {d : ℕ} (F : PhaseTorus d → ℂ) :
    IsFiniteFourierSum F ↔ ∃ c : (Fin d → ℤ) →₀ ℂ,
      F = fun x => c.sum (fun a z => z * torusCharacter a x) := by
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨f.coeff, ?_⟩
    funext x
    simp [torusLaurent_expansion, Finsupp.sum]
  · rintro ⟨c, rfl⟩
    refine ⟨AddMonoidAlgebra.ofCoeff c, ?_⟩
    funext x
    simp [torusLaurent_expansion, Finsupp.sum]

/-- Every finite Fourier sum is continuous.
@isnad1 id=continuo.1h2v.s6.6daca8d5cb87 from=translated src=- shape=0018a448 vocab=767763e9
-/
theorem IsFiniteFourierSum.continuous {d : ℕ} {F : PhaseTorus d → ℂ}
    (hF : IsFiniteFourierSum F) : Continuous F := by
  obtain ⟨f, rfl⟩ := hF
  exact torusLaurent_continuous f _

/-- The Haar/constant-term bridge for a product and a power.
@isnad1 id=eq.0h4v.s7.c88b1e6735d5 from=translated src=- shape=6659bd14 vocab=fa1b8293
-/
theorem integral_torusLaurent_mul_pow {d : ℕ} (f h : MultiLaurent d) (n : ℕ) :
    (∫ x, laurentEval h (torusPoint (fun _ => 1) x) *
      laurentEval f (torusPoint (fun _ => 1) x) ^ n ∂phaseTorusMeasure d) =
        constantTerm (h * f ^ n) := by
  have hz (x : PhaseTorus d) := torusPoint_ne_zero (fun _ : Fin d => (1 : ℝ))
    (fun _ => one_ne_zero) x
  simp_rw [← laurentEval_pow f n (hz _), ← laurentEval_mul h (f ^ n) (hz _)]
  exact integral_torusLaurent_eq_constantTerm _ _

/-- The compact-torus Mathieu statement for all finite Fourier sums follows
from the still-open arbitrary-rank minimal nonvanishing theorem.
@isnad1 id=ex.4h3v.s7.0c3ca6edfbed from=translated src=- shape=3a522af4 vocab=bf357a20
-/
theorem torus_mathieu_of_minimal (hminimal : MinimalNonvanishing) {d : ℕ}
    {F H : PhaseTorus d → ℂ} (hF : IsFiniteFourierSum F) (hH : IsFiniteFourierSum H)
    (hvan : ∀ n : ℕ, 1 ≤ n → (∫ x, F x ^ n ∂phaseTorusMeasure d) = 0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (∫ x, H x * F x ^ n ∂phaseTorusMeasure d) = 0 := by
  obtain ⟨f, rfl⟩ := hF
  obtain ⟨h, rfl⟩ := hH
  have hct : ∀ n : ℕ, 1 ≤ n → constantTerm (f ^ n) = 0 := by
    intro n hn
    rw [← integral_torusLaurent_pow f (fun _ => 1) (fun _ => one_ne_zero) n]
    exact hvan n hn
  obtain ⟨N, hN⟩ := mathieu_of_minimal hminimal f h hct
  exact ⟨N, fun n hn => (integral_torusLaurent_mul_pow f h n).trans (hN n hn)⟩

end
end DuistermaatVanDerKallen
