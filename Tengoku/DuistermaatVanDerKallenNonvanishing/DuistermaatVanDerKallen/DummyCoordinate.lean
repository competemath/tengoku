import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.CriticalLocus
import Tengoku.Seed.Algebra.MvPolynomial.Rename

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Extend the affine torus by one unused coordinate and its inverse. -/

namespace DuistermaatVanDerKallen
noncomputable section

def ambientSucc {d : ℕ} : (Fin d ⊕ Fin d) → (Fin (d + 1) ⊕ Fin (d + 1)) :=
  Sum.map Fin.succ Fin.succ

theorem ambientSucc_injective (d : ℕ) : Function.Injective (ambientSucc (d := d)) :=
  Sum.map_injective.mpr ⟨Fin.succ_injective d, Fin.succ_injective d⟩

def dummyExtension {d : ℕ} (p : AmbientPolynomial d) : AmbientPolynomial (d + 1) :=
  MvPolynomial.rename ambientSucc p

def dummyPoint {d : ℕ} (a : ℂ) (x : TorusAmbient d) : TorusAmbient (d + 1) :=
  WithLp.toLp 2 (Sum.elim (Fin.cons a (fun i => x (.inl i)))
    (Fin.cons a⁻¹ (fun i => x (.inr i))))

theorem dummyPoint_mem {d : ℕ} {a : ℂ} (ha : a ≠ 0) {x : TorusAmbient d}
    (hx : x ∈ affineTorus d) : dummyPoint a x ∈ affineTorus (d + 1) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact mul_inv_cancel₀ ha
  · exact hx j

theorem norm_le_dummyPoint_norm {d : ℕ} (a : ℂ) (x : TorusAmbient d) :
    ‖a‖ ≤ ‖dummyPoint a x‖ :=
  PiLp.norm_apply_le (dummyPoint a x) (.inl 0)

theorem dummyExtension_eval {d : ℕ} (p : AmbientPolynomial d) (a : ℂ) (x : TorusAmbient d) :
    ambientEval (dummyExtension p) (dummyPoint a x) = ambientEval p x := by
  unfold ambientEval dummyExtension
  rw [MvPolynomial.eval_rename]
  have he : (dummyPoint a x).ofLp ∘ ambientSucc = x.ofLp := by
    funext i
    cases i <;> rfl
  rw [he]

theorem pderiv_dummyExtension_zero {d : ℕ} (p : AmbientPolynomial d) :
    MvPolynomial.pderiv (.inl 0) (dummyExtension p) = 0 ∧
      MvPolynomial.pderiv (.inr 0) (dummyExtension p) = 0 := by
  constructor <;> apply MvPolynomial.pderiv_eq_zero_of_notMem_vars <;>
    intro h <;> obtain ⟨j, _, hj⟩ := MvPolynomial.mem_vars_rename ambientSucc p h <;>
    cases j <;> simp [ambientSucc] at hj

theorem torusPartial_dummyExtension_zero {d : ℕ} (p : AmbientPolynomial d) :
    torusPartial (dummyExtension p) 0 = 0 := by
  simp [torusPartial, (pderiv_dummyExtension_zero p).1, (pderiv_dummyExtension_zero p).2]

theorem torusPartial_dummyExtension_succ {d : ℕ} (p : AmbientPolynomial d) (i : Fin d) :
    torusPartial (dummyExtension p) i.succ = dummyExtension (torusPartial p i) := by
  have hl := MvPolynomial.pderiv_rename (ambientSucc_injective d) (.inl i) p
  have hr := MvPolynomial.pderiv_rename (ambientSucc_injective d) (.inr i) p
  simpa [torusPartial, dummyExtension, ambientSucc, map_sub, map_mul, map_pow] using
    congrArg₂ (fun a b => a - MvPolynomial.X (.inr i.succ) ^ 2 * b) hl hr

/-- Criticality persists along the new, unused torus coordinate.-/
theorem dummyExtension_critical {d : ℕ} (p : AmbientPolynomial d) (a : ℂ) (x : TorusAmbient d)
    (hx : ambientDifferentialNorm (torusPartial p) x = 0) :
    ambientDifferentialNorm (torusPartial (dummyExtension p)) (dummyPoint a x) = 0 := by
  rw [ambientDifferentialNorm_eq_zero_iff] at hx ⊢
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [torusPartial_dummyExtension_zero, ambientEval]
  · rw [torusPartial_dummyExtension_succ, dummyExtension_eval]
    exact hx j

end
end DuistermaatVanDerKallen
