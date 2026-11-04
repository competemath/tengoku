import Tengoku.ErdosLean.ErdosLean.Erdos514.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Erdős #514 — Part: Taylor shifts of transcendental functions are transcendental.
If `shift f n = p` then `f = ∑_{k<n} aₖ zᵏ + zⁿ p`, a polynomial. -/

namespace Erdos514

/--
@isnad1 id=istransc.1h2v.s3.70654a804335 from=translated src=- shape=35a9db1b vocab=44d61caf
-/
theorem shift_transcendental {f : ℂ → ℂ} (hf : IsTranscendentalEntire f) (n : ℕ) :
    IsTranscendentalEntire (shift f n) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · rw [shift_succ, ← differentiableOn_univ,
        Complex.differentiableOn_dslope Filter.univ_mem]
      exact ih.1.differentiableOn
    · rintro ⟨p, hp⟩
      apply ih.2
      refine ⟨Polynomial.C (shift f n 0) + Polynomial.X * p, fun z => ?_⟩
      have h := sub_smul_dslope (shift f n) 0 z
      simp only [sub_zero, smul_eq_mul] at h
      rw [shift_succ] at hp
      simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
        Polynomial.eval_X, ← hp, h]
      ring

end Erdos514
