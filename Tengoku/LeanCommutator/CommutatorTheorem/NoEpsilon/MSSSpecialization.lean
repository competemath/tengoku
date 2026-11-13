import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.MSSBarrier
import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.MSSPick
import Tengoku.Seed.Analysis.Polynomial.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Real specialization of stable multivariate polynomials

The nonvanishing proof uses the sign of the logarithmic derivative and its
explicit Laurent residue, rather than taking Hurwitz closure as a hypothesis.
-/

namespace NoEpsilon.MSSSpecialization

open Polynomial NoEpsilon.MSSStability NoEpsilon.MSSBarrier NoEpsilon.MSSPick

variable {σ : Type*} [DecidableEq σ]

noncomputable def coordinatePolynomial {R : Type*} [CommRing R]
    (p : MvPolynomial σ R) (z : σ → R) (j : σ) : R[X] :=
  MvPolynomial.eval₂ Polynomial.C
    (fun k ↦ Polynomial.C (z k) + if k = j then Polynomial.X else 0) p

@[simp] theorem eval_coordinatePolynomial {R : Type*} [CommRing R]
    (p : MvPolynomial σ R) (z : σ → R) (j : σ) (t : R) :
    (coordinatePolynomial p z j).eval t =
      MvPolynomial.eval (coordinateShift z j t) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [coordinatePolynomial]
  | add p q hp hq => simpa [coordinatePolynomial] using congrArg₂ (· + ·) hp hq
  | mul_X p k hp =>
    simp only [coordinatePolynomial, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
      eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_X] at *
    rw [hp]
    congr 1
    by_cases hk : k = j <;> simp [coordinateShift, hk]

@[simp] theorem map_coordinatePolynomial {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : MvPolynomial σ R) (z : σ → R) (j : σ) :
    (coordinatePolynomial p z j).map f =
      coordinatePolynomial (p.map f) (fun k ↦ f (z k)) j := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [coordinatePolynomial]
  | add p q hp hq => simpa [coordinatePolynomial] using congrArg₂ (· + ·) hp hq
  | mul_X p k hp =>
    simp only [coordinatePolynomial, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
      Polynomial.map_mul, map_mul, MvPolynomial.map_X] at *
    rw [hp]
    congr 1
    by_cases hk : k = j <;> simp [hk]

variable [Fintype σ]

-- Preserve the existing parameter list for downstream callers.

/-- Real polynomials whose complexifications are upper stable split over `ℝ`.
The proof is adapted from the source repository's `BTRealStabilityClosure`.-/
theorem splits_of_complexification_upperStable {p : ℝ[X]}
    (hp : ∀ z : ℂ, 0 < z.im → (p.map Complex.ofRealHom).eval z ≠ 0) : p.Splits := by
  have hp0 : p ≠ 0 := by
    intro hzero
    subst p
    exact hp Complex.I (by simp) (by simp)
  have hmap0 : p.map Complex.ofRealHom ≠ 0 :=
    fun h ↦ hp0 ((Polynomial.map_eq_zero_iff Complex.ofReal_injective).mp h)
  apply Polynomial.Splits.of_splits_map_of_injective
    (i := Complex.ofRealHom) Complex.ofReal_injective (IsAlgClosed.splits _)
  intro z hz
  have hzroot : (p.map Complex.ofRealHom).IsRoot z := (Polynomial.mem_roots hmap0).mp hz
  have hmapEq : p.map Complex.ofRealHom = p.map (algebraMap ℝ ℂ) := by congr 1
  have hzeval : Polynomial.aeval z p = 0 := by
    rw [← Polynomial.eval_map_algebraMap, ← hmapEq]
    exact hzroot
  have hnotPos : ¬ 0 < z.im := fun hzpos ↦ hp z hzpos hzroot
  have hnotNeg : ¬ z.im < 0 := by
    intro hzneg
    have hconjPos : 0 < (starRingEnd ℂ z).im := by simp; linarith
    apply hp (starRingEnd ℂ z) hconjPos
    rw [hmapEq, Polynomial.eval_map_algebraMap, Polynomial.aeval_conj, hzeval]
    simp
  have hzim : z.im = 0 := by linarith
  refine ⟨z.re, ?_⟩
  apply Complex.ext
  · simp
  · simpa using hzim.symm

-- Preserve the existing parameter list for downstream callers.

omit [Fintype σ] in
/-- Every root of an above-roots coordinate restriction is strictly negative.-/
theorem coordinatePolynomial_roots_neg {p : MvPolynomial σ ℝ} {z : σ → ℝ}
    (hz : AboveRoots p z) (j : σ) {r : ℝ}
    (hr : r ∈ (coordinatePolynomial p z j).roots) : r < 0 := by
  have hne : coordinatePolynomial p z j ≠ 0 := by
    intro h
    have he := hz.eval_pos
    rw [← coordinateShift_zero z j, ← eval_coordinatePolynomial, h] at he
    simp at he
  by_contra hnot
  have hr0 : 0 ≤ r := le_of_not_gt hnot
  have heval := (mem_roots hne).mp hr
  have hpos := hz _ (le_coordinateShift z j hr0)
  rw [← eval_coordinatePolynomial] at hpos
  exact hpos.ne' heval

-- Preserve the existing parameter list for downstream callers.

/-- A polynomial quotient bounded on the positive ray cannot have numerator
degree larger than denominator degree.-/
theorem natDegree_le_of_bounded_quotient (g h : ℝ[X]) (hzero : h ≠ 0) (C : ℝ)
    (hbound : ∀ x : ℝ, 0 ≤ x → |g.eval x / h.eval x| ≤ C) :
    g.natDegree ≤ h.natDegree := by
  by_contra hnot
  have hdeg := Polynomial.degree_lt_degree (Nat.lt_of_not_ge hnot)
  have ht := g.abs_div_tendsto_atTop_atTop_of_degree_gt h hdeg hzero
  have he : ∀ᶠ x : ℝ in Filter.atTop, C < |g.eval x / h.eval x| :=
    ht.eventually (Filter.eventually_gt_atTop C)
  obtain ⟨x, hx, hx0⟩ := (he.and (Filter.eventually_ge_atTop (0 : ℝ))).exists
  exact (not_lt_of_ge (hbound x hx0)) hx

-- Preserve the existing parameter list for downstream callers.

end NoEpsilon.MSSSpecialization
