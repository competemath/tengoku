import Tengoku.TusnadyLean.Riesz.WeightedMoments

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# From recursive independent samples to finite vectors

The weighted-moment proof uses an iterated binary product sample space. This
module identifies it with ordinary vectors and derives the normalized finite
sum needed by the conditional fresh-digit law. No moment or Laplace conclusion
is introduced as an assumption.
-/

namespace Riesz.Moments

open scoped BigOperators

universe u

/-- The recursive sample space is exactly the space of length-`n` vectors.-/
noncomputable def sampleSpaceEquiv (Ω : Type u) : (n : ℕ) → SampleSpace Ω n ≃ (Fin n → Ω)
  | 0 =>
    { toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => PUnit.unit
      left_inv := fun x => by cases x; rfl
      right_inv := fun f => by funext i; exact Fin.elim0 i }
  | n + 1 =>
    ((Equiv.prodCongr (sampleSpaceEquiv Ω n) (Equiv.refl Ω)).trans
      (Equiv.prodComm _ _)).trans (Fin.snocEquiv (fun _ : Fin (n + 1) => Ω))

/--
@isnad1 id=eq.0h4v.s8.5cdd7a89e5ee from=translated src=- shape=51b36849 vocab=1b4a691c
-/
@[simp] lemma sampleSpaceEquiv_castSucc (Ω : Type u) (n : ℕ) (ω : SampleSpace Ω (n + 1))
    (i : Fin n) :
    sampleSpaceEquiv Ω (n + 1) ω i.castSucc = sampleSpaceEquiv Ω n ω.1 i := by
  change Fin.snoc (α := fun _ : Fin (n + 1) => Ω) (sampleSpaceEquiv Ω n ω.1) ω.2 i.castSucc = _
  exact Fin.snoc_castSucc _ _ _

/--
@isnad1 id=eq.0h3v.s7.72f8a132e56f from=translated src=- shape=9764ad99 vocab=956c974f
-/
@[simp] lemma sampleSpaceEquiv_last (Ω : Type u) (n : ℕ) (ω : SampleSpace Ω (n + 1)) :
    sampleSpaceEquiv Ω (n + 1) ω (Fin.last n) = ω.2 := by
  change Fin.snoc (α := fun _ : Fin (n + 1) => Ω) (sampleSpaceEquiv Ω n ω.1) ω.2 (Fin.last n) = _
  exact Fin.snoc_last _ _

variable {Ω : Type u} [Fintype Ω]

/--
@isnad1 id=eq.1h5v.s5.4ef3c037f85e from=translated src=- shape=86d3e4c4 vocab=b45158a6
-/
lemma independentLaw_constant_weight (μ : FiniteLaw Ω) (c : ℝ)
    (hweight : ∀ ω, μ.weight ω = c) (n : ℕ) (ω : SampleSpace Ω n) :
    (independentLaw μ n).weight ω = c ^ n := by
  induction n with
  | zero => simp [independentLaw]
  | succ n ih =>
    change (independentLaw μ n).weight ω.1 * μ.weight ω.2 = c ^ (n + 1)
    rw [ih, hweight, pow_succ]

/-- Exact conversion of expectations under a uniform recursive product law
into a finite vector sum.
@isnad1 id=eq.1h5v.s7.e7ad1db8ada6 from=translated src=- shape=c0337728 vocab=a3bc621c
-/
theorem expectation_independentLaw_vector (μ : FiniteLaw Ω) (c : ℝ)
    (hweight : ∀ ω, μ.weight ω = c) (n : ℕ) (H : (Fin n → Ω) → ℝ) :
    expectation (independentLaw μ n) (fun ω => H (sampleSpaceEquiv Ω n ω)) =
      c ^ n * ∑ ω : Fin n → Ω, H ω := by
  unfold expectation
  simp_rw [independentLaw_constant_weight μ c hweight n]
  rw [← Finset.mul_sum]
  congr 1
  exact (sampleSpaceEquiv Ω n).sum_comp H

omit [Fintype Ω] in
/-- The recursively defined weighted sum is the ordinary vector dot product.
@isnad1 id=eq.0h5v.s6.51d336fd5034 from=translated src=- shape=7711721e vocab=38c43065
-/
lemma weightedSum_eq_vector_sum (W : Ω → ℝ) (n : ℕ) (a : Fin n → ℝ)
    (ω : SampleSpace Ω n) :
    weightedSum W n a ω = ∑ i, a i * W (sampleSpaceEquiv Ω n ω i) := by
  induction n with
  | zero => simp [weightedSum]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [weightedSum, sampleSpaceEquiv_castSucc, sampleSpaceEquiv_last]
    rw [ih]

/-- Exact expectation identity for independent uniform dyadic profile cells.
@isnad1 id=eq.1h3v.s8.aba799384f41 from=translated src=- shape=a122344c vocab=3f84a34f
-/
theorem profile_vector_expectation (m : ℕ) (hm : 0 < m) (n : ℕ)
    (H : (Fin n → (Fin 4 × Fin m)) → ℝ) :
    expectation (independentLaw (profileLaw m hm) n)
      (fun ω => H (sampleSpaceEquiv (Fin 4 × Fin m) n ω)) =
      (∑ ω : Fin n → (Fin 4 × Fin m), H ω) / (4 * (m : ℝ)) ^ n := by
  rw [expectation_independentLaw_vector (profileLaw m hm) (1 / (4 * (m : ℝ)))
    (fun _ => rfl)]
  rw [one_div_pow]
  ring

/-- Flatten each quarter/cell pair into its ordinary `4m`-cell index.
@isnad1 id=eq.0h3v.s8.dceb731e1661 from=translated src=- shape=c900734a vocab=d131c358
-/
lemma profile_vector_sum_eq_flat (m n : ℕ) (H : (Fin n → (Fin 4 × Fin m)) → ℝ) :
    (∑ ω : Fin n → (Fin 4 × Fin m), H ω) =
      ∑ ω : Fin n → Fin (4 * m), H (fun i => finProdFinEquiv.symm (ω i)) := by
  let e : (Fin n → (Fin 4 × Fin m)) ≃ (Fin n → Fin (4 * m)) :=
    Equiv.piCongrRight (fun _ => finProdFinEquiv)
  apply Fintype.sum_equiv e
  intro ω
  congr 1
  funext i
  exact (finProdFinEquiv.symm_apply_apply (ω i)).symm

end Riesz.Moments
