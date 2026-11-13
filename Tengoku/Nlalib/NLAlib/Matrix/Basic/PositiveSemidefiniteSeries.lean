import Tengoku.Seed.Analysis.Matrix.Order

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Limits and convergent sums in the PSD cone

Continuity of quadratic forms proves closure of the real PSD cone and
positivity of convergent sums and their tails. These are the analytic
ingredients for entrywise positive-coefficient power series.
Source: Horn--Johnson (2013), Section 7.5;
supports `schur-product-inequalities`.
-/

noncomputable section
open Matrix Filter
open scoped Topology MatrixOrder
namespace NLAlib
variable {n : Type*} [Fintype n]

/-- A limit of PSD real matrices along a nontrivial filter is PSD.
Horn--Johnson (2013), Section 7.1; helper for entrywise series.
@isnad1 id=possemid.2h5v.s6.a082e3fb22c0 from=translated src=- shape=e60715cd vocab=bdd11873
-/
theorem posSemidef_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → Matrix n n ℝ} {A : Matrix n n ℝ}
    (hF : ∀ i, (F i).PosSemidef) (hlim : Tendsto F l (𝓝 A)) : A.PosSemidef := by
  have ht : Tendsto (fun i => (F i)ᵀ) l (𝓝 Aᵀ) :=
    (show Continuous (fun M : Matrix n n ℝ => Mᵀ) by fun_prop).continuousAt.tendsto.comp hlim
  have he : (fun i => (F i)ᵀ) = F := by
    funext i
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (hF i).isHermitian.eq
  rw [he] at ht
  have hAt : Aᵀ = A := tendsto_nhds_unique ht hlim
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (by simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hAt)
  intro x
  have hc : Continuous (fun M : Matrix n n ℝ => x ⬝ᵥ M *ᵥ x) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  simp only [star_trivial]
  exact le_of_tendsto_of_tendsto tendsto_const_nhds (hc.continuousAt.tendsto.comp hlim)
    (Eventually.of_forall fun i => by
      change (0 : ℝ) ≤ x ⬝ᵥ F i *ᵥ x
      simpa only [star_trivial] using (hF i).dotProduct_mulVec_nonneg x)

/-- Every convergent sum of PSD real matrices is PSD. No countability
assumption is needed on the summation index. Horn--Johnson (2013),
Section 7.5; helper for positive-coefficient series.
@isnad1 id=possemid.2h4v.s5.b82b25b31a03 from=translated src=- shape=1a5b287e vocab=516f0224
-/
theorem posSemidef_of_hasSum {ι : Type*} {F : ι → Matrix n n ℝ} {A : Matrix n n ℝ}
    (hF : ∀ i, (F i).PosSemidef) (h : HasSum F A) : A.PosSemidef := by
  exact posSemidef_of_tendsto (fun S : Finset ι => Matrix.posSemidef_sum S (fun i _ => hF i)) h

/-- Every finite initial sum of a convergent PSD matrix series lies below
the full sum in Loewner order. Horn--Johnson (2013), Section 7.5;
helper for strict positive-definiteness certificates.
@isnad1 id=le.2h4v.s6.99e4665e585a from=translated src=- shape=6abee936 vocab=f93685ba
-/
theorem sum_range_le_of_hasSum_posSemidef {F : ℕ → Matrix n n ℝ} {A : Matrix n n ℝ}
    (hF : ∀ i, (F i).PosSemidef) (h : HasSum F A) (k : ℕ) :
    (∑ i ∈ Finset.range k, F i) ≤ A := by
  exact posSemidef_of_hasSum (fun i => hF (i + k)) ((hasSum_nat_add_iff' k).mpr h)

end NLAlib
