/-
Cardinality bridge for the protected hitCount definition.
The pinned elaborator lifts the untyped filter receiver to integer casts.
Keep the specification unchanged and prove that this injective change of carrier
preserves the count. This new source has not been Lean-compiled here.
-/
import Tengoku.Erdos647.Erdos647Sieve.Specification
import Tengoku.Seed.Data.Finset.Functor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section
namespace Erdos647Sieve

/-- Filtering an injectively cast finite set counts the same elements as filtering
before the cast. No primality, window positivity, or budget premise is needed.-/
theorem card_filter_natCast_image (s : Finset ℕ) (P : ℤ → Prop) [DecidablePred P] :
    ((s.image (fun p : ℕ => (p : ℤ))).filter P).card =
      (s.filter (fun p : ℕ => P (p : ℤ))).card := by
  classical
  have hfilter :
      (s.image (fun p : ℕ => (p : ℤ))).filter P =
        (s.filter (fun p : ℕ => P (p : ℤ))).image (fun p : ℕ => (p : ℤ)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hP⟩
      exact ⟨p, ⟨hp, hP⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hP⟩, rfl⟩
      exact ⟨⟨p, hp, rfl⟩, hP⟩
  rw [hfilter]
  have hinj : Function.Injective (fun p : ℕ => (p : ℤ)) := by
    intro a b h
    -- Expose the cast equality before invoking the cast-normalization tactic.
    change (a : ℤ) = (b : ℤ) at h
    exact_mod_cast h
  exact Finset.card_image_of_injective _ hinj

/-- The exact protected hitCount equals the explicitly natural-indexed hit count.
This works for arbitrary integer n, including zeros of the window polynomial.-/
theorem hitCount_eq_nat_filter_card (H : ℕ) (y : ℝ) (n : ℤ) :
    hitCount H y n =
      ((selectedPrimes H y).filter
        (fun p : ℕ => (p : ℤ) ∣ windowPolynomial H n)).card := by
  classical
  -- Keep the direct bijection, and pass the classical equality decision stored
  -- in hitCount explicitly to BOTH image-membership lemmas below. The implicit
  -- form would instead synthesize Int.instDecidableEq in this concrete type.
  simp only [hitCount, Finset.bind_def, Finset.pure_def,
    Finset.sup_singleton_apply]
  symm
  refine Finset.card_bij (fun (p : ℕ) _ => (p : ℤ)) ?_ ?_ ?_
  · intro p hp
    obtain ⟨hpS, hpP⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨(@Finset.mem_image ℕ ℤ
          (fun a b : ℤ => Classical.propDecidable (a = b))
          (fun p : ℕ => (p : ℤ)) (selectedPrimes H y) (p : ℤ)).mpr
        ⟨p, hpS, rfl⟩, hpP⟩
  · intro a _ha b _hb hab
    change (a : ℤ) = (b : ℤ) at hab
    exact_mod_cast hab
  · intro q hq
    obtain ⟨hqImage, hqP⟩ := Finset.mem_filter.mp hq
    obtain ⟨p, hpS, hpq⟩ :=
      (@Finset.mem_image ℕ ℤ
        (fun a b : ℤ => Classical.propDecidable (a = b))
        (fun p : ℕ => (p : ℤ)) (selectedPrimes H y) q).mp hqImage
    change (p : ℤ) = q at hpq
    subst q
    exact ⟨p, Finset.mem_filter.mpr ⟨hpS, hqP⟩, rfl⟩

end Erdos647Sieve
end
