module
public import Tengoku
public import Tengoku.FltStickelberger.Stickelberger.DigitSum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
@[expose] public section

/-!
# Washington Proposition 6.13: `s(α)` is the base-`p` digit sum

Development following L. C. Washington, *Introduction to Cyclotomic
Fields* (2nd ed.), §6.2 (Proposition 6.13, p. 96–97). The `𝒫̄`-adic valuation
`s(α) = v_𝒫̄(g(ω^{-α}))` of a Gauss sum equals the sum of the base-`p` digits of `α`
(for `0 ≤ α < q-1`, `q = p^f`).

This file isolates the **counting argument** of Proposition 6.13 as statements about
an *abstract* function `s : ℕ → ℕ` satisfying the formal properties established in
Lemmas 6.11–6.12:

* `s 0 = 0`                                   (6.11(a))
* `s(α+β) ≤ s α + s β`                         (6.11(b))
* `s(α+β) ≡ s α + s β (mod p-1)`               (6.11(c))
* `s(p·α) = s α`                               (6.11(d))
* `s 1 = 1`                                    (6.12)
* the pairing `s α + s(q-1-α) = f(p-1)`        (6.11(e))

Combined with `Stickelberger.DigitSum` (in particular `two_mul_sum_digitSumF`) these
force `s = digitSumF`. Nothing here depends on Gauss sums or the cyclotomic tower; the
concrete `s` from `GaussSumVal`/`Lemma612` discharges the hypotheses.
-/

namespace Stickelberger

open Finset

section Prop613

variable {p : ℕ} {s : ℕ → ℕ}

/-- **`s n ≤ n`** (subadditivity from `s 1 = 1`): `s(n+1) ≤ s n + s 1 = s n + 1`.
@isnad1 id=le.3h2v.s6.90546de04664 from=translated src=- shape=2316495c vocab=086a35fc
-/
theorem s_le (hs0 : s 0 = 0) (hs1 : s 1 = 1) (hadd : ∀ a b, s (a + b) ≤ s a + s b) :
    ∀ n, s n ≤ n
  | 0 => by rw [hs0]
  | n + 1 => by
    have h := hadd n 1
    rw [hs1] at h
    have := s_le hs0 hs1 hadd n
    omega

/-- **Subadditivity over a finite sum** (from the binary `s(a+b) ≤ s a + s b`).
@isnad1 id=le.2h4v.s6.02b2c5b83695 from=translated src=- shape=b1dd3c84 vocab=5297e9b3
-/
theorem s_sum_le (hs0 : s 0 = 0) (hadd : ∀ a b, s (a + b) ≤ s a + s b) {ι : Type*}
    (g : ι → ℕ) (t : Finset ι) : s (∑ i ∈ t, g i) ≤ ∑ i ∈ t, s (g i) := by
  classical
  refine Finset.induction_on t ?_ (fun a t ha ih => ?_)
  · simp [hs0]
  · rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (hadd _ _).trans (Nat.add_le_add_left ih _)

end Prop613

end Stickelberger
