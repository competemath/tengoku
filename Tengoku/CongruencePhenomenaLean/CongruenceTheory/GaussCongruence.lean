import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
**Theorem `thm:gauss`** ("Prime-power Gauss criterion"): condition (iii) of
`thm:euler-integrality` — `∀N≥1, N ∣ M_N` where `M_N = ∑_{d∣N} μ(N/d) w_d` — is equivalent to
the Gauss congruence condition `w_{mp^r} ≡ w_{mp^{r-1}} (mod p^r)` for every prime `p`, `r≥1`,
and `m≥1` with `p∤m`. This is a self-contained fact about Möbius transforms of integer
sequences, independent of the power-series machinery `thm:euler-product`/`thm:euler-integrality`
need.

The crux is the **key identity**: for `p∤m`, `r≥1`,
`M_{mp^r} = ∑_{e∣m} μ(m/e)·(w_{ep^r} - w_{ep^{r-1}})`, obtained by splitting the divisors of
`m·p^r` into `e·p^i` for `e∣m`, `0≤i≤r` (using `Nat.Coprime.divisors_mul` and
`Nat.divisors_prime_pow`), then using multiplicativity of `μ` to show only `i=r` and `i=r-1`
contribute (`μ(p^j)=0` for `j≥2`).
-/

namespace CongruenceTheory

open Nat Finset ArithmeticFunction

open scoped ArithmeticFunction.Moebius

/-- `M_N`, the Möbius transform `∑_{d∣N} μ(N/d)·w_d`.-/
noncomputable def MTrans (w : ℕ → ℤ) (N : ℕ) : ℤ := ∑ d ∈ N.divisors, (μ (N / d) : ℤ) * w d

/-- **Möbius inversion**: `w_m = ∑_{d∣m} M_d`, for free from Mathlib's own
`ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq`.-/
theorem moebius_inversion (w : ℕ → ℤ) (m : ℕ) (hm : 0 < m) :
    w m = ∑ d ∈ m.divisors, MTrans w d := by
  have hiff := @sum_eq_iff_sum_smul_moebius_eq ℤ _ (MTrans w) w
  have hrhs : ∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℤ) • w x.2 = MTrans w n := by
    intro n _
    rw [Nat.sum_divisorsAntidiagonal' (f := fun a b => (μ a : ℤ) • w b)]
    simp only [MTrans, smul_eq_mul]
  exact ((hiff.mpr hrhs) m hm).symm

end CongruenceTheory
