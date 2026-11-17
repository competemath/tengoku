/-
The size obstruction in the final local row.

This module isolates the deterministic arithmetic core of the reverse-fibre
argument.  It intentionally does not formalize an asymptotic claim or a finite
computer census.
-/
import Tengoku.Seed.Data.Nat.ModEq
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

/-- A natural number strictly between `1` and the modulus cannot be congruent
to `1` modulo that modulus.  This is the `j = 0` branch of the final-row size
obstruction.
@isnad1 id=not.2h2v.s4.cb7e766bff7d from=translated src=- shape=107e8e78 vocab=745abe38
-/
theorem not_modEq_one_of_one_lt_of_lt {P T : ℕ}
    (hP : 1 < P) (hPT : P < T) : ¬ P ≡ 1 [MOD T] := by
  intro h
  have h1T : 1 < T := lt_trans hP hPT
  have : P = 1 := h.eq_of_lt_of_lt hPT h1T
  omega

/-- If `0 < P < q² ≤ T`, then `P` cannot be congruent to `q²` modulo
`T`.  The proof treats separately `q² < T` and the boundary `q² = T`.
@isnad1 id=not.3h3v.s6.05ff6e736698 from=translated src=- shape=5ab16b8a vocab=137ffae1
-/
theorem not_modEq_sq_of_pos_of_lt_of_le {P q T : ℕ}
    (hP0 : 0 < P) (hPq : P < q ^ 2) (hqT : q ^ 2 ≤ T) :
    ¬ P ≡ q ^ 2 [MOD T] := by
  intro h
  have hPT : P < T := lt_of_lt_of_le hPq hqT
  rcases hqT.lt_or_eq with hqTlt | rfl
  · have : P = q ^ 2 := h.eq_of_lt_of_lt hPT hqTlt
    omega
  · change P % (q ^ 2) = q ^ 2 % q ^ 2 at h
    rw [Nat.mod_eq_of_lt hPq, Nat.mod_self] at h
    omega

/-- **Final-row size exclusion for three factors.**

If the final local row has either residue `1` or `q²`, a product
`1 < P < q²` cannot satisfy it modulo an order `T ≥ q²`.  In the Agrawal
application, `P = p₁p₂`, `q` is the largest prime, and the two alternatives
are exactly the exponents `j_q ∈ {0,2}`.
@isnad1 id=false.4h3v.s6.0ccd6060a2d2 from=translated src=- shape=18f32aef vocab=137ffae1
-/
theorem threeFactor_finalRow_size_exclusion {P q T : ℕ}
    (hP : 1 < P) (hPq : P < q ^ 2) (hqT : q ^ 2 ≤ T)
    (hrow : P ≡ 1 [MOD T] ∨ P ≡ q ^ 2 [MOD T]) : False := by
  rcases hrow with hrow | hrow
  · exact not_modEq_one_of_one_lt_of_lt hP (lt_of_lt_of_le hPq hqT) hrow
  · exact not_modEq_sq_of_pos_of_lt_of_le (by omega) hPq hqT hrow

/-- **Universal size bound for a local row.**

Suppose a nontrivial natural number `P`, distinct from `p²`, satisfies one
of the two local-row congruences

`P ≡ 1 (mod T)` or `P ≡ p² (mod T)`.

Then the modulus cannot exceed both representatives:

`T ≤ max p² P`.

In the Agrawal application `P = n / p`.  Squarefreeness with another
prime factor supplies `1 < P` and `P ≠ p²`; the local theory supplies the
two alternatives.  The theorem itself deliberately isolates the purely
arithmetic kernel and does not build those application hypotheses into
its statement.
@isnad1 id=le.3h3v.s6.d3a4899712ff from=translated src=- shape=73a67f75 vocab=1b49a7ea
-/
theorem localRow_order_le_max {P p T : ℕ}
    (hP : 1 < P) (hne : P ≠ p ^ 2)
    (hrow : P ≡ 1 [MOD T] ∨ P ≡ p ^ 2 [MOD T]) :
    T ≤ max (p ^ 2) P := by
  by_contra h
  have hmax : max (p ^ 2) P < T := Nat.lt_of_not_ge h
  have hpT : p ^ 2 < T := lt_of_le_of_lt (Nat.le_max_left _ _) hmax
  have hPT : P < T := lt_of_le_of_lt (Nat.le_max_right _ _) hmax
  rcases hrow with hrow | hrow
  · exact not_modEq_one_of_one_lt_of_lt hP hPT hrow
  · exact hne (hrow.eq_of_lt_of_lt hPT hpT)

/-- **Normal-defect gap at a middle factor.**

Assume the exact order/defect identity

`T * I = 10 * (r² - 1)`

with `r ≥ 7` and a normal odd defect `I ≤ 9`.  Then `T` is strictly larger
than `r²`.  Consequently, if a local row supplies the universal size bound
`T ≤ max r² P`, its complementary product must satisfy `r² < P`.

For a three-prime candidate `p < r < q`, taking `P = p*q` says that a
normal middle prime forces the large-gap alternative `r² < p*q`; otherwise
the middle prime itself must have exceptional defect at least `11`.
@isnad1 id=lt.4h4v.s7.0e3e9837bbca from=translated src=- shape=a82afe04 vocab=11a964b9
-/
theorem normalDefect_forces_sq_lt_complement {r T I P : ℕ}
    (hr : 7 ≤ r) (hexact : T * I = 10 * (r ^ 2 - 1))
    (hI : I ≤ 9) (hsize : T ≤ max (r ^ 2) P) :
    r ^ 2 < P := by
  have hr2 : 10 < r ^ 2 := by nlinarith
  have hT : r ^ 2 < T := by
    by_contra h
    have hTle : T ≤ r ^ 2 := Nat.le_of_not_gt h
    have hmul : T * I ≤ r ^ 2 * 9 :=
      Nat.mul_le_mul hTle hI
    rw [hexact] at hmul
    have hsub : r ^ 2 - 1 + 1 = r ^ 2 := by omega
    omega
  by_contra h
  have hPle : P ≤ r ^ 2 := Nat.le_of_not_gt h
  have hmax : max (r ^ 2) P = r ^ 2 := max_eq_left hPle
  rw [hmax] at hsize
  omega

/-- The pure final row is exactly the divisibility `T ∣ P - 1`.
@isnad1 id=dvd.2h2v.s5.2b47105bfd61 from=translated src=- shape=a38a1144 vocab=b8829c5b
-/
theorem pureRow_dvd_product_sub_one {P T : ℕ}
    (hP : 1 ≤ P) (hrow : P ≡ 1 [MOD T]) :
    T ∣ P - 1 := by
  exact (Nat.modEq_iff_dvd' hP).mp hrow.symm

/-- The twisted final row is exactly the divisibility `T ∣ q² - P`
when the candidate product lies below `q²`.
@isnad1 id=dvd.2h3v.s6.e5744699ed75 from=translated src=- shape=0e7e1cde vocab=0fe24a4f
-/
theorem twistedRow_dvd_sq_sub_product {P q T : ℕ}
    (hPq : P < q ^ 2) (hrow : P ≡ q ^ 2 [MOD T]) :
    T ∣ q ^ 2 - P := by
  exact (Nat.modEq_iff_dvd' (Nat.le_of_lt hPq)).mp hrow

/-- **Twisted final-row clamp.** A proper candidate in the twisted row
satisfies `P ≤ q² - T`.  This is an exact rewriting of the congruence,
not an additional sieve on candidates already enumerated in that residue
class.
@isnad1 id=le.2h3v.s6.e0ca157e8d67 from=translated src=- shape=e7405afb vocab=515367b1
-/
theorem twistedRow_product_le_sq_sub_order {P q T : ℕ}
    (hPq : P < q ^ 2) (hrow : P ≡ q ^ 2 [MOD T]) :
    P ≤ q ^ 2 - T := by
  have hdvd : T ∣ q ^ 2 - P :=
    twistedRow_dvd_sq_sub_product hPq hrow
  have hpos : 0 < q ^ 2 - P := Nat.sub_pos_of_lt hPq
  have hTle : T ≤ q ^ 2 - P := Nat.le_of_dvd hpos hdvd
  omega

/-- **Pure-row quantized gap.**

A nontrivial representative of the pure local row is not merely at least
`1`: its distance from `1` is a positive multiple of the order `T`.  Hence
the complementary product satisfies `T ≤ P - 1`.

Unlike `localRow_order_le_max`, this retains the exact distance from the
prescribed residue and can therefore exclude candidates that pass the
coarser maximum bound.
@isnad1 id=le.2h2v.s5.7ddd0aa87cf6 from=translated src=- shape=a38a1144 vocab=acc293ee
-/
theorem pureRow_order_le_product_sub_one {P T : ℕ}
    (hP : 1 < P) (hrow : P ≡ 1 [MOD T]) :
    T ≤ P - 1 := by
  have hdvd : T ∣ P - 1 :=
    pureRow_dvd_product_sub_one (Nat.le_of_lt hP) hrow
  exact Nat.le_of_dvd (Nat.sub_pos_of_lt hP) hdvd

/-- **Twisted-row forbidden annulus.**

If `P` is distinct from `p²` and satisfies the twisted local row, then its
positive distance from `p²` is at least one full order:

`T ≤ (P - p²) + (p² - P)`.

The sum on the right is the natural-number absolute difference.  Thus no
candidate can lie strictly inside the open interval of radius `T` around
`p²`.
@isnad1 id=le.2h3v.s6.64ac624b6738 from=translated src=- shape=7d9392c4 vocab=7cf55240
-/
theorem twistedRow_order_le_absGap {P p T : ℕ}
    (hne : P ≠ p ^ 2) (hrow : P ≡ p ^ 2 [MOD T]) :
    T ≤ (P - p ^ 2) + (p ^ 2 - P) := by
  rcases lt_or_gt_of_ne hne with hP | hp
  · have hdvd : T ∣ p ^ 2 - P :=
      (Nat.modEq_iff_dvd' (Nat.le_of_lt hP)).mp hrow
    have hle : T ≤ p ^ 2 - P :=
      Nat.le_of_dvd (Nat.sub_pos_of_lt hP) hdvd
    omega
  · have hdvd : T ∣ P - p ^ 2 :=
      (Nat.modEq_iff_dvd' (Nat.le_of_lt hp)).mp hrow.symm
    have hle : T ≤ P - p ^ 2 :=
      Nat.le_of_dvd (Nat.sub_pos_of_lt hp) hdvd
    omega

/-- Cancellation of a common multiplier in a natural congruence when that
multiplier is coprime to the modulus.
@isnad1 id=modeq.3h4v.s5.28ac0dbb8739 from=translated src=- shape=d84baf35 vocab=355452f3
-/
theorem modEq_cancel_left_of_coprime {A B₁ B₂ T : ℕ}
    (hT : 0 < T) (hAT : Nat.Coprime A T)
    (h : A * B₁ ≡ A * B₂ [MOD T]) :
    B₁ ≡ B₂ [MOD T] := by
  have reduced := h.cancel_left_div_gcd hT
  have hgcd : Nat.gcd T A = 1 := hAT.symm.gcd_eq_one
  simpa [hgcd] using reduced

/-- **Meet-in-the-middle uniqueness below the order.**

If `T ≥ q²`, two candidate second products below `q²` that give the same
final-row residue after multiplication by a unit `A` are equal.  This is the
kernel-pure uniqueness statement behind the `k = 5` decision algorithm; it
does not assert a complexity bound or the absence of a candidate.
@isnad1 id=eq.7h6v.s6.7d0d497e0d56 from=translated src=- shape=c85780c4 vocab=28d41342
-/
theorem mitm_secondProduct_unique {A B₁ B₂ c q T : ℕ}
    (hq : 0 < q) (hqT : q ^ 2 ≤ T) (hAT : Nat.Coprime A T)
    (hB₁ : B₁ < q ^ 2) (hB₂ : B₂ < q ^ 2)
    (h₁ : A * B₁ ≡ c [MOD T]) (h₂ : A * B₂ ≡ c [MOD T]) :
    B₁ = B₂ := by
  have hT : 0 < T := by
    have : 0 < q ^ 2 := Nat.pow_pos hq
    omega
  have hmul : A * B₁ ≡ A * B₂ [MOD T] := h₁.trans h₂.symm
  have hmod : B₁ ≡ B₂ [MOD T] :=
    modEq_cancel_left_of_coprime hT hAT hmul
  exact hmod.eq_of_lt_of_lt (lt_of_lt_of_le hB₁ hqT)
    (lt_of_lt_of_le hB₂ hqT)

end AgrawalCore
