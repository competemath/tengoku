import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.C1Coordinates
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms sign_cocycle_factorization` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms overlap_triples_gauge_related` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Sign-cocycle reconstruction on the real principal open

The three arrays below are ratios of two nonzero overlap triples.  Equal
squares say that every ratio is a sign.  Equal oriented triple products say
that the signs form a cocycle on every triangle of the complete tripartite
graph.  The theorem constructs the three vertex-sign families explicitly.
No square roots are chosen.
-/

namespace AlbertLean.Generic.RealRow

variable {K : Type*} [Field K]

/-- A scalar whose square is one is nonzero and is its own inverse.
@isnad1 id=ne.1h2v.s6.366445dde739 from=translated src=- shape=b0e5c05c vocab=73a33ec7
-/
theorem sign_ne_zero {x : K} (hx : x ^ 2 = 1) : x ≠ 0 := by
  intro h
  rw [h, zero_pow (by decide : 2 ≠ 0)] at hx
  exact zero_ne_one hx

/--
@isnad1 id=eq.1h2v.s6.b95d6135ff87 from=translated src=- shape=437d50a0 vocab=f98f2d4f
-/
theorem sign_mul_self {x : K} (hx : x ^ 2 = 1) : x * x = 1 := by
  simpa only [pow_two] using hx

/-- Triangle signs factor through signs at the three vertex sets.  The chosen
gauge is `epsilon i = s i 0`, `eta j = s 0 0 * s 0 j`, and
`zeta l = t 0 l`.  Simultaneously negating all three families leaves the edge signs unchanged;
no uniqueness or exact-kernel assertion is needed here.
@isnad1 id=ex.4h4v.s9.64b011a53de4 from=translated src=- shape=008d191b vocab=aafd7ad2
-/
theorem sign_cocycle_factorization
    (s t r : Fin 3 → Fin 3 → K)
    (hs : ∀ i j, (s i j) ^ 2 = 1)
    (ht : ∀ j l, (t j l) ^ 2 = 1)
    (hr : ∀ l i, (r l i) ^ 2 = 1)
    (htriangle : ∀ i j l, s i j * t j l * r l i = 1) :
    ∃ epsilon eta zeta : Fin 3 → K,
      (∀ i, (epsilon i) ^ 2 = 1) ∧
      (∀ j, (eta j) ^ 2 = 1) ∧
      (∀ l, (zeta l) ^ 2 = 1) ∧
      (∀ i j, s i j = epsilon i * eta j) ∧
      (∀ j l, t j l = eta j * zeta l) ∧
      (∀ l i, r l i = zeta l * epsilon i) := by
  let epsilon : Fin 3 → K := fun i => s i 0
  let eta : Fin 3 → K := fun j => s 0 0 * s 0 j
  let zeta : Fin 3 → K := fun l => t 0 l
  refine ⟨epsilon, eta, zeta, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hs i 0
  · intro j
    simp only [eta, mul_pow, hs, one_mul]
  · intro l
    exact ht 0 l
  · intro i j
    have h1 := htriangle i j 0
    have h2 := htriangle i 0 0
    have h3 := htriangle 0 j 0
    have h4 := htriangle 0 0 0
    have hij : s i j * t j 0 = s i 0 * t 0 0 := by
      apply mul_right_cancel₀ (sign_ne_zero (hr 0 i))
      rw [h1, h2]
    have h0j : s 0 j * t j 0 = s 0 0 * t 0 0 := by
      apply mul_right_cancel₀ (sign_ne_zero (hr 0 0))
      rw [h3, h4]
    dsimp only [epsilon, eta]
    apply mul_right_cancel₀ (sign_ne_zero (ht j 0))
    rw [hij]
    symm
    calc
      s i 0 * (s 0 0 * s 0 j) * t j 0 =
          s i 0 * s 0 0 * (s 0 j * t j 0) := by ring
      _ = s i 0 * s 0 0 * (s 0 0 * t 0 0) := by rw [h0j]
      _ = s i 0 * t 0 0 := by
        linear_combination s i 0 * t 0 0 * (hs 0 0)
  · intro j l
    have h1 := htriangle 0 j l
    have h2 := htriangle 0 0 l
    have hjl : s 0 j * t j l = s 0 0 * t 0 l := by
      apply mul_right_cancel₀ (sign_ne_zero (hr l 0))
      rw [h1, h2]
    dsimp only [eta, zeta]
    apply mul_left_cancel₀ (sign_ne_zero (hs 0 j))
    rw [hjl]
    symm
    calc
      s 0 j * (s 0 0 * s 0 j * t 0 l) =
          s 0 0 * (s 0 j * s 0 j) * t 0 l := by ring
      _ = s 0 0 * t 0 l := by rw [sign_mul_self (hs 0 j), mul_one]
  · intro l i
    have h := htriangle i 0 l
    have hsi0 := sign_mul_self (hs i 0)
    have ht0l := sign_mul_self (ht 0 l)
    dsimp only [zeta, epsilon]
    calc
      r l i = 1 * r l i := by rw [one_mul]
      _ = ((s i 0 * s i 0) * (t 0 l * t 0 l)) * r l i := by
        simp only [hsi0, ht0l, one_mul]
      _ = t 0 l * s i 0 * (s i 0 * t 0 l * r l i) := by ring
      _ = t 0 l * s i 0 := by rw [h, mul_one]

/-- Equal nonzero overlap squares and equal oriented triple cells imply exact
three-sided vertex-sign gauge equivalence.  This is the source normalization
statement in overlap coordinates, with no selected square roots.
@isnad1 id=ex.7h7v.s9.daf8f3361852 from=translated src=- shape=797a42ba vocab=aafd7ad2
-/
theorem overlap_triples_gauge_related
    (U V W U' V' W' : Fin 3 → Fin 3 → K)
    (hUnz : ∀ i j, U i j ≠ 0) (hVnz : ∀ j l, V j l ≠ 0)
    (hWnz : ∀ l i, W l i ≠ 0)
    (hUsq : ∀ i j, (U' i j) ^ 2 = (U i j) ^ 2)
    (hVsq : ∀ j l, (V' j l) ^ 2 = (V j l) ^ 2)
    (hWsq : ∀ l i, (W' l i) ^ 2 = (W l i) ^ 2)
    (hC : ∀ i j l, U' i j * V' j l * W' l i =
      U i j * V j l * W l i) :
    ∃ epsilon eta zeta : Fin 3 → K,
      (∀ i, (epsilon i) ^ 2 = 1) ∧
      (∀ j, (eta j) ^ 2 = 1) ∧
      (∀ l, (zeta l) ^ 2 = 1) ∧
      (∀ i j, U' i j = epsilon i * U i j * eta j) ∧
      (∀ j l, V' j l = eta j * V j l * zeta l) ∧
      (∀ l i, W' l i = zeta l * W l i * epsilon i) := by
  let s : Fin 3 → Fin 3 → K := fun i j => U' i j / U i j
  let t : Fin 3 → Fin 3 → K := fun j l => V' j l / V j l
  let r : Fin 3 → Fin 3 → K := fun l i => W' l i / W l i
  have hs : ∀ i j, (s i j) ^ 2 = 1 := by
    intro i j
    dsimp only [s]
    rw [div_pow, hUsq i j, div_self (pow_ne_zero 2 (hUnz i j))]
  have ht : ∀ j l, (t j l) ^ 2 = 1 := by
    intro j l
    dsimp only [t]
    rw [div_pow, hVsq j l, div_self (pow_ne_zero 2 (hVnz j l))]
  have hr : ∀ l i, (r l i) ^ 2 = 1 := by
    intro l i
    dsimp only [r]
    rw [div_pow, hWsq l i, div_self (pow_ne_zero 2 (hWnz l i))]
  have htriangle : ∀ i j l, s i j * t j l * r l i = 1 := by
    intro i j l
    dsimp only [s, t, r]
    field_simp [hUnz i j, hVnz j l, hWnz l i]
    exact hC i j l
  rcases sign_cocycle_factorization s t r hs ht hr htriangle with
    ⟨epsilon, eta, zeta, he, hn, hz, hsFac, htFac, hrFac⟩
  refine ⟨epsilon, eta, zeta, he, hn, hz, ?_, ?_, ?_⟩
  · intro i j
    have h := hsFac i j
    dsimp only [s] at h
    field_simp [hUnz i j] at h
    calc
      U' i j = U i j * epsilon i * eta j := h
      _ = epsilon i * U i j * eta j := by ring
  · intro j l
    have h := htFac j l
    dsimp only [t] at h
    field_simp [hVnz j l] at h
    calc
      V' j l = V j l * eta j * zeta l := h
      _ = eta j * V j l * zeta l := by ring
  · intro l i
    have h := hrFac l i
    dsimp only [r] at h
    field_simp [hWnz l i] at h
    calc
      W' l i = W l i * zeta l * epsilon i := h
      _ = zeta l * W l i * epsilon i := by ring

end AlbertLean.Generic.RealRow
