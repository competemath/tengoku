import Tengoku.PcfCyclotomicLean.IngramMello.Statements

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Mann's theorem on vanishing sums of roots of unity

Source: H. B. Mann, *On linear relations between roots of unity*, Mathematika 12 (1965),
107–117. Rational-coefficient form: in a minimal vanishing relation `∑ cᵢ ζᵢ = 0` among `k`
roots of unity with rational coefficients, all ratios `ζᵢ/ζⱼ` satisfy
`(ζᵢ/ζⱼ)^{k!} = 1` (`IngramMello.mann`). The proof uses only the irreducibility of
cyclotomic polynomials over `ℚ` (through embeddings `ℚ⟮ω⟯ → ℂ`) and the geometric
sum of a primitive `p`-th root of unity. This is the arithmetic input for the proof
of `Laurent`.
-/

namespace IngramMello

open Polynomial Finset IntermediateField

/-! ### The Fourier identity for a primitive `p`-th root of unity -/

/-- `∑_{m<p} ξ^{m a} = p` if `p ∣ a` and `0` otherwise, for a primitive `p`-th root `ξ`,
`p` prime.
@isnad1 id=eq.2h3v.s6.da246cfc8f58 from=translated src=- shape=9c701607 vocab=b6079511
-/
theorem sum_pow_mul_primitiveRoot {p : ℕ} (hp : p.Prime) {ξ : ℂ} (hξ : IsPrimitiveRoot ξ p)
    (a : ℕ) :
    ∑ m ∈ range p, ξ ^ (m * a) = if p ∣ a then (p : ℂ) else 0 := by
  have h1 : ∀ m, ξ ^ (m * a) = (ξ ^ a) ^ m := fun m => by rw [mul_comm, pow_mul]
  simp_rw [h1]
  split_ifs with hd
  · rw [(hξ.pow_eq_one_iff_dvd a).2 hd]
    simp
  · have hcop : a.Coprime p := (Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hd)
    exact (hξ.pow_of_coprime a hcop).geom_sum_eq_zero hp.one_lt

/-! ### Embeddings of `ℚ⟮ω⟯` moving `ω` to `ω^b` -/

/-! ### The one-prime step -/

/-- For `m < p`, the residue class filter `p ∣ a + (p - j)` means `a ≡ j (mod p)`; two
different classes `j ≠ j'` are disjoint.-/
theorem eq_of_dvd_add_sub {p a j j' : ℕ} (hj : j < p) (hj' : j' < p)
    (h : p ∣ a + (p - j)) (h' : p ∣ a + (p - j')) : j = j' := by
  rcases le_total j j' with hle | hle
  · have hd : p ∣ (a + (p - j)) - (a + (p - j')) := Nat.dvd_sub h h'
    have he : (a + (p - j)) - (a + (p - j')) = j' - j := by omega
    rw [he] at hd
    have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega
  · have hd : p ∣ (a + (p - j')) - (a + (p - j)) := Nat.dvd_sub h' h
    have he : (a + (p - j')) - (a + (p - j)) = j - j' := by omega
    rw [he] at hd
    have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega

/-! ### Mann's theorem -/

/-- A finite family of roots of unity has a common positive exponent.
@isnad1 id=ex.1h2v.s5.fd321c25fd64 from=translated src=- shape=4c33e858 vocab=21db454e
-/
theorem exists_common_exponent {k : ℕ} (ζ : Fin k → ℂ) (hζ : ∀ i, IsRootOfUnityC (ζ i)) :
    ∃ n : ℕ, 0 < n ∧ ∀ i, ζ i ^ n = 1 := by
  choose N hN using hζ
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => (hN i).1, fun i => ?_⟩
  obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ i)
  rw [ht, pow_mul, (hN i).2, one_pow]

/--
@isnad1 id=ne.1h1v.s3.16cdba658bd7 from=translated src=- shape=4f29f389 vocab=fec7638c
-/
theorem IsRootOfUnityC.ne_zero {ζ : ℂ} (h : IsRootOfUnityC ζ) : ζ ≠ 0 := by
  obtain ⟨n, hn, hζ⟩ := h
  rintro rfl
  rw [zero_pow hn.ne'] at hζ
  exact zero_ne_one hζ

/--
@isnad1 id=isrootof.2h2v.s4.2d23a5122ccf from=translated src=- shape=255dce7b vocab=6f96d468
-/
theorem IsRootOfUnityC.mul {ζ₁ ζ₂ : ℂ} (h₁ : IsRootOfUnityC ζ₁) (h₂ : IsRootOfUnityC ζ₂) :
    IsRootOfUnityC (ζ₁ * ζ₂) := by
  obtain ⟨n₁, hn₁, h₁⟩ := h₁
  obtain ⟨n₂, hn₂, h₂⟩ := h₂
  refine ⟨n₁ * n₂, Nat.mul_pos hn₁ hn₂, ?_⟩
  rw [mul_pow, pow_mul, h₁, one_pow, mul_comm n₁, pow_mul, h₂, one_pow, one_mul]

/--
@isnad1 id=isrootof.1h1v.s3.0cd8c03088aa from=translated src=- shape=23658224 vocab=466a17f2
-/
theorem IsRootOfUnityC.inv {ζ : ℂ} (h : IsRootOfUnityC ζ) : IsRootOfUnityC ζ⁻¹ := by
  obtain ⟨n, hn, hζ⟩ := h
  exact ⟨n, hn, by rw [inv_pow, hζ, inv_one]⟩

/--
@isnad1 id=isrootof.1h2v.s4.0dc0a3f57429 from=translated src=- shape=17957909 vocab=b729923c
-/
theorem IsRootOfUnityC.pow {ζ : ℂ} (h : IsRootOfUnityC ζ) (m : ℕ) : IsRootOfUnityC (ζ ^ m) := by
  obtain ⟨n, hn, hζ⟩ := h
  exact ⟨n, hn, by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]⟩

/--
@isnad1 id=isrootof.1h2v.s4.fa5b95a86cce from=translated src=- shape=17957909 vocab=336dc061
-/
theorem IsRootOfUnityC.zpow {ζ : ℂ} (h : IsRootOfUnityC ζ) (m : ℤ) : IsRootOfUnityC (ζ ^ m) := by
  rcases Int.natAbs_eq m with hm | hm
  · rw [hm, zpow_natCast]; exact h.pow _
  · rw [hm, zpow_neg, zpow_natCast]; exact (h.pow _).inv

end IngramMello
