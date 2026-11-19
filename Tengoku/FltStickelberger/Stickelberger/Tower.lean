module
public import Tengoku
public import Tengoku.FltStickelberger.Stickelberger.DigitSum
public import Tengoku.FltStickelberger.Stickelberger.Teichmuller

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
@[expose] public section

/-!
# The cyclotomic tower for Stickelberger's theorem

Development following L. C. Washington, *Introduction to Cyclotomic
Fields* (2nd ed.), §6.2 (the construction on p. 95–97). To compute the valuation
`s(α)` of a Gauss sum we work over a prime `P` of `ℚ(ζ_{q-1})` above the residue
characteristic `p`, where `q = p^f`. The key numerical facts about that prime —
its inertia degree is `f` and its residue field has `q = p^f` elements — are
sourced entirely from Mathlib's cyclotomic ramification theory
(`IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd`,
`Ideal.absNorm_eq_pow_inertiaDeg'`), not from any other formalization.
-/

open NumberField Ideal IsCyclotomicExtension.Rat

namespace Stickelberger

/-- **Linear binomial approximation mod `x²`.** In any commutative ring, `(1 + x)^k` is
congruent to `1 + k·x` modulo `x²`. Used to expand `ζ_p^{T(a)} = (1 + (ζ_p - 1))^{T(a)}` to first
order modulo `(ζ_p - 1)²` in the Gauss-sum congruence (Washington Lemma 6.12).
@isnad1 id=dvd.0h3v.s7.c38db8c8ab6a from=translated src=- shape=d85d1d30 vocab=242a95b4
-/
theorem sq_dvd_one_add_pow_sub {R : Type*} [CommRing R] (x : R) (k : ℕ) :
    x ^ 2 ∣ (1 + x) ^ k - (1 + k • x) := by
  induction k with
  | zero => simp
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + (n : R) + x * c, ?_⟩
    have hexp : (1 + x) ^ n = x ^ 2 * c + (1 + n • x) := sub_eq_iff_eq_add.mp hc
    rw [pow_succ', hexp]
    push_cast [nsmul_eq_mul]
    ring

/-- **Multiplicity is invariant under a ring automorphism.** For `τ : R ≃+* R`, the induced map
`I ↦ I.map τ` is a multiplicative automorphism of the ideal monoid, so it preserves `emultiplicity`:
`v_{τ P}(τ I) = v_P(I)`. This is the Galois-invariance of valuations used in the Stickelberger
factorization (`v_{σ•𝒫̄}(σ•x) = v_𝒫̄(x)` for `σ` in the Galois group).
@isnad1 id=eq.0h4v.s9.0c31c49f8d92 from=translated src=- shape=0ee08277 vocab=2932ca2f
-/
theorem emultiplicity_map_ringEquiv {R : Type*} [CommRing R] (τ : R ≃+* R) (P I : Ideal R) :
    emultiplicity (P.map (τ : R →+* R)) (I.map (τ : R →+* R)) = emultiplicity P I :=
  emultiplicity_map_eq
    ({ toFun := Ideal.map (τ : R →+* R)
       invFun := Ideal.map (τ.symm : R →+* R)
       left_inv := fun J => by rw [Ideal.map_map]; simp
       right_inv := fun J => by rw [Ideal.map_map]; simp
       map_mul' := Ideal.map_mul τ } : Ideal R ≃* Ideal R)

/-- **A prime containing `p` lies over `(p)`.** If `(p : 𝓞 K) ∈ Q` for a prime `Q` (and `p` a
rational prime), then `Q` lies over `(p)`: the contraction `Q ∩ ℤ` is a prime containing the maximal
ideal `(p)`, hence equals it. Contrapositive: a prime `Q` *not* over `p` does not contain `p` — used
to show the Gauss sum has trivial valuation away from primes over the residue prime.
@isnad1 id=liesover.1h3v.s7.3403cfe90b07 from=translated src=- shape=ee0493aa vocab=8caeb338
-/
theorem liesOver_of_natCast_mem {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {Q : Ideal (𝓞 K)} [Q.IsPrime] (hp_mem : (p : 𝓞 K) ∈ Q) :
    Q.LiesOver (Ideal.span {(p : ℤ)}) := by
  have hmem : (p : ℤ) ∈ Q.under ℤ := by
    rw [Ideal.mem_under]; simpa using hp_mem
  have hle : Ideal.span {(p : ℤ)} ≤ Q.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hmem
  exact ⟨(Int.ideal_span_isMaximal_of_prime p).eq_of_le (Ideal.IsPrime.under ℤ Q).ne_top hle⟩

open scoped Pointwise in
/-- **Galois-invariance of the valuation: `v_{σ•P}(σ•x) = v_P(x)`.** For any group `M` acting on a
commutative ring `R` (`MulSemiringAction`), the `(σ•P)`-multiplicity of `σ•x` equals the
`P`-multiplicity of `x`, since `σ` acts by the ring automorphism `MulSemiringAction.toRingEquiv`.
Applied with `M = Gal(L/ℚ)` acting on `𝓞 L`, this lets the exponent of a conjugate prime `σ•𝒫̄` in
`(σ•g)` be read off from that of `𝒫̄` in `(g)` — the symmetry behind the factorization.
@isnad1 id=eq.0h5v.s8.f61a04bfff99 from=translated src=- shape=de4cf1b1 vocab=ef6396c3
-/
theorem emultiplicity_smul {M R : Type*} [Group M] [CommRing R] [MulSemiringAction M R]
    (σ : M) (P : Ideal R) (x : R) :
    emultiplicity (σ • P) (Ideal.span {σ • x}) = emultiplicity P (Ideal.span {x}) := by
  have hτ : (MulSemiringAction.toRingEquiv M R σ : R →+* R) = MulSemiringAction.toRingHom M R σ :=
    RingHom.ext (congrFun rfl)
  rw [Ideal.pointwise_smul_def, show σ • x = MulSemiringAction.toRingHom M R σ x from rfl,
    show (Ideal.span {MulSemiringAction.toRingHom M R σ x} : Ideal R)
      = (Ideal.span {x}).map (MulSemiringAction.toRingHom M R σ) from by
        rw [Ideal.map_span, Set.image_singleton], ← hτ]
  exact emultiplicity_map_ringEquiv (MulSemiringAction.toRingEquiv M R σ) P (Ideal.span {x})

/-- **Valuation from congruence.** If `v_P(b) = 1` and `a ≡ b (mod P²)`, then `v_P(a) = 1`.
(`a ∈ P` since `b ∈ P` and `a - b ∈ P² ⊆ P`; `a ∉ P²` else `b = a - (a-b) ∈ P²`.) This turns
the congruence `g(ω⁻¹) ≡ ζ_p - 1 (mod 𝒫̄²)` into `s(1) = v(g(ω⁻¹)) = v(ζ_p-1) = 1`.
@isnad1 id=eq.2h4v.s9.f3f6b2958ce6 from=translated src=- shape=d94287ed vocab=94b9f148
-/
theorem emultiplicity_eq_one_of_sub_mem {K : Type*} [Field K] [NumberField K]
    {P : Ideal (𝓞 K)} {a b : 𝓞 K}
    (hb : emultiplicity P (Ideal.span {b}) = 1) (hab : a - b ∈ P ^ 2) :
    emultiplicity P (Ideal.span {a}) = 1 := by
  have hbP : b ∈ P := by
    have h1 : P ^ 1 ∣ Ideal.span {b} := pow_dvd_iff_le_emultiplicity.mpr (by simp [hb])
    rwa [pow_one, Ideal.dvd_span_singleton] at h1
  have hbP2 : b ∉ P ^ 2 := by
    intro h
    have h2 := le_emultiplicity_of_pow_dvd (Ideal.dvd_span_singleton.mpr h)
    rw [hb] at h2
    simp at h2
  have hP2P : P ^ 2 ≤ P := Ideal.pow_le_self (by norm_num)
  have haP : a ∈ P := by
    have hsum : a = b + (a - b) := by ring
    rw [hsum]; exact P.add_mem hbP (hP2P hab)
  have haP2 : a ∉ P ^ 2 := by
    intro h
    refine hbP2 ?_
    have hsum : b = a - (a - b) := by ring
    rw [hsum]; exact (P ^ 2).sub_mem h hab
  refine emultiplicity_eq_of_dvd_of_not_dvd (k := 1) ?_ ?_
  · rw [pow_one, Ideal.dvd_span_singleton]; exact haP
  · rw [Ideal.dvd_span_singleton]; exact haP2

end Stickelberger
