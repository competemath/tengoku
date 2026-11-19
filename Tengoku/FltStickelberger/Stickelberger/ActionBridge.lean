module
public import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
@[expose] public section

/-!
# Bridging the two Galois actions on the ring of integers

There are two propositionally-equal-but-not-defeq `MulSemiringAction (K ≃ₐ[ℚ] K) (𝓞 K)`
instances in play:

* `IsIntegralClosure.MulSemiringAction ℤ ℚ K (𝓞 K)` — the AKLB action via `galRestrict`
  (used in this development as `Stickelberger.galMulSemiringAction`), and
* the canonical `NumberField.RingOfIntegers` action inherited from `AlgEquiv.aut` on `K`
  (the one Mathlib's `IsCyclotomicExtension.Rat.galEquivZMod_stabilizer` is stated against).

Both send `x` to the (unique) element of `𝓞 K` whose image under `algebraMap (𝓞 K) K` is
`σ (algebraMap (𝓞 K) K x)`, so by injectivity of `algebraMap` they coincide. We record their
equality here so that stabilizer/orbit statements proved with one instance transfer to the other.

This file deliberately imports only `Mathlib` (not the `galMulSemiringAction` instance), so that
the `inferInstance` on the right-hand side of `galMul_eq_canonical` resolves to the canonical
`RingOfIntegers` action.
-/

open NumberField

namespace Stickelberger

/-- A `MulSemiringAction` is determined by its underlying `DistribMulAction`: the remaining
`smul_one`/`smul_mul` fields are propositions.
@isnad1 id=eq.1h4v.s5.d8ca741579c0 from=translated src=- shape=27b8154f vocab=c71e1a1f
-/
theorem msa_eq_of_distrib {M R : Type*} [Monoid M] [Semiring R] (a b : MulSemiringAction M R)
    (hd : a.toDistribMulAction = b.toDistribMulAction) : a = b := by
  cases a; cases b; congr 1

variable {K : Type*} [Field K] [NumberField K]

/-- **The two Galois actions on `𝓞 K` agree.** The AKLB action
`IsIntegralClosure.MulSemiringAction ℤ ℚ K (𝓞 K)` (used as `galMulSemiringAction`) equals the
canonical `RingOfIntegers` action. Both satisfy `algebraMap (σ • x) = σ (algebraMap x)`, and
`algebraMap (𝓞 K) K` is injective, so they coincide as `MulSemiringAction`s.
@isnad1 id=eq.0h1v.s8.bc10639d8c9d from=translated src=- shape=be48467e vocab=52a25480
-/
theorem galMul_eq_canonical :
    (IsIntegralClosure.MulSemiringAction ℤ ℚ K (𝓞 K) : MulSemiringAction (K ≃ₐ[ℚ] K) (𝓞 K))
      = (inferInstance : MulSemiringAction (K ≃ₐ[ℚ] K) (𝓞 K)) := by
  apply msa_eq_of_distrib
  ext g x
  rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap]
  trans (g (algebraMap (𝓞 K) K x))
  · exact algebraMap_galRestrict_apply ℤ g x
  · exact ((by simpa using algebraMap.smul' g x K) :
      algebraMap (𝓞 K) K (g • x) = g (algebraMap (𝓞 K) K x)).symm

/-- **Abstract β-twist cancellation (the heart of the direct-invariance descent).** Suppose `g`
spans an `H`-stable line with `m`-th-root-of-unity scalars (`∀ τ ∈ H, τ g = u·g` with `uᵐ = 1`),
`σ_c` acts as the `c`-power on all `m`-th roots of unity, and `σ_c` commutes with every `τ ∈ H`.
Then `g^c · (σ_c g)⁻¹` is fixed by `H` — the scalar cancels:
`τ(g^c (σ_c g)⁻¹) = (u g)^c (u^c σ_c g)⁻¹ = g^c (σ_c g)⁻¹`. Instantiated with `g` the Gauss sum in
`L` and `H = Gal(L/ℚ(ζ_m))`, this yields `γ^{c-σ_c} ∈ ℚ(ζ_m)` — Washington's descent without the
Kummer-unramified detour.
@isnad1 id=mem.4h7v.s10.20d10ef10011 from=translated src=- shape=d708b084 vocab=384476aa
-/
theorem twist_fixed {F L : Type*} [Field F] [Field L] [Algebra F L]
    {H : Subgroup (L ≃ₐ[F] L)} {g : L} {σc : L ≃ₐ[F] L} {m c : ℕ} (hm : 0 < m)
    (heig : ∀ τ ∈ H, ∃ u : L, u ^ m = 1 ∧ τ g = u * g)
    (hσc : ∀ u : L, u ^ m = 1 → σc u = u ^ c)
    (hcomm : ∀ τ ∈ H, ∀ x : L, τ (σc x) = σc (τ x)) :
    g ^ c * (σc g)⁻¹ ∈ IntermediateField.fixedField H := by
  rw [IntermediateField.mem_fixedField_iff]
  intro τ hτ
  obtain ⟨u, hum, hu⟩ := heig τ hτ
  have hu0 : u ≠ 0 := fun h => by rw [h, zero_pow hm.ne'] at hum; exact zero_ne_one hum
  have hucne : (u : L) ^ c ≠ 0 := pow_ne_zero c hu0
  rw [map_mul, map_pow, hu, map_inv₀, hcomm τ hτ g, hu, map_mul, hσc u hum,
    mul_pow, mul_inv, mul_mul_mul_comm, mul_inv_cancel₀ hucne, one_mul]

/-- **The Galois group of a cyclotomic extension of `ℚ` is abelian** (it embeds into `(ZMod n)ˣ` via
`galEquivZMod`). So any two automorphisms commute as functions — discharges
the `hcomm` hypothesis of
`twist_fixed` (`σ_c` commutes with `Gal(L/ℚ(ζ_m))`).
@isnad1 id=eq.0h5v.s8.75979c9bc1ed from=translated src=- shape=e7084cdc vocab=4984dbf7
-/
theorem galEquiv_apply_comm {n : ℕ} [NeZero n] {L : Type*} [Field L] [NumberField L]
    [IsCyclotomicExtension {n} ℚ L] (σ τ : L ≃ₐ[ℚ] L) (x : L) : τ (σ x) = σ (τ x) := by
  have h : σ * τ = τ * σ := by
    apply (IsCyclotomicExtension.Rat.galEquivZMod n L).injective
    rw [map_mul, map_mul, mul_comm]
  have h2 := DFunLike.congr_fun h x
  simpa [AlgEquiv.mul_apply] using h2.symm

end Stickelberger
