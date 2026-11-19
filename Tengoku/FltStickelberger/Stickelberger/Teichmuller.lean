module
public import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
@[expose] public section

/-!
# The Teichmüller character of a prime of a cyclotomic field

Development following L. C. Washington, *Introduction to Cyclotomic
Fields* (2nd ed.), §6.2 (p. 95): if `K = ℚ(ζ_n)` and `𝔭` is a prime of `𝓞 K`
above `p` whose residue field `𝓞 K ⧸ 𝔭` has `q = n + 1` elements, then the
`n`-th roots of unity of `𝓞 K` map bijectively onto `(𝓞 K ⧸ 𝔭)ˣ`. Inverting
this bijection gives the **Teichmüller character** `ω = ω_𝔭`, the unique
multiplicative character `(𝓞 K ⧸ 𝔭)ˣ → (𝓞 K)ˣ` lifting the identity, i.e.
`ω(a) ≡ a (mod 𝔭)`.

This is built directly on Mathlib's `Ideal.rootsOfUnityMapQuot` and
`MulChar.ofUnitHom`; no other formalization is consulted.
-/

open NumberField Ideal

namespace Stickelberger

variable {K : Type*} [Field K] [NumberField K]

/-- A primitive `n`-th root of unity in `𝓞 K`, for `K` the `n`-th cyclotomic field.-/
noncomputable def zetaInteger (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ K] : 𝓞 K :=
  (IsCyclotomicExtension.zeta_spec n ℚ K).toInteger

/--
@isnad1 id=isprimit.0h2v.s5.ca8b5d81fcc3 from=translated src=- shape=39e99e01 vocab=eb827501
-/
theorem zetaInteger_isPrimitiveRoot (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ K] :
    IsPrimitiveRoot (zetaInteger (K := K) n) n :=
  (IsCyclotomicExtension.zeta_spec n ℚ K).toInteger_isPrimitiveRoot

end Stickelberger
