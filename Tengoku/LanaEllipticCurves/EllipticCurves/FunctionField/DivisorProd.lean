/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FunctionField.Divisors

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-product laws for the order of vanishing and the divisor (issue #465)

For a Weierstrass curve `W` over a field `F` whose affine coordinate ring `F[W]` is a Dedekind
domain, `Reduction`/`FunctionField/Divisors.lean` establishes that `ord v` and `divisor W` are
homomorphisms on nonzero arguments: `ord_mul`, `divisor_mul`, `ord_pow`, `divisor_pow`.  This file
extends those two-factor/power laws to **arbitrary finite products** over a `Finset`:

* `ord_prod`     : `ord v (∏ i ∈ s, f i) = ∑ i ∈ s, ord v (f i)`;
* `divisor_prod` : `divisor W (∏ i ∈ s, f i) = ∑ i ∈ s, divisor W (f i)`,

each under the hypothesis that every factor is nonzero on `s`.

These are the finite-product companions of the merged `ord_mul` / `divisor_mul` (`Divisors.lean`)
and `divisor_pow` (`NthRootOfPullback.lean`, PR #150).  They are the exact tool consumed by the
**product-over-`⟨T⟩` / divisor-telescoping** argument for the alternating property of the
divisor-theoretic Weil pairing (`e_n(T, T) = 1`, Silverman AEC III.8.1(b), issue #465 deliverable
2): there one forms `h := ∏_{i} τ_{iT}∗ f_T` and computes `divisor W h` by pushing the divisor
through the product — precisely `divisor_prod`.

⚠️ **This paragraph used to list *"a divisor-pullback-under-translation formula for
`translateEndo`"* first among *"the argument's remaining ingredients"*.  It is not remaining**: the
projective one is `divisorProj_translateEndo` (`EllipticCurves.FunctionField.PlaceOrder`, `#658`),
downstream of this file, and it is what the telescoping argument rewrites with; only the **affine**
formula is undelivered, and `EllipticCurves.FunctionField.DivisorTransport` is where that is
recorded.  ⚠️ The other two ingredients that sentence listed — `divisor W g_T = [n]∗(T)`, which is
`#418`, and the `⟨T⟩` enumeration with the `{(1 − i)T} = {−iT}` multiset telescoping — are **not**
adjudicated here, in either direction.  This file lands the reusable, fully ungated product
homomorphism law that they all consume.

## References

Silverman, *The Arithmetic of Elliptic Curves*, II.3 (divisors) and III.8 (the Weil pairing).
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]
  (v : HeightOneSpectrum W.CoordinateRing)

/-- **Finite-product law for the order of vanishing.** If every factor `f i` (`i ∈ s`) is nonzero,
then the order of vanishing of the product at a closed point `v` is the sum of the orders:
`ord v (∏ i ∈ s, f i) = ∑ i ∈ s, ord v (f i)`.  The finite-product companion of `ord_mul`. -/
lemma ord_prod {ι : Type*} (s : Finset ι) (f : ι → W.FunctionField)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    ord v (∏ i ∈ s, f i) = ∑ i ∈ s, ord v (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have hfa : f a ≠ 0 := hf a (Finset.mem_cons_self a s)
    have hmem : ∀ i ∈ s, f i ≠ 0 := fun i hi => hf i (Finset.mem_cons_of_mem hi)
    have hprod : ∏ i ∈ s, f i ≠ 0 := Finset.prod_ne_zero_iff.2 hmem
    rw [Finset.prod_cons, Finset.sum_cons, ord_mul v hfa hprod, ih hmem]

variable (W) in
/-- **Finite-product law for the divisor.** If every factor `f i` (`i ∈ s`) is nonzero, then the
divisor of the product is the sum of the divisors: `divisor W (∏ i ∈ s, f i) = ∑ i ∈ s, divisor W
(f i)`.  The finite-product companion of `divisor_mul`; the tool the Weil-pairing alternating
property's product-over-`⟨T⟩` telescoping consumes (issue #465). -/
lemma divisor_prod {ι : Type*} (s : Finset ι) (f : ι → W.FunctionField)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    divisor W (∏ i ∈ s, f i) = ∑ i ∈ s, divisor W (f i) := by
  ext v
  simp only [divisor_apply, Finsupp.finsetSum_apply]
  exact ord_prod v s f hf

end WeierstrassCurve.Affine
