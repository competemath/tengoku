/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.RingTheory.Huber.Restricted.TwoSidedSeries.Basic
public import Tengoku.Tauceti.TauCeti.Topology.Algebra.Nonarchimedean.DiscreteConvolution

/-!
# Convolution of two-sided restricted series

The coefficient family underlying a two-sided restricted series is closed under additive
convolution.  For restricted families `f g : ℤ → A`, the coefficient at `n` is

```text
∑' (i,j), i + j = n, f i * g j.
```

The products `f i * g j` tend to zero cofinitely on `ℤ × ℤ`; completeness of `A` upgrades this
to summability on every addition fiber. The resulting coefficients again tend to zero: modulo an
open additive subgroup, only finitely many pairs contribute, hence only their finitely many degrees
can contribute.

This supplies the analytic part of multiplication on Wedhorn's `A⟨X, X⁻¹⟩` (Example 6.39).
This module constructs the bilinear convolution; the unit and the ring structure are built in
`TauCeti.RingTheory.Huber.Restricted.TwoSidedSeries.Ring`.

## Main results

* `TauCeti.Huber.addConvolutionExists_of_mem_twoSidedRestrictedSubmodule`: every coefficient
  convolution is summable.
* `TauCeti.Huber.addRingConvolution_mem_twoSidedRestrictedSubmodule`: convolution preserves the
  two-sided restricted condition.
* `TauCeti.Huber.twoSidedRestrictedMul`: convolution as a bilinear map on the restricted
  coefficient module.
* `TauCeti.Huber.twoSidedRestrictedMul_comm`: commutativity of this multiplication.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Example 6.39 and Lemma 8.33.
-/

public section

open Filter Topology
open scoped DiscreteConvolution

namespace TauCeti.Huber

section Convergence

section Summability

variable {A : Type*} [Ring A] [UniformSpace A] [IsUniformAddGroup A]
  [NonarchimedeanRing A] [CompleteSpace A]

/-- In a complete nonarchimedean ring, the convolution coefficients of two two-sided restricted
families are summable. -/
theorem addConvolutionExists_of_mem_twoSidedRestrictedSubmodule
    {f g : ℤ → A} (hf : f ∈ twoSidedRestrictedSubmodule A A)
    (hg : g ∈ twoSidedRestrictedSubmodule A A) :
    DiscreteConvolution.AddConvolutionExists (.mul ℕ A) f g :=
  TauCeti.addConvolutionExists_of_zeroAtFilter_cofinite
    (mem_twoSidedRestrictedSubmodule.mp hf) (mem_twoSidedRestrictedSubmodule.mp hg)

end Summability

section Preservation

variable {A : Type*} [Ring A] [TopologicalSpace A] [NonarchimedeanRing A]

end Preservation

end Convergence

section Bilinear

variable {A : Type*} [CommRing A] [UniformSpace A] [hA : IsUniformAddGroup A]
  [NonarchimedeanRing A] [hComplete : CompleteSpace A] [T2Space A]

end Bilinear

end TauCeti.Huber

end
