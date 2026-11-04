/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.RingTheory.GradedAlgebra.HomogeneousLocalization
import Tengoku.Seed.RingTheory.Localization.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Domain properties of homogeneous localizations

`HomogeneousLocalization 𝒜 S` is by construction a subring of the ordinary
localization `Localization S`, through the injective map
`HomogeneousLocalization.val`. Thus a homogeneous localization of a domain at
nonzerodivisors is again a domain.

The `Away` specialization records nontriviality and the domain property away
from a nonzero element, and reducedness for every element. These are statements
about graded rings and localization only. Projective-spectrum geometry consumes
them when proving that the standard affine charts of `Proj 𝒜` are reduced or
integral.
-/

open scoped nonZeroDivisors

namespace HomogeneousLocalization

variable {ι σ A : Type*} [AddCommMonoid ι] [DecidableEq ι] [CommRing A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

/-- A homogeneous localization at a multiplicative set of nonzerodivisors is a domain, provided
it is nontrivial.
@isnad1 id=isdomain.1h5v.s7.a7440e5eef6f from=translated src=- shape=959191f6 vocab=6b9ef292
-/
theorem isDomain_of_le_nonZeroDivisors [IsDomain A] (S : Submonoid A)
    (hS : S ≤ A⁰) :
    IsDomain (HomogeneousLocalization 𝒜 S) := by
  haveI : IsDomain (Localization S) := IsLocalization.isDomain_localization hS
  exact Function.Injective.isDomain
    (algebraMap (HomogeneousLocalization 𝒜 S) (Localization S)) (val_injective S)

/-- A homogeneous localization at a multiplicative set of nonzerodivisors of a nontrivial ring
is nontrivial: `val` is injective, so a trivial source would force `0 = 1` in the target.
@isnad1 id=nontrivi.1h5v.s7.62d5f94aebd9 from=translated src=- shape=e7873b41 vocab=3d0f4213
-/
theorem nontrivial_of_le_nonZeroDivisors [IsDomain A] (S : Submonoid A) (hS : S ≤ A⁰) :
    Nontrivial (HomogeneousLocalization 𝒜 S) := by
  haveI : IsDomain (Localization S) := IsLocalization.isDomain_localization hS
  refine ⟨0, 1, fun h ↦ ?_⟩
  have h0 : (0 : HomogeneousLocalization 𝒜 S).val = (1 : HomogeneousLocalization 𝒜 S).val :=
    congrArg HomogeneousLocalization.val h
  rw [val_zero, val_one] at h0
  exact zero_ne_one (α := Localization S) h0

/-- Away from a nonzero element of a graded domain the homogeneous localization is nontrivial.

Nonzero is needed and not cosmetic: away from `0` the localization is the zero ring, since
`0 = 0 ^ 1` lies in the powers of `0`.
@isnad1 id=nontrivi.1h5v.s6.fe5395101803 from=translated src=- shape=7f2ac85e vocab=1ceace1f
-/
theorem Away.nontrivial [IsDomain A] {f : A} (hf : f ≠ 0) :
    Nontrivial (HomogeneousLocalization.Away 𝒜 f) := by
  refine nontrivial_of_le_nonZeroDivisors 𝒜 (Submonoid.powers f) ?_
  rintro _ ⟨n, rfl⟩
  exact pow_mem (mem_nonZeroDivisors_of_ne_zero hf) n

/-- Away from a nonzero element of a graded domain, the degree-zero homogeneous localization is
a domain.

Nonzero is what puts the powers of `f` among the nonzerodivisors; away from `0` the ring is
trivial instead.
@isnad1 id=isdomain.1h5v.s7.197bcc1b416b from=translated src=- shape=e2ab6e79 vocab=fe149663
-/
theorem Away.isDomain [IsDomain A] {f : A} (hf : f ≠ 0) :
    IsDomain (HomogeneousLocalization.Away 𝒜 f) := by
  refine isDomain_of_le_nonZeroDivisors 𝒜 (Submonoid.powers f) ?_
  rintro _ ⟨n, rfl⟩
  exact pow_mem (mem_nonZeroDivisors_of_ne_zero hf) n

/-- Every degree-zero homogeneous localization of a graded domain is reduced: away from a
nonzero element it is a domain, and away from zero it is the zero ring.
@isnad1 id=isreduce.0h5v.s6.5ae557fbc9ba from=translated src=- shape=3eff3f61 vocab=1f380c35
-/
theorem Away.isReduced [IsDomain A] (f : A) :
    IsReduced (HomogeneousLocalization.Away 𝒜 f) := by
  by_cases hf : f = 0
  · subst hf
    haveI : Subsingleton (HomogeneousLocalization.Away 𝒜 (0 : A)) :=
      HomogeneousLocalization.subsingleton 𝒜 ⟨1, pow_one 0⟩
    infer_instance
  · haveI := Away.isDomain 𝒜 hf
    infer_instance

end HomogeneousLocalization
