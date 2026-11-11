/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku.Seed.Data.Fintype.Card
public import Tengoku.Seed.GroupTheory.QuotientGroup.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Singular Kummer: finite group comparison

This file proves the elementary finite-group fact used at the start of the
singular-group construction.

For a finite abelian group `A`, the elementary quotient

```text
A / pA
```

is nontrivial if and only if the subgroup

```text
A[p] = {x : A | p • x = 0}
```

is nontrivial.  The proof is only the finite endomorphism fact that an
endomorphism of a finite type is injective if and only if it is surjective.

The component-refined statement will require the same comparison after passing
to character components; this file isolates the group-theoretic core.
-/

@[expose] public section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

variable {A : Type*} [AddCommGroup A]

/-- The subgroup `nA` of `n`-multiples in an additive abelian group.-/
abbrev multiplesSubgroup (A : Type*) [AddCommGroup A] (n : ℕ) : AddSubgroup A :=
  (nsmulAddMonoidHom (α := A) n).range

/-- The subgroup `A[n]` of elements killed by `n`.-/
abbrev torsionBySubgroup (A : Type*) [AddCommGroup A] (n : ℕ) : AddSubgroup A :=
  (nsmulAddMonoidHom (α := A) n).ker

/-- The elementary quotient `A / nA`, written additively.-/
abbrev elementaryQuotient (A : Type*) [AddCommGroup A] (n : ℕ) : Type _ :=
  A ⧸ multiplesSubgroup A n

/-- For an endomorphism of a finite additive abelian group, the quotient by its
range is nontrivial if and only if its kernel is nontrivial.
@isnad1 id=iff.0h2v.s6.13468e96dacb from=translated src=- shape=d0679de6 vocab=166584d0
-/
theorem quotient_range_nontrivial_iff_ker_nontrivial
    [Finite A] (f : A →+ A) :
    Nontrivial (A ⧸ f.range) ↔ Nontrivial f.ker := by
  rw [QuotientAddGroup.nontrivial_iff]
  rw [AddSubgroup.nontrivial_iff_ne_bot]
  constructor
  · intro h_range h_ker
    exact h_range ((AddMonoidHom.range_eq_top).2
      (Finite.injective_iff_surjective.1
        ((AddMonoidHom.ker_eq_bot_iff f).1 h_ker)))
  · intro h_ker h_range
    exact h_ker ((AddMonoidHom.ker_eq_bot_iff f).2
      (Finite.injective_iff_surjective.2
        ((AddMonoidHom.range_eq_top).1 h_range)))

/-- The quotient `A / nA` is nontrivial if and only if `A[n]` is nontrivial.
@isnad1 id=iff.0h2v.s5.2a046613bfea from=translated src=- shape=654fd580 vocab=cd342718
-/
theorem elementaryQuotient_nontrivial_iff_torsionBySubgroup_nontrivial
    [Finite A] (n : ℕ) :
    Nontrivial (elementaryQuotient A n) ↔ Nontrivial (torsionBySubgroup A n) :=
  quotient_range_nontrivial_iff_ker_nontrivial
    (A := A) (nsmulAddMonoidHom (α := A) n)

/-- The direction used to pass from a nonzero elementary quotient to
`n`-torsion.
@isnad1 id=nontrivi.1h2v.s5.2f33a39f75ff from=translated src=- shape=ecec68fa vocab=cd342718
-/
theorem torsionBySubgroup_nontrivial_of_elementaryQuotient_nontrivial
    [Finite A] {n : ℕ} :
    Nontrivial (elementaryQuotient A n) → Nontrivial (torsionBySubgroup A n) :=
  (elementaryQuotient_nontrivial_iff_torsionBySubgroup_nontrivial
    (A := A) n).1

/-- The reverse direction, useful when switching back from `n`-torsion to the
elementary quotient.
@isnad1 id=nontrivi.1h2v.s5.5e5948c118e9 from=translated src=- shape=6f4dfad4 vocab=cd342718
-/
theorem elementaryQuotient_nontrivial_of_torsionBySubgroup_nontrivial
    [Finite A] {n : ℕ} :
    Nontrivial (torsionBySubgroup A n) → Nontrivial (elementaryQuotient A n) :=
  (elementaryQuotient_nontrivial_iff_torsionBySubgroup_nontrivial
    (A := A) n).2

end SingularKummer
end Reflection
end BernoulliRegular

end
