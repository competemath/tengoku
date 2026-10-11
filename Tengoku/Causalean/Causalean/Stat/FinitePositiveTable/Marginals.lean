module
public import Tengoku.Causalean.Causalean.Stat.FinitePositiveTable.Basic
public import Tengoku

/-!
# Marginals and finite conditional masses

This module defines marginals and conditional masses for finite real tables, proving positivity
of conditioning denominators and normalization of each conditional row.
-/

@[expose] public section

open Finset
open scoped BigOperators

noncomputable section

namespace Causalean.Stat.FinitePositiveTable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {r : V → ℕ}

/-- The [kernel](hyp:q), [fixed coordinate set](hyp:S), and [reference profile](hyp:x) determine
[the kernel's marginal mass](goal) [by summing over compatible complete profiles](step:1). -/
def kernelMarginalMass (q : Kernel r) (S : Finset V) (x : ProfileSpace r) : ℝ :=
  fiberSum q S x

/-- The [positive table](hyp:p), [fixed coordinate set](hyp:S), and [reference profile](hyp:x)
determine [the table's marginal mass](goal) [as its kernel marginal](step:1). -/
def marginalMass (p : PositiveTable r) (S : Finset V) (x : ProfileSpace r) : ℝ :=
  kernelMarginalMass p.mass S x

/-- The [kernel](hyp:q) has [pointwise strict positivity](goal) [when every complete profile has
positive real mass](step:1). -/
def Kernel.IsStrictlyPositive (q : Kernel r) : Prop := ∀ x, 0 < q x

/-- For [a pointwise strictly positive kernel](hyp:q,hq), [a fixed coordinate set](hyp:S), and
[a reference profile](hyp:x), [the kernel marginal is strictly positive](goal).
@isnad1 id=lt.1h5v.s5.2093d62e0fa7 from=translated src=- shape=93536175 vocab=02347857
-/
theorem kernelMarginalMass_pos {q : Kernel r} (hq : q.IsStrictlyPositive)
    (S : Finset V) (x : ProfileSpace r) : 0 < kernelMarginalMass q S x := by
  unfold kernelMarginalMass fiberSum
  apply Finset.sum_pos'
  · intro y hy
    split_ifs
    · exact (hq y).le
    · exact le_rfl
  · refine ⟨x, Finset.mem_univ x, ?_⟩
    simp [AgreeOn, hq x]

/-- For [a positive table](hyp:p), [a fixed coordinate set](hyp:S), and [a reference
profile](hyp:x), [the table marginal is strictly positive](goal).
@isnad1 id=lt.0h5v.s5.b9dd7a599f5c from=translated src=- shape=398d456f vocab=928d0bee
-/
theorem marginalMass_pos (p : PositiveTable r) (S : Finset V) (x : ProfileSpace r) :
    0 < marginalMass p S x := by
  exact kernelMarginalMass_pos p.mass_pos S x

/-- For [a positive table](hyp:p), [a fixed coordinate set](hyp:S), and [a reference
profile](hyp:x), [the table marginal is nonzero](goal).
@isnad1 id=ne.0h5v.s5.afdcaae19440 from=translated src=- shape=e15ba54a vocab=8f52eb8b
-/
theorem marginalMass_ne_zero (p : PositiveTable r) (S : Finset V) (x : ProfileSpace r) :
    marginalMass p S x ≠ 0 := by
  exact (marginalMass_pos p S x).ne'

/-- For [a positive table](hyp:p) and [a reference profile](hyp:x), [the marginal with no
coordinates fixed equals one](goal).
@isnad1 id=eq.0h4v.s5.d1713a9cac8e from=translated src=- shape=3fc03d7e vocab=cf9c919e
-/
theorem marginalMass_empty (p : PositiveTable r) (x : ProfileSpace r) :
    marginalMass p ∅ x = 1 := by
  unfold marginalMass kernelMarginalMass
  rw [fiberSum_empty]
  exact p.sum_mass_eq_one

/-- For [a positive table](hyp:p) and [a reference profile](hyp:x), [the marginal fixing every
coordinate equals the profile's own mass](goal).
@isnad1 id=eq.0h4v.s5.d55af702c49c from=translated src=- shape=131d20b4 vocab=38c965a6
-/
theorem marginalMass_univ (p : PositiveTable r) (x : ProfileSpace r) :
    marginalMass p Finset.univ x = p.mass x := by
  exact fiberSum_univ p.mass x

/-- The [kernel](hyp:q), [coordinate and conditioning set](hyp:v,C), [reference profile](hyp:x),
and [proposed coordinate value](hyp:z) determine [the kernel conditional mass](goal) [as the
joint marginal divided by the conditioning marginal](step:1). -/
def kernelConditionalMass (q : Kernel r) (v : V) (C : Finset V)
    (x : ProfileSpace r) (z : Fin (r v)) : ℝ :=
  kernelMarginalMass q (insert v C) (Function.update x v z) /
    kernelMarginalMass q C x

/-- The [positive table](hyp:p), [coordinate and conditioning set](hyp:v,C), [reference
profile](hyp:x), and [proposed coordinate value](hyp:z) determine [the table conditional
mass](goal) [as its kernel conditional mass](step:1). -/
def conditionalMass (p : PositiveTable r) (v : V) (C : Finset V)
    (x : ProfileSpace r) (z : Fin (r v)) : ℝ :=
  kernelConditionalMass p.mass v C x z

/-- For [a pointwise strictly positive kernel](hyp:q,hq), [a coordinate](hyp:v), [a conditioning
set](hyp:C), and [a reference profile](hyp:x), [the conditional denominator is strictly
positive](goal).
@isnad1 id=lt.1h6v.s5.2dbc85447d28 from=translated src=- shape=0e6fed97 vocab=02347857
-/
theorem kernelConditionalMass_den_pos {q : Kernel r} (hq : q.IsStrictlyPositive)
    (v : V) (C : Finset V) (x : ProfileSpace r) :
    0 < kernelMarginalMass q C x := by
  exact kernelMarginalMass_pos hq C x

/-- For [a positive table](hyp:p), [a coordinate](hyp:v), [a conditioning set](hyp:C), and [a
reference profile](hyp:x), [the conditional denominator is nonzero](goal).
@isnad1 id=ne.0h6v.s5.f08aa46c0430 from=translated src=- shape=a6305ed8 vocab=8f52eb8b
-/
theorem conditionalMass_den_ne_zero (p : PositiveTable r)
    (v : V) (C : Finset V) (x : ProfileSpace r) :
    marginalMass p C x ≠ 0 := by
  exact marginalMass_ne_zero p C x

/-- For [a pointwise strictly positive kernel](hyp:q,hq), [a coordinate and conditioning
set](hyp:v,C), [a reference profile](hyp:x), and [a proposed coordinate value](hyp:z),
[multiplying the conditional mass by its denominator recovers the joint marginal](goal).
@isnad1 id=eq.1h7v.s6.54d934652b03 from=translated src=- shape=56b0dbc3 vocab=fa4066c3
-/
theorem kernelConditionalMass_mul_den {q : Kernel r} (hq : q.IsStrictlyPositive)
    (v : V) (C : Finset V) (x : ProfileSpace r) (z : Fin (r v)) :
    kernelConditionalMass q v C x z * kernelMarginalMass q C x =
      kernelMarginalMass q (insert v C) (Function.update x v z) := by
  unfold kernelConditionalMass
  exact div_mul_cancel₀ _ (kernelMarginalMass_pos hq C x).ne'

/-- For [a positive table](hyp:p), [a coordinate and conditioning set](hyp:v,C), [a reference
profile](hyp:x), and [a proposed coordinate value](hyp:z), [multiplying the conditional mass by
the conditioning marginal recovers the joint marginal](goal).
@isnad1 id=eq.0h7v.s6.bb32de7442e9 from=translated src=- shape=67ea31bf vocab=deeb001c
-/
theorem conditionalMass_mul_marginal (p : PositiveTable r)
    (v : V) (C : Finset V) (x : ProfileSpace r) (z : Fin (r v)) :
    conditionalMass p v C x z * marginalMass p C x =
      marginalMass p (insert v C) (Function.update x v z) := by
  exact kernelConditionalMass_mul_den p.mass_pos v C x z

/-- For [a pointwise strictly positive kernel](hyp:q,hq), [a coordinate and conditioning
set](hyp:v,C), [a reference profile](hyp:x), and [a proposed coordinate value](hyp:z), [the
conditional mass is strictly positive](goal).
@isnad1 id=lt.1h7v.s5.835d9ae8dd8d from=translated src=- shape=9ba7829d vocab=39166fae
-/
theorem kernelConditionalMass_pos {q : Kernel r} (hq : q.IsStrictlyPositive)
    (v : V) (C : Finset V) (x : ProfileSpace r) (z : Fin (r v)) :
    0 < kernelConditionalMass q v C x z := by
  unfold kernelConditionalMass
  exact div_pos (kernelMarginalMass_pos hq _ _) (kernelMarginalMass_pos hq _ _)

/-- For [a positive table](hyp:p), [a coordinate and conditioning set](hyp:v,C), [a reference
profile](hyp:x), and [a proposed coordinate value](hyp:z), [the conditional mass is strictly
positive](goal).
@isnad1 id=lt.0h7v.s5.da20c2319ff8 from=translated src=- shape=4416ca1a vocab=d006e242
-/
theorem conditionalMass_pos (p : PositiveTable r)
    (v : V) (C : Finset V) (x : ProfileSpace r) (z : Fin (r v)) :
    0 < conditionalMass p v C x z := by
  exact kernelConditionalMass_pos p.mass_pos v C x z

/-- For [a pointwise strictly positive kernel](hyp:q,hq), [a coordinate outside the conditioning
set](hyp:v,C,hv), and [a reference profile](hyp:x), [the conditional row sums to one](goal).
@isnad1 id=eq.2h6v.s6.362caf7f721d from=translated src=- shape=e5778950 vocab=9bbd245e
-/
theorem sum_kernelConditionalMass {q : Kernel r} (hq : q.IsStrictlyPositive)
    (v : V) (C : Finset V) (hv : v ∉ C) (x : ProfileSpace r) :
    ∑ z : Fin (r v), kernelConditionalMass q v C x z = 1 := by
  unfold kernelConditionalMass kernelMarginalMass
  rw [← Finset.sum_div, sum_fiberSum_insert_update q hv x]
  exact div_self (kernelMarginalMass_pos hq C x).ne'

/-- For [a positive table](hyp:p), [a coordinate outside the conditioning set](hyp:v,C,hv), and
[a reference profile](hyp:x), [the conditional row sums to one](goal).
@isnad1 id=eq.1h6v.s6.6e134e87ad1e from=translated src=- shape=285d37c5 vocab=df751ead
-/
theorem sum_conditionalMass (p : PositiveTable r)
    (v : V) (C : Finset V) (hv : v ∉ C) (x : ProfileSpace r) :
    ∑ z : Fin (r v), conditionalMass p v C x z = 1 := by
  exact sum_kernelConditionalMass p.mass_pos v C hv x

end Causalean.Stat.FinitePositiveTable
