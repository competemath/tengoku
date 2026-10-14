/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku

/-!
# IMO 2012 A5 (Definitions)

Let $R$ be a ring and $S$ be a domain.
Find all functions $f : R → S$ such that, for any $x, y ∈ R$,
$$ f(xy + 1) = f(x) f(y) + f(x + y). $$

This file defines the functional equation and prove some basic properties.
We also define some notions; we say that $f$ is
* `good` if it satisfies the above functional equation;
* `NontrivialGood` if $f$ is good and $f(0) = -1$;
* `ReducedGood` if $f$ is non-trivial good and there is no non-zero $f$-periodic element.

The `NontrivialGood` functions are defined in the folder `A5Answers`.
They file `IMOSLLean4/IMO2012/A5/A5Answers/Common.lean` collects all these functions.
The file `IMOSLLean4/IMO2012/A5/A5.lean` proves that these are
  precisely the good functions, up to ring homomorphism.
-/

@[expose] public section

namespace IMOSL
namespace IMO2012A5
namespace Generalization

variable [NonAssocSemiring R] [Add S] [Mul S]

/-- The main problem. -/
def good (f : R → S) := ∀ x y : R, f (x * y + 1) = f x * f y + f (x + y)

/--
@isnad1 id=eq.2h5v.s6.8fe150cbe978 from=translated src=- shape=98b9fe6f vocab=fde18a20
-/
theorem map_commute_of_commute [IsCancelAdd S]
    {f : R → S} (h : good f) (h0 : x * y = y * x) : f x * f y = f y * f x :=
  add_right_cancel (b := f (x + y)) (by rw [← h, h0, h, add_comm x])

variable [One S] [Zero S]

structure NontrivialGood (f : R → S) : Prop where
  is_good : good f
  map_zero_add_one : f 0 + 1 = 0

/--
@isnad1 id=eq.1h3v.s6.8ff5cef4ab55 from=translated src=- shape=7fe62e02 vocab=838853a0
-/
lemma NontrivialGood.map_zero {S} [AddGroupWithOne S] [Mul S]
    {f : R → S} (hf : NontrivialGood f) : f 0 = -1 :=
  eq_neg_of_add_eq_zero_left hf.map_zero_add_one

/--
@isnad1 id=eq.1h3v.s6.b2a7e528b6e4 from=translated src=- shape=2721a8fd vocab=57808706
-/
lemma NontrivialGood.map_one {S} [NonAssocSemiring S]
    {f : R → S} (hf : NontrivialGood f) : f 1 = 0 := by
  rw [← zero_add 1, ← zero_mul 0, hf.is_good, zero_add,
    ← add_one_mul (f 0), hf.map_zero_add_one, zero_mul]

structure ReducedGood (f : R → S) extends NontrivialGood f where
  period_imp_eq (c d) (_ : ∀ x, f (x + c) = f (x + d)) : c = d

/--
@isnad1 id=eq.2h4v.s6.86116712e0e7 from=translated src=- shape=1f04a0ec vocab=373bc658
-/
lemma ReducedGood.period_imp_zero {f : R → S} (hf : ReducedGood f)
    (h : ∀ x, f (x + c) = f x) : c = 0 :=
  hf.period_imp_eq c 0 λ x ↦ by rw [h, add_zero]
