import Tengoku.Brauerinduction.BrauerInduction.Bernstein.PElementaryConstruction
import Tengoku.Brauerinduction.BrauerInduction.Cyclotomic.IntegralCharacterRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bernstein's prime-local ideal

This file defines the prime-local Bernstein span used in Steps 3--5 of the
proof.

For a fixed prime `p`, the basic generators are induced class functions

`Ind_E^G q`

where `E ≤ G` is `p`-elementary and `q ∈ Q(E)`.  We package these generators
as `JGen` and define their integral span `J p`.

The file also proves the structural properties needed later:

* generators restrict to global elements of the character system `Q`;
* `J p` absorbs multiplication by global `Q`-functions;
-/
namespace Tengoku.Brauerinduction end Tengoku.Brauerinduction open Tengoku.Brauerinduction
universe u

namespace BrauerInduction.Bernstein

variable {k G : Type u} [Field k] [Group G] [Finite G]

section IntegralIdeal

variable (p : ℕ)

/-!
## The integral span `J_p`

This section defines the common generator set `JGen` and the integral span
`J p`.  It proves the elementary closure lemmas for `J`, the projection-formula
ideal property `mul_mem_J`, and the Step 8 membership result `f_a_mem_J`.
-/

/-- The common generator set for both `J_p` and `Jloc_p`.-/
def JGen : Set (ClassFun k G) :=
  { f : ClassFun k G |
      ∃ (E : Subgroup G) (_ : IsPElementary p E)
        (q : ClassFun k E),
        q ∈ ClassFun.Q_sys k G E ∧
        f = ClassFun.ind (k := k) E q }

/-- Bernstein's integral prime-local span `J_p`.-/
def J : Submodule ℤ (ClassFun k G) := Submodule.span ℤ (JGen p)

/-- A generator of `J_p`: induction from a `p`-elementary subgroup.
@isnad1 id=mem.2h5v.s8.59ff43b21c02 from=translated src=- shape=7cc07b0d vocab=dff8c2c9
-/
lemma ind_mem_J
    (E : Subgroup G) (hE : IsPElementary p E)
    {q : ClassFun k E}
    (hq : q ∈ ClassFun.Q_sys k G E) :
    ClassFun.ind (k := k) E q ∈ J p := by
  exact Submodule.subset_span ⟨E, hE, q, hq, rfl⟩

/-- The zero function belongs to `J_p`.
@isnad1 id=mem.0h3v.s7.8533eb452714 from=translated src=- shape=bb5de77a vocab=9c556c4b
-/
lemma zero_mem_J :
    (0 : ClassFun k G) ∈ J p :=
  Submodule.zero_mem _

/-- `J_p` is closed under addition.
@isnad1 id=mem.2h5v.s8.5c3ecec52b97 from=translated src=- shape=34084741 vocab=6597c069
-/
lemma add_mem_J
    {f g : ClassFun k G} (hf : f ∈ J p) (hg : g ∈ J p) :
    f + g ∈ J p :=
  Submodule.add_mem _ hf hg

/-- `J_p` is closed under integral scalar multiplication.
@isnad1 id=mem.1h5v.s8.2347e4a990eb from=translated src=- shape=69823ef6 vocab=73827ae6
-/
lemma zsmul_mem_J
    (n : ℤ) {f : ClassFun k G} (hf : f ∈ J p) :
    n • f ∈ J p :=
  Submodule.smul_mem _ n hf

/-- The integral span `J_p` absorbs multiplication by global `Q`-functions.
@isnad1 id=mem.2h5v.s8.4e281201e4c5 from=translated src=- shape=e55a8c19 vocab=5897c6dc
-/
lemma mul_mem_J [Fact p.Prime]
    (f g : ClassFun k G)
    (hf : f ∈ J p)
    (hg : ClassFun.res (⊤ : Subgroup G) g ∈ ClassFun.Q_sys (k := k) (G := G) ⊤) :
    f * g ∈ J p := by
  refine Submodule.span_induction (p := fun f _ => f * g ∈ J p) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨E, hE, q, ⟨hq_Lambda, hq_Z⟩, rfl⟩
    obtain ⟨hg_Lambda, hg_Z⟩ := hg
    rw [mul_comm, ClassFun.projection_formula]
    apply Submodule.subset_span (R := ℤ)
    use E, hE, (ClassFun.res E g * q)
    constructor
    · constructor
      · apply ClassFun.R_Lambda.mul_mem
        · exact ClassFun.R_Lambda.res_top_to_subgroup hg_Lambda
        · exact hq_Lambda
      · apply ClassFun.C_Z.mul_mem
        · apply ClassFun.C_Z.res
          intro x
          exact hg_Z ⟨x, Subgroup.mem_top x⟩
        · exact hq_Z
    · rfl
  · simp only [zero_mul, zero_mem]
  · intro x y _ _ hx_mem hy_mem
    rw [add_mul]
    exact Submodule.add_mem _ hx_mem hy_mem
  · intro n x _ hx_mem
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ n hx_mem

section IdealPackaging

variable [Fact p.Prime]

/--
Bernstein's fixed-prime ideal in the ring of integer-valued cyclotomic
characters.

Its underlying membership condition is membership in the integral span `J p`.-/
def JIdeal :
    Ideal (ClassFun.IntegralCyclotomicCharacterRing (k := k) (G := G)) where
  carrier :=
    {f | (f : ClassFun k G) ∈ J p}
  zero_mem' := by
    change (0 : ClassFun k G) ∈ J p
    exact Submodule.zero_mem _
  add_mem' := by
    intro f g hf hg
    change
      (f : ClassFun k G) + (g : ClassFun k G) ∈ J p
    exact Submodule.add_mem _ hf hg
  smul_mem' := by
    intro q f hf
    change
      (q : ClassFun k G) * (f : ClassFun k G) ∈ J p
    simpa only [mul_comm] using
      mul_mem_J p
        (f : ClassFun k G)
        (q : ClassFun k G)
        hf
        (ClassFun.IntegralCyclotomicCharacterRing.res_top_mem_Q_sys q)

namespace JIdeal

/--
@isnad1 id=iff.0h4v.s16.3b2395c84f34 from=translated src=- shape=535d28a9 vocab=22df81d7
-/
@[simp]
lemma mem_iff
    (f : ClassFun.IntegralCyclotomicCharacterRing (k := k) (G := G)) :
    f ∈ JIdeal p ↔ (f : ClassFun k G) ∈ J p :=
  Iff.rfl

end JIdeal
end IdealPackaging

open BrauerInduction.PElementary in
/-- Bernstein Step 8: the induced function `f_a` belongs to `J_p`.
@isnad1 id=mem.1h4v.s7.055be3c90591 from=translated src=- shape=f062d267 vocab=8c55009c
-/
lemma f_a_mem_J
    [Fact p.Prime] [CharZero k] [IsAlgClosed k]
    (a : G) (ha : IsPRegular p a) :
    f (k := k) p a ∈ J p :=
      ind_mem_J p
        (E_subgroup p a) (E_isPElementary p ha) (phi_mem_Q p a ha)

end IntegralIdeal

end BrauerInduction.Bernstein
-- Tengoku: root names of this library moved to Tengoku.Brauerinduction so they do not collide with other libraries (generated)
