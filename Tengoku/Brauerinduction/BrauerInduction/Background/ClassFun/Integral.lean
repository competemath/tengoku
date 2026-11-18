import Tengoku.Brauerinduction.BrauerInduction.Background.ClassFun.Maps
import Tengoku.Brauerinduction.BrauerInduction.Background.ClassFun.Induced

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!

# Integer-valued class functions

This file contains basic API for class functions whose values are integers, and
for casting such functions to other coefficient rings.

The main constructions are:

* `ClassFun.mapIntCast`: pointwise casting of a `ℤ`-valued class function to a
  `k`-valued class function.
* `ClassFun.IsIntValued`: the predicate that a `k`-valued class function takes
  values in the image of `ℤ → k`.
* `ClassFun.C_Z`: the additive subgroup/submodule of integer-valued class
  functions.

The main closure results show that integer-valued class functions are stable
under the basic class-function operations used in Brauer induction, including
restriction and induction.
-/
namespace Tengoku.Brauerinduction end Tengoku.Brauerinduction open Tengoku.Brauerinduction
universe u v

namespace Tengoku.Brauerinduction.ClassFun

section IntegerCoefficients

variable {k : Type u} {G : Type v} [Group G] [Ring k]

/--
Cast an integer-valued class function pointwise into a class function over `k`.-/
def mapIntCast
    {k : Type u} [Ring k]
    {G : Type v} [Group G]
    (ψ : ClassFun ℤ G) :
    ClassFun k G :=
  ψ.postcomp fun z => (z : k)

/-- Evaluation of a pointwise-cast integer-valued class function.
@isnad1 id=eq.0h4v.s5.25a9dcc79ee0 from=translated src=- shape=8ebfdc17 vocab=5a153795
-/
@[simp]
lemma mapIntCast_apply
    {H : Type v} [Group H]
    (ψ : ClassFun ℤ H) (h : H) :
    mapIntCast (k := k) ψ h = (ψ h : k) :=
  rfl

/--
Pointwise casting of integer-valued class functions commutes with integer
scalar multiplication.
@isnad1 id=eq.0h4v.s6.04131f4e4d47 from=translated src=- shape=fae4fbaa vocab=955599c6
-/
lemma intCast_zsmul
    {H : Type v} [Group H]
    (n : ℤ) (ψ : ClassFun ℤ H) :
    (n : k) • mapIntCast (k := k) ψ =
      mapIntCast (k := k) (n • ψ) := by
  ext h
  simp only [smul_apply, mapIntCast_apply, smul_eq_mul, zsmul_eq_mul, mul_apply,
    intCast_apply, Int.cast_eq, Int.cast_mul]

/--
A class function is integer-valued if each of its values is the image of an
integer.-/
def IsIntValued (f : ClassFun k G) : Prop :=
  ∀ g : G, ∃ n : ℤ, f g = (n : k)

/--
Induction commutes with pointwise casting of integer-valued class functions.
@isnad1 id=eq.0h4v.s6.5305e0956ae5 from=translated src=- shape=546eb2f6 vocab=b1c62e60
-/
@[simp]
lemma ind_mapIntCast
    (H : Subgroup G) [Finite G]
    (ψ : ClassFun ℤ H) :
    ind H (mapIntCast (k := k) ψ) =
      mapIntCast (k := k) (ind H ψ) := by
  simpa [mapIntCast] using
    (ind_postcomp
      (G := G)
      (F := (Int.castRingHom k).toAddMonoidHom)
      (H := H)
      (φ := ψ))

end IntegerCoefficients

section C_Z

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]

/--
`C_Z(H)`: the set of integer-valued class functions on `H`.-/
abbrev C_Z (k : Type u) [CommRing k]
    (G : Type v) [Group G] : Set (ClassFun k G) :=
  { f | ClassFun.IsIntValued f }

/--
@isnad1 id=iff.0h3v.s5.dfdc42858ac4 from=translated src=- shape=f165b349 vocab=10fa2ebf
-/
@[simp]
lemma mem_C_Z {f : ClassFun k G} :
    f ∈ C_Z k G ↔ ClassFun.IsIntValued f :=
  Iff.rfl

namespace C_Z

/--
@isnad1 id=mem.0h2v.s5.1a4bb08715a7 from=translated src=- shape=ee74871d vocab=cd160374
-/
lemma zero_mem :
    (0 : ClassFun k G) ∈ C_Z k G := by
  intro g
  refine ⟨0, ?_⟩
  simp

/--
@isnad1 id=mem.0h2v.s5.4198c045e17c from=translated src=- shape=ee74871d vocab=cd160374
-/
lemma one_mem :
    (1 : ClassFun k G) ∈ C_Z k G := by
  intro g
  refine ⟨1, ?_⟩
  simp

/--
@isnad1 id=mem.2h4v.s6.627c6b4f67f2 from=translated src=- shape=00fe3b30 vocab=628a56e9
-/
lemma add_mem {f g : ClassFun k G}
    (hf : f ∈ C_Z k G) (hg : g ∈ C_Z k G) :
    f + g ∈ C_Z k G := by
  intro x
  rcases hf x with ⟨m, hm⟩
  rcases hg x with ⟨n, hn⟩
  refine ⟨m + n, ?_⟩
  simp [ClassFun.add_apply, hm, hn]

/--
@isnad1 id=mem.1h3v.s6.215280c708a3 from=translated src=- shape=fa4b5858 vocab=1b126001
-/
lemma neg_mem {f : ClassFun k G}
    (hf : f ∈ C_Z k G) :
    -f ∈ C_Z k G := by
  intro x
  rcases hf x with ⟨m, hm⟩
  refine ⟨-m, ?_⟩
  simp [hm]

/--
@isnad1 id=mem.2h4v.s6.04c1a2e37143 from=translated src=- shape=00fe3b30 vocab=4db2adee
-/
lemma sub_mem {f g : ClassFun k G}
    (hf : f ∈ C_Z k G) (hg : g ∈ C_Z k G) :
    f - g ∈ C_Z k G := by
  simpa [sub_eq_add_neg] using add_mem hf (neg_mem hg)

/--
@isnad1 id=mem.1h4v.s6.9bfce3b3c2aa from=translated src=- shape=4e6d7de0 vocab=f5005062
-/
lemma zsmul_mem (n : ℤ) {f : ClassFun k G}
    (hf : f ∈ C_Z k G) :
    n • f ∈ C_Z k G := by
  intro x
  rcases hf x with ⟨m, hm⟩
  refine ⟨n * m, ?_⟩
  simp [hm]

/--
@isnad1 id=mem.2h4v.s6.349386c12334 from=translated src=- shape=00fe3b30 vocab=1bf56436
-/
lemma mul_mem {f g : ClassFun k G}
    (hf : f ∈ C_Z k G) (hg : g ∈ C_Z k G) :
    f * g ∈ C_Z k G := by
  intro x
  rcases hf x with ⟨m, hm⟩
  rcases hg x with ⟨n, hn⟩
  refine ⟨m * n, ?_⟩
  simp [ClassFun.mul_apply, hm, hn]

/--
@isnad1 id=mem.1h4v.s6.1f2c6556451a from=translated src=- shape=b40cd6f9 vocab=fdf5c131
-/
lemma pow_mem {f : ClassFun k G}
    (hf : f ∈ ClassFun.C_Z k G) :
    ∀ n : ℕ, f ^ n ∈ ClassFun.C_Z k G := by
  intro n
  induction n with
  | zero => simp only [pow_zero, Set.mem_ofPred_eq]; apply one_mem
  | succ n ih => simpa [pow_succ] using mul_mem ih hf

/-- Integer-valued class functions remain integer-valued after restriction.
@isnad1 id=mem.1h4v.s7.406c824c51c5 from=translated src=- shape=3faeca3e vocab=18288e71
-/
lemma res
    {G : Type v} [Group G]
    {H : Subgroup G} {g : ClassFun k G}
    (hg : g ∈ C_Z k G) :
    ClassFun.res H g ∈ C_Z k H := by
  intro h
  exact hg h

/--
A finite sum of elements lying in the image of `ℤ` again lies in the image of
`ℤ`.-/
private lemma exists_int_cast_sum
    {k : Type u} [AddCommGroupWithOne k]
    {ι : Type*} (s : Finset ι) (f : ι → k)
    (hf : ∀ i, i ∈ s → ∃ z : ℤ, f i = (z : k)) :
    ∃ z : ℤ, s.sum f = (z : k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, by simp⟩
  | insert a s ha ih =>
      rcases hf a (by simp [ha]) with ⟨za, hza⟩
      rcases ih (by
        intro i hi
        exact hf i (by simp [hi])) with ⟨zs, hzs⟩
      refine ⟨za + zs, ?_⟩
      simp only [ha, not_false_eq_true, Finset.sum_insert, hza, hzs, Int.cast_add]

/--
Induction preserves integer-valued class functions.

The result is stated after restricting the induced class function to `⊤`, so
that it is an element of `C_Z k (⊤ : Subgroup G)`.
@isnad1 id=mem.1h4v.s8.f2a94289bc5c from=translated src=- shape=9d7097ff vocab=6c13d737
-/
lemma ind_mem_C_Z
    {G : Type v} [Group G] [Finite G]
    {H : Subgroup G} {q : ClassFun k H}
    (hq : q ∈ C_Z k H) :
    ClassFun.res (⊤ : Subgroup G)
      (ClassFun.ind H q) ∈ C_Z k (⊤ : Subgroup G) := by
  classical
  intro g_top

  let g : G := g_top

  change ∃ z : ℤ,
    ClassFun.ind (G := G) (k := k) H q g = (z : k)

  simp only [ClassFun.ind_apply]
  letI: Fintype G := Fintype.ofFinite G
  refine exists_int_cast_sum
    (s := Finset.univ)
    (f := fun x : G ⧸ H =>
      if hx : (Quotient.out x)⁻¹ * g * Quotient.out x ∈ H
      then q ⟨(Quotient.out x)⁻¹ * g * Quotient.out x, hx⟩
      else 0)
    ?_

  intro x hx
  by_cases hmem : (Quotient.out x)⁻¹ * g * Quotient.out x ∈ H
  · rcases hq ⟨(Quotient.out x)⁻¹ * g * Quotient.out x, hmem⟩ with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    simp [hmem, hz]
  · refine ⟨0, ?_⟩
    simp [hmem]

/-- Induction preserves integer-valued class functions.
@isnad1 id=mem.1h4v.s7.1e245540262b from=translated src=- shape=5f72829e vocab=c656b8df
-/
lemma ind_mem
    {G : Type v} [Group G] [Finite G]
    {H : Subgroup G} {q : ClassFun k H}
    (hq : q ∈ C_Z k H) :
    ClassFun.ind H q ∈ C_Z k G := by
  intro g
  simpa only [ClassFun.res_apply] using
    ind_mem_C_Z hq ⟨g, Subgroup.mem_top g⟩

end C_Z
end C_Z

end Tengoku.Brauerinduction.ClassFun
-- Tengoku: root names of this library moved to Tengoku.Brauerinduction so they do not collide with other libraries (generated)
