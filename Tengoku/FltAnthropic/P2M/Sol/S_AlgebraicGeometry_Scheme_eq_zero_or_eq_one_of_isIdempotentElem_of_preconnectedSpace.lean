import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_eq_zero_or_eq_one_of_isIdempotentElem_of_preconnectedSpace.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_eq_zero_or_eq_one_of_isIdempotentElem_of_preconnectedSpace

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

namespace E160GC

open TensorProduct

theorem eq_zero_or_eq_one_of_isIdempotentElem_of_isLocalRing {S : Type*} [CommRing S]
    [IsLocalRing S] (e : S) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
  · right
    have h1 : 1 - e = 0 := (hu.mul_right_eq_zero).mp h0
    exact (sub_eq_zero.mp h1).symm
  · left
    exact (hu.mul_left_eq_zero).mp h0

end E160GC

namespace E160GC

theorem germ_eq_zero_or_eq_one {X : Scheme.{u}} (e : Γ(X, ⊤)) (he : IsIdempotentElem e) (x : X) :
    X.presheaf.germ ⊤ x trivial e = 0 ∨ X.presheaf.germ ⊤ x trivial e = 1 :=
  eq_zero_or_eq_one_of_isIdempotentElem_of_isLocalRing _
    (he.map (X.presheaf.germ ⊤ x trivial).hom)

theorem mem_basicOpen_iff_germ_eq_one {X : Scheme.{u}} (e : Γ(X, ⊤)) (he : IsIdempotentElem e)
    (x : X) : x ∈ X.basicOpen e ↔ X.presheaf.germ ⊤ x trivial e = 1 := by
  rw [Scheme.mem_basicOpen_top]
  constructor
  · intro hu
    rcases germ_eq_zero_or_eq_one e he x with h | h
    · rw [h] at hu; exact absurd hu not_isUnit_zero
    · exact h
  · intro h; rw [h]; exact isUnit_one

theorem compl_basicOpen_eq_of_isIdempotentElem {X : Scheme.{u}} (e : Γ(X, ⊤))
    (he : IsIdempotentElem e) :
    (X.basicOpen e : Set X)ᶜ = (X.basicOpen (1 - e) : Set X) := by
  ext x
  have he' : IsIdempotentElem (1 - e) := he.one_sub
  simp only [Set.mem_compl_iff, SetLike.mem_coe, mem_basicOpen_iff_germ_eq_one e he,
    mem_basicOpen_iff_germ_eq_one (1 - e) he', map_sub, map_one]
  rcases germ_eq_zero_or_eq_one e he x with h | h
  · rw [h]; simp
  · rw [h]; simp

theorem isClopen_basicOpen_of_isIdempotentElem {X : Scheme.{u}} (e : Γ(X, ⊤))
    (he : IsIdempotentElem e) : IsClopen (X.basicOpen e : Set X) := by
  refine ⟨?_, (X.basicOpen e).isOpen⟩
  rw [← isOpen_compl_iff, compl_basicOpen_eq_of_isIdempotentElem e he]
  exact (X.basicOpen (1 - e)).isOpen

end E160GC

theorem solution
    (X : Scheme.{u}) [PreconnectedSpace X] (e : Γ(X, ⊤)) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  rcases isClopen_iff.mp (E160GC.isClopen_basicOpen_of_isIdempotentElem e he) with h0 | h1
  · left
    apply TopCat.Presheaf.section_ext X.sheaf ⊤ e 0
    intro x hx
    have hx' : x ∉ X.basicOpen e := by
      rw [← SetLike.mem_coe, h0]; exact fun h => h
    rcases E160GC.germ_eq_zero_or_eq_one e he x with h | h
    · rw [map_zero]; exact h
    · exact absurd ((E160GC.mem_basicOpen_iff_germ_eq_one e he x).mpr h) hx'
  · right
    apply TopCat.Presheaf.section_ext X.sheaf ⊤ e 1
    intro x hx
    have hx' : x ∈ X.basicOpen e := by
      rw [← SetLike.mem_coe, h1]; trivial
    rw [map_one]
    exact (E160GC.mem_basicOpen_iff_germ_eq_one e he x).mp hx'
