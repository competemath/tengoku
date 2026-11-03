import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Combinatorics.PosetSpaceUpperSetHeight

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The upper-set cube above a finite antichain -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.AntichainUpperCube
universe u
variable {T : Type u} [PartialOrder T] [Fintype T] [DecidableEq T]

/-- Elements strictly above at least one member of the antichain.-/
def base (A : Finset T) : Finset T := by
  classical
  exact Finset.univ.filter (fun t ↦ ∃ a ∈ A, a < t)

/--
@isnad1 id=iff.0h3v.s5.d6c45ae17f33 from=translated src=- shape=dc0f56bc vocab=ef58625a
-/
@[simp]
theorem mem_base (A : Finset T) (t : T) : t ∈ base A ↔ ∃ a ∈ A, a < t := by
  classical
  simp [base]

/-- The strict upper part is an upper set.
@isnad1 id=isuppers.0h2v.s5.32297fb6ba50 from=translated src=- shape=6f2d25c0 vocab=878e0b26
-/
theorem base_isUpperSet (A : Finset T) : IsUpperSet (base A : Set T) := by
  intro x y hxy hx
  obtain ⟨a, ha, hax⟩ := (mem_base A x).1 hx
  exact (mem_base A y).2 ⟨a, ha, hax.trans_le hxy⟩

/-- The strict upper part contains no member of the antichain.
@isnad1 id=disjoint.1h2v.s6.b6eda9d4510b from=translated src=- shape=60692939 vocab=198ceaf2
-/
theorem base_disjoint (A : Finset T)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a ≤ b → a = b) : Disjoint (base A) A := by
  classical
  apply Finset.disjoint_left.mpr
  intro b hb hbA
  obtain ⟨a, ha, hab⟩ := (mem_base A b).1 hb
  exact hab.ne (hA a ha b hbA hab.le)

/-- Adjoining any subset of the antichain to the strict upper part gives
an upper set.
@isnad1 id=isuppers.1h3v.s5.4e306f798816 from=translated src=- shape=06cfb686 vocab=d2634f02
-/
theorem union_isUpperSet (A B : Finset T) (hB : B ⊆ A) :
    IsUpperSet ((base A ∪ B : Finset T) : Set T) := by
  classical
  intro x y hxy hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Finset.mem_union_left _ (base_isUpperSet A hxy hx)
  · by_cases heq : x = y
    · subst y
      exact Finset.mem_union_right _ hx
    · exact Finset.mem_union_left _ ((mem_base A y).2 ⟨x, hB hx, lt_of_le_of_ne hxy heq⟩)

/-- The cube vertex indexed by B has exactly |B| more elements than its base.
@isnad1 id=eq.2h3v.s6.80f8f6988424 from=translated src=- shape=5e74c3ce vocab=17376a41
-/
theorem card_union (A B : Finset T)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a ≤ b → a = b) (hB : B ⊆ A) :
    (base A ∪ B).card = (base A).card + B.card := by
  classical
  exact Finset.card_union_of_disjoint ((base_disjoint A hA).mono_right hB)

/-- Different subsets of the antichain give different cube vertices.
@isnad1 id=eq.4h4v.s6.bb24438184e7 from=translated src=- shape=644a2b74 vocab=a3d22068
-/
theorem union_injective (A : Finset T)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a ≤ b → a = b)
    {B C : Finset T} (hB : B ⊆ A) (hC : C ⊆ A)
    (heq : base A ∪ B = base A ∪ C) : B = C := by
  classical
  have hb := (base_disjoint A hA).mono_right hB
  have hc := (base_disjoint A hA).mono_right hC
  have h := congrArg (fun U : Finset T ↦ U \ base A) heq
  simpa [Finset.union_sdiff_left, Finset.sdiff_eq_self_iff_disjoint.mpr hb.symm,
    Finset.sdiff_eq_self_iff_disjoint.mpr hc.symm] using h

end MagnitudeConjecture.AntichainUpperCube
