import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

universe u

namespace AffineDilatation

variable {A : Type u} [CommRing A]

def gen (I : Ideal A) (a : A) : Set (Localization.Away a) :=
  (fun g : A => IsLocalization.mk' (Localization.Away a) g
    (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)) '' (I : Set A)

def subalgebra (I : Ideal A) (a : A) : Subalgebra A (Localization.Away a) :=
  Algebra.adjoin A (gen I a)

abbrev Ring (I : Ideal A) (a : A) : Type u :=
  ↥(subalgebra I a)

def divElem (I : Ideal A) (a : A) (g : A) (hg : g ∈ I) : Ring I a :=
  ⟨IsLocalization.mk' (Localization.Away a) g (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a),
    Algebra.subset_adjoin ⟨g, hg, rfl⟩⟩

/--
@isnad1 id=eq.1h4v.s8.b3140dc00125 from=translated src=- shape=126123c5 vocab=2066201e
-/
@[simp]
theorem coe_divElem (I : Ideal A) (a : A) (g : A) (hg : g ∈ I) :
    ((divElem I a g hg : Ring I a) : Localization.Away a) =
      IsLocalization.mk' (Localization.Away a) g
        (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a) :=
  rfl

/--
@isnad1 id=eq.0h4v.s9.b14d39952467 from=translated src=- shape=d97067e7 vocab=0d56d46e
-/
theorem coe_algebraMap (I : Ideal A) (a : A) (g : A) :
    ((algebraMap A (Ring I a) g : Ring I a) : Localization.Away a) =
      algebraMap A (Localization.Away a) g :=
  rfl

/--
@isnad1 id=eq.1h4v.s9.5fd02151b8b1 from=translated src=- shape=8b9f73cd vocab=e2ab0b08
-/
theorem algebraMap_mul_divElem (I : Ideal A) (a : A) (g : A) (hg : g ∈ I) :
    algebraMap A (Ring I a) a * divElem I a g hg = algebraMap A (Ring I a) g := by
  apply Subtype.ext
  change algebraMap A (Localization.Away a) a *
      IsLocalization.mk' (Localization.Away a) g
        (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a) =
    algebraMap A (Localization.Away a) g
  rw [mul_comm]
  exact IsLocalization.mk'_spec (Localization.Away a) g
    (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)

/--
@isnad1 id=iff.0h4v.s7.63b64e17fee9 from=translated src=- shape=97763c1c vocab=f2b70ebf
-/
theorem mem_gen_iff (I : Ideal A) (a : A) (x : Localization.Away a) :
    x ∈ gen I a ↔ ∃ g ∈ I, IsLocalization.mk' (Localization.Away a) g
      (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a) = x :=
  Iff.rfl

/--
@isnad1 id=eq.0h3v.s7.e3bc8e354864 from=translated src=- shape=052cead0 vocab=0b07de3f
-/
theorem subalgebra_eq_adjoin (I : Ideal A) (a : A) :
    subalgebra I a = Algebra.adjoin A (gen I a) :=
  rfl

/--
@isnad1 id=le.0h3v.s7.01d5aaefbed9 from=translated src=- shape=aa0b5e51 vocab=e440222e
-/
theorem gen_subset (I : Ideal A) (a : A) :
    gen I a ⊆ (subalgebra I a : Set (Localization.Away a)) :=
  Algebra.subset_adjoin

/--
@isnad1 id=mem.1h4v.s8.b79faaee4f99 from=translated src=- shape=35f9a706 vocab=c9c3b2a6
-/
theorem divElem_mem (I : Ideal A) (a : A) (g : A) (hg : g ∈ I) :
    ((divElem I a g hg : Ring I a) : Localization.Away a) ∈ gen I a :=
  ⟨g, hg, rfl⟩

end AffineDilatation

end
