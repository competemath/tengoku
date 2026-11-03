/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Abelian.Stability.Uniqueness.Extrema

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The maximally destabilizing subobject and the extremal phase functions

This file owns the public interface built on the uniqueness argument: the
canonical maximally destabilizing subobject of a nonzero object, its
destabilizing quotient and the short exact sequence they form, and the extremal
phase functions `phiPlus` and `phiMinus` with the characterisation of
semistability as their equality.

This is the module a consumer of the uniqueness milestone should import.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace StabilityFunction

/-- The canonical maximally destabilizing subobject of a nonzero object.-/
noncomputable def maxDestabilizingSubobject (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) : Subobject E :=
  let F := Classical.choice (hHN E hE)
  F.chain ⟨1, by have := F.nonempty; lia⟩

/-- The canonical maximally destabilizing subobject agrees with the first
nonzero term of every owner HN filtration.
@isnad1 id=eq.2h4v.s6.45523818d705 from=translated src=- shape=c36f4d0c vocab=3c367bf0
-/
theorem maxDestabilizingSubobject_eq_filtration (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) {E : A} (hE : ¬IsZero E)
    (F : AbelianHNFiltration Z E) :
    Z.maxDestabilizingSubobject hHN E hE =
      F.chain ⟨1, by have := F.nonempty; lia⟩ :=
  (Classical.choice (hHN E hE)).chain_one_eq F

/-- The canonical maximally destabilizing subobject is nonzero.
@isnad1 id=ne.2h3v.s6.2cc7b64123d4 from=translated src=- shape=dbf55054 vocab=72eb0025
-/
theorem maxDestabilizingSubobject_ne_bot (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) :
    Z.maxDestabilizingSubobject hHN E hE ≠ ⊥ :=
  (Classical.choice (hHN E hE)).chain_one_ne_bot

/-- The canonical maximally destabilizing subobject is semistable.
@isnad1 id=issemist.2h3v.s6.14bb71a75014 from=translated src=- shape=6a9cbf8a vocab=390cd059
-/
theorem maxDestabilizingSubobject_isSemistable (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) :
    Z.IsSemistable (Z.maxDestabilizingSubobject hHN E hE : A) :=
  (Classical.choice (hHN E hE)).chain_one_isSemistable

/-- A nonzero object is semistable exactly when its canonical maximally
destabilizing subobject is the whole object.
@isnad1 id=iff.2h3v.s6.23bcbeadd18f from=translated src=- shape=0ea0afee vocab=0e5dbb57
-/
theorem maxDestabilizingSubobject_eq_top_iff_isSemistable
    (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    (E : A) (hE : ¬IsZero E) :
    Z.maxDestabilizingSubobject hHN E hE = ⊤ ↔ Z.IsSemistable E := by
  let F := Classical.choice (hHN E hE)
  rw [Z.maxDestabilizingSubobject_eq_filtration hHN hE F]
  constructor
  · intro htop
    have htopsemistable : Z.IsSemistable ((⊤ : Subobject E) : A) :=
      htop ▸ F.chain_one_isSemistable
    exact Z.isSemistable_of_iso (asIso (⊤ : Subobject E).arrow)
      htopsemistable
  · intro hEsemistable
    have hn : F.n = 1 := F.n_eq_one_of_semistable hEsemistable
    have hindex : (⟨1, by have := F.nonempty; lia⟩ : Fin (F.n + 1)) =
        ⟨F.n, by lia⟩ := Fin.ext (by lia)
    rw [hindex, F.chain_top]

/-- The quotient left after removing the canonical maximally destabilizing
subobject.-/
noncomputable def destabilizingQuotient (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) : A :=
  cokernel (Z.maxDestabilizingSubobject hHN E hE).arrow

/-- The destabilizing quotient is zero exactly for semistable objects.
@isnad1 id=iff.2h3v.s5.6b9a2708b62d from=translated src=- shape=b5abb6e7 vocab=b2b60750
-/
theorem isZero_destabilizingQuotient_iff_isSemistable
    (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    (E : A) (hE : ¬IsZero E) :
    IsZero (Z.destabilizingQuotient hHN E hE) ↔ Z.IsSemistable E := by
  rw [← Z.maxDestabilizingSubobject_eq_top_iff_isSemistable hHN E hE]
  constructor
  · intro hquotient
    haveI : Epi (Z.maxDestabilizingSubobject hHN E hE).arrow :=
      Preadditive.epi_of_isZero_cokernel _ hquotient
    haveI : IsIso (Z.maxDestabilizingSubobject hHN E hE).arrow :=
      isIso_of_mono_of_epi _
    exact Subobject.eq_top_of_isIso_arrow _
  · intro htop
    change IsZero (cokernel (Z.maxDestabilizingSubobject hHN E hE).arrow)
    rw [htop]
    exact isZero_cokernel_of_epi (⊤ : Subobject E).arrow

/-- A non-semistable object has a nonzero destabilizing quotient.
@isnad1 id=not.3h3v.s5.4ac5cd771870 from=translated src=- shape=3f9bc974 vocab=b2b60750
-/
theorem destabilizingQuotient_not_isZero_of_not_isSemistable
    (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    (E : A) (hE : ¬IsZero E) (hnot : ¬Z.IsSemistable E) :
    ¬IsZero (Z.destabilizingQuotient hHN E hE) :=
  fun hzero => hnot ((Z.isZero_destabilizingQuotient_iff_isSemistable
    hHN E hE).1 hzero)

/-- The canonical short complex presenting an object as an extension of its
maximally destabilizing subobject by the destabilizing quotient.-/
noncomputable def destabilizingShortComplex (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) : ShortComplex A :=
  ShortComplex.mk (Z.maxDestabilizingSubobject hHN E hE).arrow
    (cokernel.π (Z.maxDestabilizingSubobject hHN E hE).arrow)
    (cokernel.condition (Z.maxDestabilizingSubobject hHN E hE).arrow)

/-- The canonical destabilizing short complex is short exact.
@isnad1 id=shortexa.2h3v.s5.f203f3cde47d from=translated src=- shape=6fcf6ecb vocab=25a7dbeb
-/
theorem destabilizingShortComplex_shortExact (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) :
    (Z.destabilizingShortComplex hHN E hE).ShortExact := by
  change (ShortComplex.mk _ _ _).ShortExact
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_cokernel
      (Z.maxDestabilizingSubobject hHN E hE).arrow)
    inferInstance inferInstance

/-- The central charge splits across the canonical destabilizing short exact
sequence.
@isnad1 id=eq.2h3v.s6.5ad92845e109 from=translated src=- shape=1f5c7253 vocab=5512a1e1
-/
theorem charge_eq_maxDestabilizingSubobject_add_destabilizingQuotient
    (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    (E : A) (hE : ¬IsZero E) :
    Z.charge E = Z.charge (Z.maxDestabilizingSubobject hHN E hE : A) +
      Z.charge (Z.destabilizingQuotient hHN E hE) :=
  Z.additive (Z.destabilizingShortComplex hHN E hE)
    (Z.destabilizingShortComplex_shortExact hHN E hE)

/-- The intrinsic highest HN phase of a nonzero object.-/
noncomputable def phiPlus (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    (E : A) (hE : ¬IsZero E) : ℝ :=
  (Classical.choice (hHN E hE)).phiPlus

/-- The intrinsic lowest HN phase of a nonzero object.-/
noncomputable def phiMinus (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    (E : A) (hE : ¬IsZero E) : ℝ :=
  (Classical.choice (hHN E hE)).phiMinus

/-- The intrinsic highest phase agrees with every owner HN filtration.
@isnad1 id=eq.2h4v.s5.5eb9f0bc4771 from=translated src=- shape=a6db3ef0 vocab=734221c8
-/
theorem phiPlus_eq_filtration (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    {E : A} (hE : ¬IsZero E) (F : AbelianHNFiltration Z E) :
    Z.phiPlus hHN E hE = F.phiPlus :=
  (Classical.choice (hHN E hE)).phiPlus_eq F

/-- The canonical maximally destabilizing subobject has the intrinsic highest
HN phase.
@isnad1 id=eq.2h3v.s6.9f0b259fde23 from=translated src=- shape=ad27578a vocab=82c9392e
-/
theorem phase_maxDestabilizingSubobject (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) :
    Z.phase (Z.maxDestabilizingSubobject hHN E hE : A) =
      Z.phiPlus hHN E hE :=
  (Classical.choice (hHN E hE)).phase_chain_one

/-- Every semistable subobject at the intrinsic highest HN phase lies in the
canonical maximally destabilizing subobject.
@isnad1 id=le.4h4v.s7.e00a041a9594 from=translated src=- shape=b1aa80ad vocab=f46ae648
-/
theorem le_maxDestabilizingSubobject_of_semistable_phase_eq_phiPlus
    (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    {E : A} (hE : ¬IsZero E) {B : Subobject E}
    (hB : Z.IsSemistable (B : A))
    (hphase : Z.phase (B : A) = Z.phiPlus hHN E hE) :
    B ≤ Z.maxDestabilizingSubobject hHN E hE := by
  let F := Classical.choice (hHN E hE)
  rw [Z.phiPlus_eq_filtration hHN hE F] at hphase
  rw [Z.maxDestabilizingSubobject_eq_filtration hHN hE F]
  exact F.le_chain_one_of_semistable_phase_eq_phiPlus hB hphase

/-- The intrinsic lowest phase agrees with every owner HN filtration.
@isnad1 id=eq.2h4v.s5.3c9f7a6d1e9a from=translated src=- shape=a6db3ef0 vocab=d0e48ecd
-/
theorem phiMinus_eq_filtration (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    {E : A} (hE : ¬IsZero E) (F : AbelianHNFiltration Z E) :
    Z.phiMinus hHN E hE = F.phiMinus :=
  (Classical.choice (hHN E hE)).phiMinus_eq F

/-- The intrinsic lowest HN phase is at most the intrinsic highest phase.
@isnad1 id=le.2h3v.s5.27ece66b062d from=translated src=- shape=4e0eee53 vocab=1fd35263
-/
theorem phiMinus_le_phiPlus (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    (E : A) (hE : ¬IsZero E) :
    Z.phiMinus hHN E hE ≤ Z.phiPlus hHN E hE := by
  let F := Classical.choice (hHN E hE)
  rw [Z.phiMinus_eq_filtration hHN hE F,
    Z.phiPlus_eq_filtration hHN hE F]
  exact F.phiMinus_le_phiPlus

/-- A nonzero object is semistable exactly when its intrinsic HN phase
interval degenerates to a point.
@isnad1 id=iff.2h3v.s5.91f010c232c6 from=translated src=- shape=9825df83 vocab=b268c8f4
-/
theorem isSemistable_iff_phiPlus_eq_phiMinus (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) :
    Z.IsSemistable E ↔ Z.phiPlus hHN E hE = Z.phiMinus hHN E hE := by
  let F := Classical.choice (hHN E hE)
  rw [Z.phiPlus_eq_filtration hHN hE F,
    Z.phiMinus_eq_filtration hHN hE F]
  constructor
  · intro hsemistable
    have hn : F.n = 1 := F.n_eq_one_of_semistable hsemistable
    apply congrArg F.phase
    apply Fin.ext
    lia
  · intro hextrema
    apply F.isSemistable_of_n_eq_one
    by_contra hn
    have hn_gt : 1 < F.n := by
      have := F.nonempty
      lia
    have hlast_lt : F.phiMinus < F.phiPlus := by
      exact F.phase_strictAnti (Fin.mk_lt_mk.mpr (by lia))
    exact (ne_of_lt hlast_lt) hextrema.symm

end StabilityFunction

end CategoryTheory.Triangulated
