/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/
module

public import Tengoku.LeanPool.LeanPool.LocalComplexGeometry.Germs.Basic
public import Tengoku

/-!
# Local zero-set germs and vanishing ideals

Zero sets are predicate-valued germs.  This avoids evaluating an abstract
function germ at points away from the base point.  Only finite intersections
are used; arbitrary intersections would not have a uniform neighborhood.
-/

@[expose] public section

open Filter
open scoped Topology

namespace LocalComplexGeometry

noncomputable section

/-- Germs at the origin of predicates on `ℂⁿ`. -/
abbrev LocalSetGerm (n : ℕ) :=
  Filter.Germ (𝓝 (0 : ComplexEuclidean n)) Prop

/-- The local zero set of a holomorphic function germ. -/
def germZeroLocus {n : ℕ} (f : HolomorphicGerm n) : LocalSetGerm n :=
  Filter.Germ.map (fun z : ℂ ↦ z = 0) (f : FunctionGerm n)

/--
@isnad1 id=eq.0h1v.s9.dbfc18166118 from=translated src=- shape=cc722af0 vocab=aecd13f8
-/
@[simp]
theorem germZeroLocus_zero (n : ℕ) :
    germZeroLocus (0 : HolomorphicGerm n) = ⊤ := by
  change
    ((fun _ : ComplexEuclidean n ↦ (0 : ℂ) = 0) : LocalSetGerm n) =
      ((fun _ : ComplexEuclidean n ↦ True) : LocalSetGerm n)
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun _ ↦ propext (by simp)

/-- A common zero of `f` and `g` is a zero of their sum.
@isnad1 id=le.0h3v.s10.c7c32aec9ca7 from=translated src=- shape=76e0a1e1 vocab=fcc7926d
-/
theorem germZeroLocus_inf_le_add {n : ℕ} (f g : HolomorphicGerm n) :
    germZeroLocus f ⊓ germZeroLocus g ≤ germZeroLocus (f + g) := by
  change
    Filter.Germ.map (fun z : ℂ ↦ z = 0) (f : FunctionGerm n) ⊓
        Filter.Germ.map (fun z : ℂ ↦ z = 0) (g : FunctionGerm n) ≤
      Filter.Germ.map (fun z : ℂ ↦ z = 0)
        ((f : FunctionGerm n) + (g : FunctionGerm n))
  refine Filter.Germ.inductionOn₂ (f : FunctionGerm n) (g : FunctionGerm n) ?_
  intro F G
  change
    ((fun x ↦ F x = 0 ∧ G x = 0) : LocalSetGerm n) ≤
      ((fun x ↦ F x + G x = 0) : LocalSetGerm n)
  rw [Filter.Germ.coe_le]
  exact Filter.Eventually.of_forall fun _ h ↦ by simp [h.1, h.2]

/-- Every zero of `f` is a zero of a left multiple of `f`.
@isnad1 id=le.0h3v.s10.a747d1bde78c from=translated src=- shape=ef48cab9 vocab=92889660
-/
theorem germZeroLocus_le_mul {n : ℕ} (a f : HolomorphicGerm n) :
    germZeroLocus f ≤ germZeroLocus (a * f) := by
  change
    Filter.Germ.map (fun z : ℂ ↦ z = 0) (f : FunctionGerm n) ≤
      Filter.Germ.map (fun z : ℂ ↦ z = 0)
        ((a : FunctionGerm n) * (f : FunctionGerm n))
  refine Filter.Germ.inductionOn₂ (a : FunctionGerm n) (f : FunctionGerm n) ?_
  intro A F
  change
    ((fun x ↦ F x = 0) : LocalSetGerm n) ≤
      ((fun x ↦ A x * F x = 0) : LocalSetGerm n)
  rw [Filter.Germ.coe_le]
  exact Filter.Eventually.of_forall fun _ h ↦ by simp [h]

/-- A positive power has exactly the same local zero-set germ.
@isnad1 id=eq.1h3v.s9.f0ac16f81d68 from=translated src=- shape=c3542865 vocab=3eefd4f1
-/
theorem germZeroLocus_pow {n : ℕ} (f : HolomorphicGerm n)
    {k : ℕ} (hk : 0 < k) :
    germZeroLocus (f ^ k) = germZeroLocus f := by
  change
    Filter.Germ.map (fun z : ℂ ↦ z = 0)
        ((f : FunctionGerm n) ^ k) =
      Filter.Germ.map (fun z : ℂ ↦ z = 0) (f : FunctionGerm n)
  refine Filter.Germ.inductionOn (f : FunctionGerm n) ?_
  intro F
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun x ↦ propext (by
    simpa [Function.comp_apply] using
      (pow_eq_zero_iff hk.ne' : F x ^ k = 0 ↔ F x = 0))

/-- A holomorphic germ vanishes on a full neighborhood exactly when it is the
zero germ.
@isnad1 id=iff.0h2v.s9.86acaa91cf98 from=translated src=- shape=1fa5999e vocab=aecd13f8
-/
theorem germZeroLocus_eq_top_iff {n : ℕ} (f : HolomorphicGerm n) :
    germZeroLocus f = ⊤ ↔ f = 0 := by
  constructor
  · intro h
    obtain ⟨F, hF, hrep⟩ := HolomorphicGerm.exists_rep f
    have hz : (⊤ : LocalSetGerm n) ≤ germZeroLocus f := h.symm.le
    change
      ((fun _ : ComplexEuclidean n ↦ True) : LocalSetGerm n) ≤
        Filter.Germ.map (fun z : ℂ ↦ z = 0) (f : FunctionGerm n) at hz
    rw [← hrep] at hz
    change
      ((fun _ : ComplexEuclidean n ↦ True) : LocalSetGerm n) ≤
        ((fun x ↦ F x = 0) : LocalSetGerm n) at hz
    rw [Filter.Germ.coe_le] at hz
    apply Subtype.ext
    change (f : FunctionGerm n) = 0
    rw [← hrep, ← Filter.Germ.coe_zero]
    apply Filter.Germ.coe_eq.mpr
    exact hz.mono fun x hx ↦ hx True.intro
  · rintro rfl
    exact germZeroLocus_zero n

/-- Holomorphic germs vanishing on a fixed local set germ form an ideal. -/
def vanishingIdeal {n : ℕ} (Z : LocalSetGerm n) : Ideal (HolomorphicGerm n) where
  carrier := {f | Z ≤ germZeroLocus f}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    exact (le_inf hf hg).trans (germZeroLocus_inf_le_add f g)
  smul_mem' := by
    intro a f hf
    exact hf.trans (germZeroLocus_le_mul a f)

/--
@isnad1 id=iff.0h3v.s11.ebe2ac45dfc4 from=translated src=- shape=bb38e2ac vocab=576ad10c
-/
@[simp]
theorem mem_vanishingIdeal {n : ℕ} {Z : LocalSetGerm n}
    {f : HolomorphicGerm n} :
    f ∈ vanishingIdeal Z ↔ Z ≤ germZeroLocus f :=
  Iff.rfl

/-- The only holomorphic germ vanishing on a full neighborhood is zero.
@isnad1 id=eq.0h1v.s11.9bf7563babc3 from=translated src=- shape=44dd6f61 vocab=076375c5
-/
@[simp]
theorem vanishingIdeal_top (n : ℕ) :
    vanishingIdeal (⊤ : LocalSetGerm n) = ⊥ := by
  ext f
  rw [mem_vanishingIdeal, Ideal.mem_bot, top_le_iff,
    germZeroLocus_eq_top_iff]

/-- Common zero set of a finite family of germs. -/
def finiteCommonZeroSet {n : ℕ} (S : Finset (HolomorphicGerm n)) :
    LocalSetGerm n :=
  S.inf germZeroLocus

/-- Common zero-set germ of a finite indexed family.  Unlike a `Finset` of
germs, this retains the indices used by the comparator-facing certificate. -/
def indexedCommonZeroSet {n s : ℕ}
    (f : Fin s → HolomorphicGerm n) : LocalSetGerm n :=
  Finset.univ.inf fun i ↦ germZeroLocus (f i)

/-- Common zero-set germ of a family indexed by an arbitrary finite type. -/
def fintypeCommonZeroSet {n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → HolomorphicGerm n) : LocalSetGerm n :=
  Finset.univ.inf fun i ↦ germZeroLocus (f i)

private def localSetGermOfFunInfTopHom (n : ℕ) :
    InfTopHom (ComplexEuclidean n → Prop) (LocalSetGerm n) where
  toFun P := (P : LocalSetGerm n)
  map_inf' _ _ := rfl
  map_top' := rfl

/-- The indexed set-germ definition has the expected eventual pointwise
meaning for a concrete representative family.
@isnad1 id=eq.1h3v.s7.1863d450e4c8 from=translated src=- shape=ea7e8351 vocab=3f53f218
-/
theorem indexedCommonZeroSet_ofFunction {n s : ℕ}
    (f : Fin s → ComplexEuclidean n → ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) 0) :
    indexedCommonZeroSet (fun i ↦ HolomorphicGerm.ofFunction (f i) (hf i)) =
      ((fun x ↦ ∀ i, f i x = 0) : LocalSetGerm n) := by
  unfold indexedCommonZeroSet germZeroLocus
  change
    Finset.univ.inf (fun i ↦
      ((fun x ↦ f i x = 0) : LocalSetGerm n)) = _
  calc
    _ = localSetGermOfFunInfTopHom n
        (Finset.univ.inf fun i ↦ fun x ↦ f i x = 0) := by
      exact (map_finset_inf (localSetGermOfFunInfTopHom n) _ _).symm
    _ = ((fun x ↦ ∀ i, f i x = 0) : LocalSetGerm n) := by
      apply Filter.Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun x ↦ propext (by
        rw [Finset.inf_eq_iInf]
        simp)

/-- The finite-type common zero set has its expected pointwise meaning for
concrete analytic representatives.
@isnad1 id=eq.1h3v.s7.617379a998b9 from=translated src=- shape=ba8b25fb vocab=e400d2d7
-/
theorem fintypeCommonZeroSet_ofFunction {n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → ComplexEuclidean n → ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) 0) :
    fintypeCommonZeroSet
        (fun i ↦ HolomorphicGerm.ofFunction (f i) (hf i)) =
      ((fun x ↦ ∀ i, f i x = 0) : LocalSetGerm n) := by
  unfold fintypeCommonZeroSet germZeroLocus
  change
    Finset.univ.inf (fun i ↦
      ((fun x ↦ f i x = 0) : LocalSetGerm n)) = _
  calc
    _ = localSetGermOfFunInfTopHom n
        (Finset.univ.inf fun i ↦ fun x ↦ f i x = 0) := by
      exact (map_finset_inf (localSetGermOfFunInfTopHom n) _ _).symm
    _ = ((fun x ↦ ∀ i, f i x = 0) : LocalSetGerm n) := by
      apply Filter.Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun x ↦ propext (by
        rw [Finset.inf_eq_iInf]
        simp)

/-- Translate a finite-type representative common-zero hypothesis into the
order relation on local set germs.
@isnad1 id=iff.2h4v.s8.2168b4e36ad9 from=translated src=- shape=812c3894 vocab=099c6dd3
-/
theorem fintypeCommonZeroSet_le_iff_eventually {n : ℕ}
    {ι : Type*} [Fintype ι]
    (f : ι → ComplexEuclidean n → ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) 0)
    (g : ComplexEuclidean n → ℂ) (hg : AnalyticAt ℂ g 0) :
    fintypeCommonZeroSet
        (fun i ↦ HolomorphicGerm.ofFunction (f i) (hf i)) ≤
        germZeroLocus (HolomorphicGerm.ofFunction g hg) ↔
      ∀ᶠ x in 𝓝 0, (∀ i, f i x = 0) → g x = 0 := by
  rw [fintypeCommonZeroSet_ofFunction f hf]
  change
    ((fun x ↦ ∀ i, f i x = 0) : LocalSetGerm n) ≤
        ((fun x ↦ g x = 0) : LocalSetGerm n) ↔ _
  exact Filter.Germ.coe_le

/-- A finite set and the family indexed by its subtype define the same common
zero-set germ.
@isnad1 id=eq.0h2v.s12.66d7ae47ef92 from=translated src=- shape=bedea57f vocab=574045a3
-/
theorem finiteCommonZeroSet_eq_fintypeCommonZeroSet_subtype {n : ℕ}
    (S : Finset (HolomorphicGerm n)) :
    finiteCommonZeroSet S =
      fintypeCommonZeroSet (fun f : S ↦ (f : HolomorphicGerm n)) := by
  classical
  unfold finiteCommonZeroSet fintypeCommonZeroSet
  apply le_antisymm
  · apply Finset.le_inf
    intro f hf
    exact Finset.inf_le f.property
  · apply Finset.le_inf
    intro f hf
    exact Finset.inf_le
      (show (⟨f, hf⟩ : S) ∈ (Finset.univ : Finset S) by simp)

/-- Translate the representative-level eventual common-zero hypothesis into
the order relation on local set germs.
@isnad1 id=iff.2h4v.s8.387b0e8af781 from=translated src=- shape=24f3185a vocab=72377528
-/
theorem indexedCommonZeroSet_le_iff_eventually {n s : ℕ}
    (f : Fin s → ComplexEuclidean n → ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) 0)
    (g : ComplexEuclidean n → ℂ) (hg : AnalyticAt ℂ g 0) :
    indexedCommonZeroSet (fun i ↦ HolomorphicGerm.ofFunction (f i) (hf i)) ≤
        germZeroLocus (HolomorphicGerm.ofFunction g hg) ↔
      ∀ᶠ x in 𝓝 0, (∀ i, f i x = 0) → g x = 0 := by
  rw [indexedCommonZeroSet_ofFunction f hf]
  change
    ((fun x ↦ ∀ i, f i x = 0) : LocalSetGerm n) ≤
        ((fun x ↦ g x = 0) : LocalSetGerm n) ↔ _
  exact Filter.Germ.coe_le

/--
@isnad1 id=le.1h3v.s10.7b3b38d6fddd from=translated src=- shape=e2fc41a6 vocab=cd133b2f
-/
theorem finiteCommonZeroSet_le_germZeroLocus {n : ℕ}
    (S : Finset (HolomorphicGerm n)) {f : HolomorphicGerm n} (hf : f ∈ S) :
    finiteCommonZeroSet S ≤ germZeroLocus f :=
  Finset.inf_le hf

/-- Every member of the ideal spanned by `S` vanishes on the common zero set of `S`.
@isnad1 id=le.1h3v.s12.32069d6a4751 from=translated src=- shape=7721b6f5 vocab=4d54b2f4
-/
theorem finiteCommonZeroSet_le_germZeroLocus_of_mem_span {n : ℕ}
    (S : Finset (HolomorphicGerm n)) {f : HolomorphicGerm n}
    (hf : f ∈ Ideal.span (S : Set (HolomorphicGerm n))) :
    finiteCommonZeroSet S ≤ germZeroLocus f := by
  have hspan : Ideal.span (S : Set (HolomorphicGerm n)) ≤
      vanishingIdeal (finiteCommonZeroSet S) := by
    apply Ideal.span_le.mpr
    intro g hg
    exact finiteCommonZeroSet_le_germZeroLocus S hg
  exact hspan hf

/-- Enlarging the generated ideal shrinks the corresponding finite zero set.
@isnad1 id=le.1h3v.s12.7481dbd5c544 from=translated src=- shape=1db9bd1c vocab=9b4b06ce
-/
theorem finiteCommonZeroSet_antitone_span {n : ℕ}
    (S T : Finset (HolomorphicGerm n))
    (h : Ideal.span (S : Set (HolomorphicGerm n)) ≤
      Ideal.span (T : Set (HolomorphicGerm n))) :
    finiteCommonZeroSet T ≤ finiteCommonZeroSet S := by
  apply Finset.le_inf
  intro f hf
  apply finiteCommonZeroSet_le_germZeroLocus_of_mem_span T
  exact h (Ideal.subset_span hf)

/-- The finite common zero-set germ depends only on the generated ideal.
@isnad1 id=eq.1h3v.s11.8c4680f5eb56 from=translated src=- shape=3b837f63 vocab=e8d350fb
-/
theorem finiteCommonZeroSet_eq_of_span_eq {n : ℕ}
    (S T : Finset (HolomorphicGerm n))
    (h : Ideal.span (S : Set (HolomorphicGerm n)) =
      Ideal.span (T : Set (HolomorphicGerm n))) :
    finiteCommonZeroSet S = finiteCommonZeroSet T := by
  apply le_antisymm
  · exact finiteCommonZeroSet_antitone_span T S h.symm.le
  · exact finiteCommonZeroSet_antitone_span S T h.le

/-- A fixed finite generating set selected from Noetherianity. -/
def idealGeneratorFinset {n : ℕ} [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n)) : Finset (HolomorphicGerm n) :=
  Classical.choose (Ideal.fg_of_isNoetherianRing I)

/--
@isnad1 id=eq.0h2v.s11.dcce621e2617 from=translated src=- shape=6c714a91 vocab=b78b961c
-/
theorem span_idealGeneratorFinset {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n)) :
    Ideal.span (idealGeneratorFinset I : Set (HolomorphicGerm n)) = I :=
  Classical.choose_spec (Ideal.fg_of_isNoetherianRing I)

/-- The zero-set germ of an ideal, defined through a finite generating set. -/
def idealZeroSetGerm {n : ℕ} [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n)) : LocalSetGerm n :=
  finiteCommonZeroSet (idealGeneratorFinset I)

/-- Generator independence for the ideal zero-set germ.
@isnad1 id=eq.1h3v.s11.3d3637a53210 from=translated src=- shape=972bb853 vocab=868ea1ee
-/
theorem idealZeroSetGerm_eq_of_span_eq {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n))
    (S : Finset (HolomorphicGerm n))
    (hS : Ideal.span (S : Set (HolomorphicGerm n)) = I) :
    idealZeroSetGerm I = finiteCommonZeroSet S := by
  unfold idealZeroSetGerm
  apply finiteCommonZeroSet_eq_of_span_eq
  exact (span_idealGeneratorFinset I).trans hS.symm

/--
@isnad1 id=eq.0h1v.s11.1c77aa521c1d from=translated src=- shape=8a1ec3d0 vocab=186ce60d
-/
@[simp]
theorem idealZeroSetGerm_bot {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)] :
    idealZeroSetGerm (⊥ : Ideal (HolomorphicGerm n)) = ⊤ := by
  rw [idealZeroSetGerm_eq_of_span_eq
    (⊥ : Ideal (HolomorphicGerm n)) ∅ (by simp)]
  simp [finiteCommonZeroSet]

/-- Every member of an ideal vanishes on its local zero-set germ.
@isnad1 id=le.1h3v.s12.3d47823ef0e6 from=translated src=- shape=0811eb48 vocab=e07fed70
-/
theorem idealZeroSetGerm_le_germZeroLocus_of_mem {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n)) {f : HolomorphicGerm n} (hf : f ∈ I) :
    idealZeroSetGerm I ≤ germZeroLocus f := by
  unfold idealZeroSetGerm
  apply finiteCommonZeroSet_le_germZeroLocus_of_mem_span
  rw [span_idealGeneratorFinset]
  exact hf

/-- Inclusion of ideals reverses inclusion of their local zero-set germs.
@isnad1 id=le.1h3v.s12.4c4dc0b95baf from=translated src=- shape=58ada272 vocab=9365e55b
-/
theorem idealZeroSetGerm_antitone {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)]
    {I J : Ideal (HolomorphicGerm n)} (hIJ : I ≤ J) :
    idealZeroSetGerm J ≤ idealZeroSetGerm I := by
  unfold idealZeroSetGerm
  apply Finset.le_inf
  intro f hf
  apply idealZeroSetGerm_le_germZeroLocus_of_mem J
  apply hIJ
  rw [← span_idealGeneratorFinset I]
  exact Ideal.subset_span hf

end

end LocalComplexGeometry
