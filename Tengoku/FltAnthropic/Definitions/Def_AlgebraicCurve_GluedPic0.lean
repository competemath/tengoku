import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

@[simp]
private theorem ord_algebraMap_of_constant (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have hu : IsUnit (algebraMap K v.toValuationSubring c) := hc.isUnit.map _
    have h := v.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec, coe_algebraMap] at h

/--
@isnad1 id=eq.0h4v.s10.26d5826b272b from=translated src=- shape=7985b68a vocab=ede4a237
-/
theorem residue_algebraMap (c : K) :
    residue v.toValuationSubring (algebraMap K v.toValuationSubring c)
      = algebraMap K v.ResidueField c := by
  rw [IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField c,
    ResidueField.algebraMap_eq]

def HasValue (g : F) (a : K) : Prop :=
  ∃ h : g ∈ v.toValuationSubring,
    residue v.toValuationSubring ⟨g, h⟩ = algebraMap K v.ResidueField a

/--
@isnad1 id=iff.0h5v.s10.510690e02e6f from=translated src=- shape=3ae4eca9 vocab=dbb77981
-/
theorem hasValue_iff (g : F) (a : K) :
    v.HasValue g a ↔ ∃ h : g ∈ v.toValuationSubring,
      residue v.toValuationSubring ⟨g, h⟩ = algebraMap K v.ResidueField a :=
  Iff.rfl

variable {v}

/--
@isnad1 id=mem.1h5v.s6.804ad9abe141 from=translated src=- shape=a450c28c vocab=4e487bb3
-/
theorem HasValue.mem {g : F} {a : K} (h : v.HasValue g a) : g ∈ v.toValuationSubring :=
  h.1

/--
@isnad1 id=eq.1h5v.s10.f4ad978900fc from=translated src=- shape=01daf5e5 vocab=e2dd5efb
-/
theorem HasValue.residue_eq {g : F} {a : K} (h : v.HasValue g a) :
    residue v.toValuationSubring ⟨g, h.mem⟩ = algebraMap K v.ResidueField a :=
  h.2

variable (v) in
/--
@isnad1 id=hasvalue.0h3v.s6.503f22a27f4e from=translated src=- shape=7511ec0a vocab=6a52db48
-/
theorem hasValue_one : v.HasValue (1 : F) 1 :=
  ⟨one_mem _, by rw [map_one]; exact map_one (residue v.toValuationSubring)⟩

variable (v) in
/--
@isnad1 id=hasvalue.0h4v.s6.d75f6a8c7b82 from=translated src=- shape=b01749e8 vocab=50cea6e3
-/
theorem hasValue_algebraMap (c : K) : v.HasValue (algebraMap K F c) c :=
  ⟨v.algebraMap_mem' c, v.residue_algebraMap c⟩

/--
@isnad1 id=hasvalue.2h7v.s6.cb8716a74cec from=translated src=- shape=ef0bb476 vocab=47627832
-/
theorem HasValue.mul {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g * g') (a * a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨mul_mem hg hg', ?_⟩
  have hx : (⟨g * g', mul_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ * ⟨g', hg'⟩ := rfl
  rw [hx, map_mul, hr, hr', map_mul]

/--
@isnad1 id=isunit.2h5v.s7.4c0cee43cfd9 from=translated src=- shape=e57bc661 vocab=460dc806
-/
theorem HasValue.isUnit {g : F} {a : K} (h : v.HasValue g a) (ha : a ≠ 0) :
    IsUnit (⟨g, h.mem⟩ : v.toValuationSubring) := by
  rw [← residue_ne_zero_iff_isUnit, h.residue_eq]
  exact (map_ne_zero _).mpr ha

/--
@isnad1 id=ne.2h5v.s6.a125572afddf from=translated src=- shape=3d90d687 vocab=6a52db48
-/
theorem HasValue.ne_zero {g : F} {a : K} (h : v.HasValue g a) (ha : a ≠ 0) : g ≠ 0 := by
  intro hg
  apply (h.isUnit ha).ne_zero
  exact Subtype.ext hg

/--
@isnad1 id=hasvalue.2h5v.s6.af80fed667fc from=translated src=- shape=b8bbe6f3 vocab=4b81b614
-/
theorem HasValue.inv {g : F} {a : K} (h : v.HasValue g a) (ha : a ≠ 0) :
    v.HasValue g⁻¹ a⁻¹ := by
  obtain ⟨u, hu⟩ := h.isUnit ha
  have hcoe : ((u : v.toValuationSubring) : F) = g := by rw [hu]
  have hinv : (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = g⁻¹ := by
    have h1 : g * (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = 1 := by
      rw [← hcoe, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        OneMemClass.coe_one]
    exact (inv_eq_of_mul_eq_one_right h1).symm
  have hmem : g⁻¹ ∈ v.toValuationSubring := hinv ▸ SetLike.coe_mem _
  refine ⟨hmem, ?_⟩
  have hx : (⟨g⁻¹, hmem⟩ : v.toValuationSubring)
      = ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) :=
    Subtype.ext hinv.symm
  rw [hx, map_units_inv, hu, h.residue_eq, map_inv₀]

/--
@isnad1 id=eq.2h6v.s5.298867065359 from=translated src=- shape=dcca3252 vocab=6a52db48
-/
theorem HasValue.unique {g : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g a') :
    a = a' :=
  (algebraMap K v.ResidueField).injective (h.residue_eq.symm.trans h'.residue_eq)

/--
@isnad1 id=eq.2h5v.s6.d006aa38517d from=translated src=- shape=1c6e23fd vocab=fbde2269
-/
theorem HasValue.ord_eq_zero {g : F} {a : K} (h : v.HasValue g a) (ha : a ≠ 0) : v.ord g = 0 := by
  have h0 := v.ord_coe_unit (h.isUnit ha).unit
  rwa [IsUnit.unit_spec] at h0

variable (v) in

/--
@isnad1 id=ex.2h4v.s7.8d2da11cddf9 from=translated src=- shape=d3b1d75a vocab=db3e0094
-/
theorem exists_isUnit_of_ord_eq_zero {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    ∃ hm : f ∈ v.toValuationSubring, IsUnit (⟨f, hm⟩ : v.toValuationSubring) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [h, zpow_zero, mul_one] at hu
  subst hu
  exact ⟨(u : v.toValuationSubring).2, u.isUnit⟩

variable (v) in

/--
@isnad1 id=ex.2h4v.s9.68ba2c664e7a from=translated src=- shape=b165b96f vocab=cb84eeaa
-/
theorem exists_hasValue_of_surjective (hv : Function.Surjective (algebraMap K v.ResidueField))
    {g : F} (hg : g ∈ v.toValuationSubring) :
    ∃ a : K, v.HasValue g a ∧ (IsUnit (⟨g, hg⟩ : v.toValuationSubring) → a ≠ 0) := by
  obtain ⟨a, ha⟩ := hv (residue v.toValuationSubring ⟨g, hg⟩)
  refine ⟨a, ⟨hg, ha.symm⟩, fun hu h0 => ?_⟩
  rw [← residue_ne_zero_iff_isUnit, ← ha, h0, map_zero] at hu
  exact hu rfl

end Place

section Glued

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

abbrev GluingData (S : Finset (Place K F × Place K F)) : Type _ :=
  Divisor K F × Divisor K F × (↥S → Additive Kˣ)

namespace GluingData

variable {K F}
variable (S : Finset (Place K F × Place K F))

def admissible : AddSubgroup (GluingData K F S) where
  carrier := {x | x.1 ∈ Divisor.degZero (K := K) (F := F) ∧
    x.2.1 ∈ Divisor.degZero (K := K) (F := F) ∧ ∀ s ∈ S, x.1 s.1 = 0 ∧ x.2.1 s.2 = 0}
  zero_mem' := ⟨zero_mem _, zero_mem _, fun _ _ => ⟨rfl, rfl⟩⟩
  add_mem' := by
    rintro x y ⟨hx₁, hx₂, hx⟩ ⟨hy₁, hy₂, hy⟩
    refine ⟨add_mem hx₁ hy₁, add_mem hx₂ hy₂, fun s hs => ⟨?_, ?_⟩⟩
    · rw [Prod.fst_add, Finsupp.add_apply, (hx s hs).1, (hy s hs).1, add_zero]
    · rw [Prod.snd_add, Prod.fst_add, Finsupp.add_apply, (hx s hs).2, (hy s hs).2, add_zero]
  neg_mem' := by
    rintro x ⟨hx₁, hx₂, hx⟩
    refine ⟨neg_mem hx₁, neg_mem hx₂, fun s hs => ⟨?_, ?_⟩⟩
    · rw [Prod.fst_neg, Finsupp.neg_apply, (hx s hs).1, neg_zero]
    · rw [Prod.snd_neg, Prod.fst_neg, Finsupp.neg_apply, (hx s hs).2, neg_zero]

/--
@isnad1 id=iff.0h4v.s11.de057bff0c5d from=translated src=- shape=e968978d vocab=992727fa
-/
theorem mem_admissible {x : GluingData K F S} :
    x ∈ admissible S ↔ x.1 ∈ Divisor.degZero (K := K) (F := F) ∧
      x.2.1 ∈ Divisor.degZero (K := K) (F := F) ∧ ∀ s ∈ S, x.1 s.1 = 0 ∧ x.2.1 s.2 = 0 :=
  Iff.rfl

/--
@isnad1 id=mem.0h4v.s11.2dc9ea099d02 from=translated src=- shape=30147fcc vocab=cf063b4e
-/
theorem zero_zero_mem_admissible (w : ↥S → Additive Kˣ) :
    ((0, 0, w) : GluingData K F S) ∈ admissible S :=
  ⟨zero_mem _, zero_mem _, fun _ _ => ⟨rfl, rfl⟩⟩

def IsGluedPrincipal (x : GluingData K F S) : Prop :=
  ∃ (g₁ g₂ : F) (a b : ↥S → Kˣ), g₁ ≠ 0 ∧ g₂ ≠ 0 ∧
    (∀ v : Place K F, x.1 v = v.ord g₁) ∧ (∀ v : Place K F, x.2.1 v = v.ord g₂) ∧
    (∀ s : ↥S, (s : Place K F × Place K F).1.HasValue g₁ (a s) ∧
      (s : Place K F × Place K F).2.HasValue g₂ (b s)) ∧
    x.2.2 = fun s => Additive.ofMul (a s / b s)

def gluedPrincipal : AddSubgroup (GluingData K F S) where
  carrier := {x | IsGluedPrincipal S x}
  zero_mem' := by
    refine ⟨1, 1, 1, 1, one_ne_zero, one_ne_zero, fun v => by simp, fun v => by simp,
      fun s => ⟨?_, ?_⟩, ?_⟩
    · simpa using (s : Place K F × Place K F).1.hasValue_one
    · simpa using (s : Place K F × Place K F).2.hasValue_one
    · funext s
      simp
  add_mem' := by
    rintro x y ⟨g₁, g₂, a, b, hg₁, hg₂, hx₁, hx₂, hv, hw⟩
      ⟨g₁', g₂', a', b', hg₁', hg₂', hy₁, hy₂, hv', hw'⟩
    refine ⟨g₁ * g₁', g₂ * g₂', a * a', b * b', mul_ne_zero hg₁ hg₁', mul_ne_zero hg₂ hg₂',
      fun v => ?_, fun v => ?_, fun s => ⟨?_, ?_⟩, ?_⟩
    · rw [Prod.fst_add, Finsupp.add_apply, hx₁ v, hy₁ v, v.ord_mul hg₁ hg₁']
    · rw [Prod.snd_add, Prod.fst_add, Finsupp.add_apply, hx₂ v, hy₂ v, v.ord_mul hg₂ hg₂']
    · simpa only [Pi.mul_apply, Units.val_mul] using (hv s).1.mul (hv' s).1
    · simpa only [Pi.mul_apply, Units.val_mul] using (hv s).2.mul (hv' s).2
    · rw [Prod.snd_add, Prod.snd_add, hw, hw']
      funext s
      rw [Pi.add_apply, Pi.mul_apply, Pi.mul_apply, ← ofMul_mul, div_mul_div_comm]
  neg_mem' := by
    rintro x ⟨g₁, g₂, a, b, hg₁, hg₂, hx₁, hx₂, hv, hw⟩
    refine ⟨g₁⁻¹, g₂⁻¹, a⁻¹, b⁻¹, inv_ne_zero hg₁, inv_ne_zero hg₂,
      fun v => ?_, fun v => ?_, fun s => ⟨?_, ?_⟩, ?_⟩
    · rw [Prod.fst_neg, Finsupp.neg_apply, hx₁ v, v.ord_inv]
    · rw [Prod.snd_neg, Prod.fst_neg, Finsupp.neg_apply, hx₂ v, v.ord_inv]
    · simpa only [Pi.inv_apply, Units.val_inv_eq_inv_val] using (hv s).1.inv (a s).ne_zero
    · simpa only [Pi.inv_apply, Units.val_inv_eq_inv_val] using (hv s).2.inv (b s).ne_zero
    · rw [Prod.snd_neg, Prod.snd_neg, hw]
      funext s
      rw [Pi.neg_apply, Pi.inv_apply, Pi.inv_apply, inv_div_inv, ← ofMul_inv, inv_div]

/--
@isnad1 id=iff.0h4v.s10.bba1e661e64a from=translated src=- shape=86205638 vocab=04c51e0a
-/
theorem mem_gluedPrincipal {x : GluingData K F S} :
    x ∈ gluedPrincipal S ↔ IsGluedPrincipal S x :=
  Iff.rfl

end GluingData

abbrev GluedPic0 (S : Finset (Place K F × Place K F)) : Type _ :=
  ↥(GluingData.admissible S) ⧸ (GluingData.gluedPrincipal S).addSubgroupOf (GluingData.admissible S)

namespace GluedPic0

variable {K F}
variable (S : Finset (Place K F × Place K F))

def mk : ↥(GluingData.admissible S) →+ GluedPic0 K F S :=
  QuotientAddGroup.mk' _

/--
@isnad1 id=surjecti.0h3v.s14.755e4f3531f5 from=translated src=- shape=e59d8308 vocab=26cf4b90
-/
theorem mk_surjective : Function.Surjective (mk S) :=
  QuotientAddGroup.mk'_surjective _

/--
@isnad1 id=iff.0h4v.s15.d85e5a983f7a from=translated src=- shape=97ea7078 vocab=c011bf71
-/
theorem mk_eq_zero_iff (x : ↥(GluingData.admissible S)) :
    mk S x = 0 ↔ GluingData.IsGluedPrincipal S (x : GluingData K F S) :=
  QuotientAddGroup.eq_zero_iff _

/--
@isnad1 id=iff.0h5v.s16.0a7c2cf04fed from=translated src=- shape=4b199de5 vocab=4d535539
-/
theorem mk_eq_mk_iff (x y : ↥(GluingData.admissible S)) :
    mk S x = mk S y ↔ GluingData.IsGluedPrincipal S (-(x : GluingData K F S) + y) :=
  QuotientAddGroup.eq

def toPic0PairAux : ↥(GluingData.admissible S) →+ Pic0 K F × Pic0 K F where
  toFun x := (Pic0.mk ⟨(x : GluingData K F S).1, x.2.1⟩,
    Pic0.mk ⟨(x : GluingData K F S).2.1, x.2.2.1⟩)
  map_zero' := rfl
  map_add' _ _ := rfl

def toPic0Pair : GluedPic0 K F S →+ Pic0 K F × Pic0 K F :=
  QuotientAddGroup.lift _ (toPic0PairAux S) <| by
    rintro x ⟨g₁, g₂, _, _, hg₁, hg₂, h₁, h₂, -, -⟩
    rw [AddMonoidHom.mem_ker]
    exact Prod.ext ((QuotientAddGroup.eq_zero_iff _).mpr ⟨g₁, hg₁, h₁⟩)
      ((QuotientAddGroup.eq_zero_iff _).mpr ⟨g₂, hg₂, h₂⟩)

/--
@isnad1 id=eq.0h4v.s15.ba638d0774f0 from=translated src=- shape=de5c2cd9 vocab=9f11af3d
-/
@[simp]
theorem toPic0Pair_mk (x : ↥(GluingData.admissible S)) :
    toPic0Pair S (mk S x) = (Pic0.mk ⟨(x : GluingData K F S).1, x.2.1⟩,
      Pic0.mk ⟨(x : GluingData K F S).2.1, x.2.2.1⟩) :=
  rfl

def nodeUnitAux : (↥S → Additive Kˣ) →+ ↥(GluingData.admissible S) where
  toFun w := ⟨(0, 0, w), GluingData.zero_zero_mem_admissible S w⟩
  map_zero' := rfl
  map_add' _ _ := Subtype.ext <| Prod.ext (add_zero _).symm (Prod.ext (add_zero _).symm rfl)

def nodeUnit : (↥S → Additive Kˣ) →+ GluedPic0 K F S :=
  (mk S).comp (nodeUnitAux S)

/--
@isnad1 id=eq.0h4v.s15.8e6920fd50c2 from=translated src=- shape=9d669696 vocab=bbf57eae
-/
theorem nodeUnit_apply (w : ↥S → Additive Kˣ) :
    nodeUnit S w = mk S ⟨(0, 0, w), GluingData.zero_zero_mem_admissible S w⟩ :=
  rfl

/--
@isnad1 id=eq.0h4v.s13.737eeab3f236 from=translated src=- shape=cad7ecdc vocab=5c0fe69d
-/
@[simp]
theorem toPic0Pair_nodeUnit (w : ↥S → Additive Kˣ) : toPic0Pair S (nodeUnit S w) = 0 :=
  rfl

/--
@isnad1 id=eq.0h3v.s12.b77968493a6f from=translated src=- shape=f54de43b vocab=43fbf24a
-/
theorem toPic0Pair_comp_nodeUnit : (toPic0Pair S).comp (nodeUnit S) = 0 :=
  AddMonoidHom.ext (toPic0Pair_nodeUnit S)

/--
@isnad1 id=eq.0h4v.s13.06cdfff23072 from=translated src=- shape=fc1431a7 vocab=2d540598
-/
theorem nodeUnit_const (c : Kˣ) : nodeUnit S (fun _ => Additive.ofMul c) = 0 := by
  rw [nodeUnit_apply, mk_eq_zero_iff]
  refine ⟨algebraMap K F c, 1, fun _ => c, 1, (map_ne_zero _).mpr c.ne_zero, one_ne_zero,
    fun v => by simp, fun v => by simp, fun s => ⟨?_, ?_⟩, ?_⟩
  · exact (s : Place K F × Place K F).1.hasValue_algebraMap (c : K)
  · simpa using (s : Place K F × Place K F).2.hasValue_one
  · funext s
    simp

end GluedPic0

end Glued

end AlgebraicCurve

end
