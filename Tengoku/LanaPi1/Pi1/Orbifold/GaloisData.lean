module

public import Tengoku.LanaPi1.Pi1.Orbicurve.SubfieldGalois
public import Tengoku.LanaPi1.Pi1.Orbicurve.GaloisPi1
public import Tengoku.LanaPi1.Pi1.Orbifold.EtaleProfinite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Galois data for the comparison of étale and Galois fundamental groups

Let `k` be a field, `Ω` a field over `k`, `t ∈ Ω`, `K₀ = k(t) ⊆ Ω` and
`Gal = Ω ≃ₐ[K₀] Ω`. A `GaloisData k t` consists of open subgroups `H_L ≤ H ≤ Gal` with `H_L`
normalized by `H`. It determines

* the function field `L = Ω^{H_L}` (`GaloisData.L`) and its coordinate ring `R`, the integral
  closure of `k[t]` in `L` (`GaloisData.R`);
* the finite group `A = H ⧸ H_L` (`GaloisData.A`), acting on `R` by ring automorphisms
  (`H` maps `L` to itself as it normalizes `H_L`, and `H_L` acts trivially on `L`);
* the set `S ⊆ H_L` of inertia elements at the places of `Ω` centered on `Spec R`
  (`GaloisData.S`).

The quotient orbifold `[Spec R / A]` has étale fundamental group `etalePi1 R A Ω`, which is
compared with `GaloisPi1.pi1 H S` in `Pi1.Orbifold.Comparison`.

We also record generalities on the coordinate rings `coordRing k t F`: elements are determined by
their image in `Ω` (`CoordRing.ext`), and a subgroup of `Gal` stabilizing `F` acts on
`coordRing k t F` (`coordAut`).
-/

@[expose] public section

universe u

open AffOrbicurve IntermediateField.algebraAdjoinAdjoin

namespace Pi1.Orbifold

section Coord

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

variable (k t) in
/-- The coordinate ring `coordRing k t F` (the integral closure of `k[t]` in `F`), as a type with
only the instances needed here (this keeps instance search fast).-/
def CoordRing (F : IntermediateField (K₀ k t) Ω) : Type u :=
  coordRing k t F

namespace CoordRing

variable (F : IntermediateField (K₀ k t) Ω)

instance : CommRing (CoordRing k t F) := inferInstanceAs (CommRing (coordRing k t F))
instance : IsDomain (CoordRing k t F) := inferInstanceAs (IsDomain (coordRing k t F))
instance : Algebra (CoordRing k t F) Ω := inferInstanceAs (Algebra (coordRing k t F) Ω)
instance : Algebra (A₀ k t) (CoordRing k t F) :=
  inferInstanceAs (Algebra (A₀ k t) (coordRing k t F))
instance : IsScalarTower (A₀ k t) (CoordRing k t F) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
instance : Algebra.IsIntegral (A₀ k t) (CoordRing k t F) :=
  inferInstanceAs (Algebra.IsIntegral (A₀ k t) (integralClosure (A₀ k t) F))

variable {F}

/--
@isnad1 id=eq.1h6v.s8.41834e64ce6e from=translated src=- shape=71e55f61 vocab=0f3e50d8
-/
lemma ext {x y : CoordRing k t F}
    (h : algebraMap (CoordRing k t F) Ω x = algebraMap (CoordRing k t F) Ω y) : x = y :=
  Subtype.ext (Subtype.ext h)

/--
@isnad1 id=injectiv.0h4v.s8.114301107921 from=translated src=- shape=627fae89 vocab=fdb23857
-/
lemma algebraMap_injective : Function.Injective (algebraMap (CoordRing k t F) Ω) :=
  fun _ _ h => ext h

/--
@isnad1 id=mem.0h5v.s9.0d4e1b4f0ed1 from=translated src=- shape=fc4d31ba vocab=0f3e50d8
-/
lemma algebraMap_mem (x : CoordRing k t F) : algebraMap (CoordRing k t F) Ω x ∈ F :=
  (show coordRing k t F from x).1.2

/--
@isnad1 id=iff.0h5v.s11.1ef636a0ba97 from=translated src=- shape=4adfaacd vocab=2821ee9c
-/
lemma isIntegral_coe_iff (y : F) : IsIntegral (A₀ k t) (y : Ω) ↔ IsIntegral (A₀ k t) y :=
  isIntegral_algHom_iff ((IntermediateField.val F).restrictScalars (A₀ k t))
    (IntermediateField.val F).injective

/--
@isnad1 id=isintegr.0h5v.s8.4b23db6c4562 from=translated src=- shape=1c4f9adf vocab=4de0a908
-/
lemma isIntegral_algebraMap (x : CoordRing k t F) :
    IsIntegral (A₀ k t) (algebraMap (CoordRing k t F) Ω x) :=
  (isIntegral_coe_iff (show coordRing k t F from x).1).2 (show coordRing k t F from x).2

/-- An element of `Ω` lying in `F` and integral over `k[t]`, as an element of the coordinate ring
of `F`.-/
def mk (x : Ω) (hF : x ∈ F) (hx : IsIntegral (A₀ k t) x) : CoordRing k t F :=
  (⟨⟨x, hF⟩, (isIntegral_coe_iff (F := F) ⟨x, hF⟩).1 hx⟩ : coordRing k t F)

/--
@isnad1 id=eq.2h5v.s9.d3118345d6c7 from=translated src=- shape=8185b486 vocab=6d666aeb
-/
@[simp] lemma algebraMap_mk (x : Ω) (hF : x ∈ F) (hx : IsIntegral (A₀ k t) x) :
    algebraMap (CoordRing k t F) Ω (mk x hF hx) = x := rfl

/-- The inclusion `CoordRing k t F → CoordRing k t F'` for `F ≤ F'`, as an algebra structure.-/
noncomputable abbrev algOfLE {F' : IntermediateField (K₀ k t) Ω} (h : F ≤ F') :
    Algebra (CoordRing k t F) (CoordRing k t F') :=
  (ringMap t h).toRingHom.toAlgebra

/-- The coordinate ring is a `k`-algebra (through `k[t] ⊆ coordRing`).-/
instance algebraK (F : IntermediateField (K₀ k t) Ω) : Algebra k (CoordRing k t F) :=
  ((algebraMap (A₀ k t) (CoordRing k t F)).comp (algebraMap k (A₀ k t))).toAlgebra

end CoordRing

/--
@isnad1 id=isintegr.1h5v.s9.9091a0263d36 from=translated src=- shape=5611105c vocab=0d5e4121
-/
lemma isIntegral_aut (σ : Ω ≃ₐ[K₀ k t] Ω) {x : Ω} (hx : IsIntegral (A₀ k t) x) :
    IsIntegral (A₀ k t) (σ x) :=
  hx.map ((σ : Ω →ₐ[K₀ k t] Ω).restrictScalars (A₀ k t))

/-- A subgroup `G` of `Gal` stabilizing `F` acts on the coordinate ring of `F`.-/
def coordAut (F : IntermediateField (K₀ k t) Ω) (G : Subgroup (Ω ≃ₐ[K₀ k t] Ω))
    (hG : ∀ g ∈ G, ∀ x ∈ F, g x ∈ F) : G →* RingAut (CoordRing k t F) where
  toFun g :=
    { toFun := fun x => CoordRing.mk (g.1 (algebraMap _ Ω x))
        (hG g g.2 _ (CoordRing.algebraMap_mem x))
        (isIntegral_aut _ (CoordRing.isIntegral_algebraMap x))
      invFun := fun x => CoordRing.mk (g.1⁻¹ (algebraMap _ Ω x))
        (hG _ (G.inv_mem g.2) _ (CoordRing.algebraMap_mem x))
        (isIntegral_aut _ (CoordRing.isIntegral_algebraMap x))
      left_inv := fun x => CoordRing.ext (by
        change (g.1⁻¹ * g.1) _ = _
        rw [inv_mul_cancel]; rfl)
      right_inv := fun x => CoordRing.ext (by
        change (g.1 * g.1⁻¹) _ = _
        rw [mul_inv_cancel]; rfl)
      map_mul' := fun x y => CoordRing.ext (by
        change g.1 (algebraMap _ Ω (x * y)) = g.1 (algebraMap _ Ω x) * g.1 (algebraMap _ Ω y)
        rw [map_mul, map_mul])
      map_add' := fun x y => CoordRing.ext (by
        change g.1 (algebraMap _ Ω (x + y)) = g.1 (algebraMap _ Ω x) + g.1 (algebraMap _ Ω y)
        rw [map_add, map_add]) }
  map_one' := RingEquiv.ext fun x => CoordRing.ext rfl
  map_mul' g h := RingEquiv.ext fun x => CoordRing.ext rfl

/--
@isnad1 id=eq.1h7v.s14.b12e3a572377 from=translated src=- shape=b79c6fd3 vocab=bb724ccd
-/
@[simp] lemma algebraMap_coordAut (F : IntermediateField (K₀ k t) Ω)
    (G : Subgroup (Ω ≃ₐ[K₀ k t] Ω)) (hG : ∀ g ∈ G, ∀ x ∈ F, g x ∈ F) (g : G)
    (x : CoordRing k t F) :
    algebraMap (CoordRing k t F) Ω (coordAut F G hG g x) = g.1 (algebraMap _ Ω x) := rfl

/-- If `G` normalizes `U`, then `G` stabilizes the fixed field of `U`.
@isnad1 id=mem.3h7v.s13.3e74dd281c5e from=translated src=- shape=558354f6 vocab=43444fe0
-/
lemma mem_fixedField_of_normalizes {U G : Subgroup (Ω ≃ₐ[K₀ k t] Ω)}
    (hUG : ∀ g ∈ G, ∀ u ∈ U, g⁻¹ * u * g ∈ U) :
    ∀ g ∈ G, ∀ x ∈ IntermediateField.fixedField U, g x ∈ IntermediateField.fixedField U := by
  intro g hg x hx
  rw [IntermediateField.mem_fixedField_iff] at hx ⊢
  intro u hu
  have h := hx _ (hUG g hg u hu)
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at h
  calc u (g x) = g ((g⁻¹ : Ω ≃ₐ[K₀ k t] Ω) (u (g x))) := by simp
    _ = g x := by rw [h]

end Coord

variable (k : Type u) {Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] (t : Ω)

/-- **Galois data** for an orbifold quotient `[Spec R / A]` of the normalization `Spec R` of the
`t`-line in a finite extension of `k(t)` inside `Ω`: open subgroups `H_L ≤ H` of
`Gal(Ω / k(t))` with `H_L` normalized by `H`.-/
structure GaloisData where
  /-- The group `H` (the automorphisms of `Ω` over the function field of the coarse space).-/
  H : Subgroup (Ω ≃ₐ[K₀ k t] Ω)
  /-- The group `H_L` (the automorphisms of `Ω` over the function field `L`).-/
  HL : Subgroup (Ω ≃ₐ[K₀ k t] Ω)
  /-- `H_L ≤ H`.-/
  le : HL ≤ H
  /-- `H_L` is open.-/
  isOpen_HL : IsOpen (HL : Set (Ω ≃ₐ[K₀ k t] Ω))
  /-- `H` normalizes `H_L`.-/
  conj_mem : ∀ h ∈ H, ∀ n ∈ HL, h * n * h⁻¹ ∈ HL
  /-- `t` is transcendental over `k`.-/
  transcendental : Transcendental k t

namespace GaloisData

variable {k t} (D : GaloisData k t)

/--
@isnad1 id=isopen.0h4v.s9.8160581f2c76 from=translated src=- shape=5b830fa0 vocab=13ecefe6
-/
lemma isOpen_H : IsOpen (D.H : Set (Ω ≃ₐ[K₀ k t] Ω)) := Subgroup.isOpen_mono D.le D.isOpen_HL

/--
@isnad1 id=isclosed.0h4v.s9.125d9acd8cdf from=translated src=- shape=5b830fa0 vocab=6a7255a9
-/
lemma isClosed_H : IsClosed (D.H : Set (Ω ≃ₐ[K₀ k t] Ω)) :=
  Subgroup.isClosed_of_isOpen _ D.isOpen_H

/--
@isnad1 id=mem.2h6v.s12.4112bedbcdf0 from=translated src=- shape=8105be6d vocab=0e08a5fb
-/
lemma conj_mem' {h : Ω ≃ₐ[K₀ k t] Ω} (hh : h ∈ D.H) {n : Ω ≃ₐ[K₀ k t] Ω} (hn : n ∈ D.HL) :
    h⁻¹ * n * h ∈ D.HL := by
  simpa using D.conj_mem h⁻¹ (D.H.inv_mem hh) n hn

/-- The function field `L = Ω^{H_L}`.-/
def L : IntermediateField (K₀ k t) Ω := IntermediateField.fixedField D.HL

/-- The coordinate ring `R = coordRing k t L` of the normalization of the `t`-line in `L`.-/
abbrev R : Type u := CoordRing k t D.L

/-- The finite group `A = H ⧸ H_L`.-/
abbrev A : Type u := D.H ⧸ D.HL.subgroupOf D.H

instance : (D.HL.subgroupOf D.H).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact D.conj_mem g g.2 n hn⟩

/--
@isnad1 id=mem.2h6v.s10.34c909f5ec6e from=translated src=- shape=892f6ff1 vocab=75d069c0
-/
lemma stable : ∀ g ∈ D.H, ∀ x ∈ D.L, g x ∈ D.L :=
  mem_fixedField_of_normalizes fun _ hg _ hu => D.conj_mem' hg hu

/-- The action of `H` on `R`.-/
def actR : D.H →* RingAut D.R := coordAut D.L D.H D.stable

/--
@isnad1 id=le.0h4v.s13.1f732682a6b1 from=translated src=- shape=afdbe69d vocab=83025350
-/
lemma subgroupOf_le_ker : D.HL.subgroupOf D.H ≤ D.actR.ker := by
  intro n hn
  rw [Subgroup.mem_subgroupOf] at hn
  rw [MonoidHom.mem_ker]
  refine RingEquiv.ext fun x => CoordRing.ext ?_
  change (n : Ω ≃ₐ[K₀ k t] Ω) (algebraMap D.R Ω x) = _
  exact (IntermediateField.mem_fixedField_iff _ _).1 (CoordRing.algebraMap_mem x) _ hn

/-- The action of `A = H ⧸ H_L` on `R`.-/
instance : MulSemiringAction D.A D.R :=
  MulSemiringAction.compHom _ (QuotientGroup.lift _ D.actR D.subgroupOf_le_ker)

/--
@isnad1 id=eq.0h6v.s15.bfd48404524f from=translated src=- shape=27f5d452 vocab=78f0c5db
-/
lemma algebraMap_smul (h : D.H) (r : D.R) :
    algebraMap D.R Ω ((h : D.A) • r) = (h : Ω ≃ₐ[K₀ k t] Ω) (algebraMap D.R Ω r) := rfl

/-- **The inertia elements** at the places of `Ω` centered on `Spec R`: the elements of `H_L`
lying in the inertia group of a valuation subring `W ⊆ Ω` containing `k` and `t`.-/
def S : Set (Ω ≃ₐ[K₀ k t] Ω) :=
  {σ | σ ∈ D.HL ∧ ∃ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) ∧ t ∈ W ∧
    σ ∈ GaloisPi1.inertia W}

/-- A section of `H → A = H ⧸ H_L` mapping `1` to `1`.-/
noncomputable def sec (a : D.A) : D.H := Quotient.out a * (Quotient.out (1 : D.A))⁻¹

/--
@isnad1 id=eq.0h5v.s12.31ea56caedad from=translated src=- shape=e0da546c vocab=0f053aaa
-/
@[simp] lemma mk_sec (a : D.A) : (D.sec a : D.A) = a := by
  simp [sec]

/--
@isnad1 id=eq.0h4v.s12.b4a4ab5245ac from=translated src=- shape=06fdb9da vocab=8b2ab460
-/
@[simp] lemma sec_one : D.sec 1 = 1 := mul_inv_cancel _

/--
@isnad1 id=eq.0h6v.s14.c86d4ef6637b from=translated src=- shape=17718c25 vocab=99ead6f1
-/
lemma mk_sec_mul_sec_inv (a b : D.A) : ((D.sec b * (D.sec (a⁻¹ * b))⁻¹ : D.H) : D.A) = a := by
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mk_sec, mk_sec]
  group

section Galois

variable [IsGalois (K₀ k t) Ω]

end Galois

end GaloisData

end Pi1.Orbifold
