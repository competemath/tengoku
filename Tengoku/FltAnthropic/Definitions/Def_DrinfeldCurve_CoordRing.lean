import Tengoku.Seed.RingTheory.MvPolynomial.Basic
import Tengoku.Seed.RingTheory.RootsOfUnity.PrimitiveRoots
import Tengoku.Seed.FieldTheory.Finite.GaloisField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u

noncomputable section

open MvPolynomial

namespace DrinfeldCurve

variable (q : ℕ) (k : Type u) [Field k]

def drinfeldPoly : MvPolynomial (Fin 2) k := X 0 * X 1 ^ q - X 0 ^ q * X 1

def drinfeldIdeal : Ideal (MvPolynomial (Fin 2) k) := Ideal.span {drinfeldPoly q k - 1}

def CoordRing : Type u := MvPolynomial (Fin 2) k ⧸ drinfeldIdeal q k

instance instCommRingCoordRing : CommRing (CoordRing q k) :=
  inferInstanceAs (CommRing (MvPolynomial (Fin 2) k ⧸ drinfeldIdeal q k))

instance instAlgebraCoordRing : Algebra k (CoordRing q k) :=
  inferInstanceAs (Algebra k (MvPolynomial (Fin 2) k ⧸ drinfeldIdeal q k))

def mk : MvPolynomial (Fin 2) k →ₐ[k] CoordRing q k := Ideal.Quotient.mkₐ k (drinfeldIdeal q k)

/--
@isnad1 id=surjecti.0h2v.s8.9053862b3d15 from=translated src=- shape=85061050 vocab=79a6ab54
-/
theorem mk_surjective : Function.Surjective (mk q k) := Ideal.Quotient.mkₐ_surjective k _

/--
@isnad1 id=eq.1h5v.s8.4b9400c47d2f from=translated src=- shape=3eec9ec6 vocab=168122d2
-/
theorem algHom_ext {A : Type*} [Semiring A] [Algebra k A] {f g : CoordRing q k →ₐ[k] A}
    (h : f.comp (mk q k) = g.comp (mk q k)) : f = g :=
  Ideal.Quotient.algHom_ext k h

/--
@isnad1 id=eq.0h2v.s8.f5f62fb1f025 from=translated src=- shape=e8e9fb33 vocab=8960ac94
-/
theorem mk_drinfeldPoly : mk q k (drinfeldPoly q k) = 1 := by
  have h : mk q k (drinfeldPoly q k - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rwa [map_sub, map_one, sub_eq_zero] at h

def x : CoordRing q k := mk q k (X 0)

def y : CoordRing q k := mk q k (X 1)

/--
@isnad1 id=eq.0h2v.s8.f37bafe2c0e3 from=translated src=- shape=e3ef57d1 vocab=95e0f074
-/
theorem relation : x q k * y q k ^ q - x q k ^ q * y q k = 1 := by
  have h := mk_drinfeldPoly q k
  rwa [drinfeldPoly, map_sub, map_mul, map_mul, map_pow, map_pow] at h

private theorem mk_mul_drinfeldPoly_sub_one (p : MvPolynomial (Fin 2) k) :
    mk q k (p * (drinfeldPoly q k - 1)) = 0 := by
  rw [map_mul, map_sub, map_one, mk_drinfeldPoly, sub_self, mul_zero]

def scalePoly (c : k) : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  aeval fun i => C c * X i

/--
@isnad1 id=eq.0h3v.s9.8e6884ad2e16 from=translated src=- shape=e997c4be vocab=5b7e5599
-/
theorem scalePoly_X (c : k) (i : Fin 2) : scalePoly k c (X i) = C c * X i := by
  simp [scalePoly]

/--
@isnad1 id=eq.0h3v.s9.790d60b8d2f4 from=translated src=- shape=e01bb7c2 vocab=9eccbdcb
-/
theorem scalePoly_drinfeldPoly (c : k) :
    scalePoly k c (drinfeldPoly q k) = C (c ^ (q + 1)) * drinfeldPoly q k := by
  simp only [drinfeldPoly, map_sub, map_mul, map_pow, scalePoly_X, mul_pow]
  ring

/--
@isnad1 id=eq.0h1v.s8.911feefbf503 from=translated src=- shape=82a129b9 vocab=c2243113
-/
theorem scalePoly_one : scalePoly k 1 = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [scalePoly_X]

/--
@isnad1 id=eq.0h3v.s8.543eb11e1188 from=translated src=- shape=4774b75e vocab=e65d9f6b
-/
theorem scalePoly_mul (c d : k) : scalePoly k (c * d) = (scalePoly k c).comp (scalePoly k d) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [scalePoly_X, AlgHom.comp_apply, map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]
  ring

section Actions

variable [Fact q.Prime] [Algebra (GaloisField q 2) k]

def ofZMod : ZMod q →+* k :=
  (algebraMap (GaloisField q 2) k).comp (algebraMap (ZMod q) (GaloisField q 2))

/--
@isnad1 id=eq.0h3v.s7.3eda42018336 from=translated src=- shape=765ded51 vocab=3bf6b044
-/
theorem ofZMod_pow_card (a : ZMod q) : ofZMod q k a ^ q = ofZMod q k a := by
  rw [← map_pow, ZMod.pow_card]

private theorem charP_base : CharP k q :=
  charP_of_injective_algebraMap (algebraMap (GaloisField q 2) k).injective q

private theorem C_ofZMod_pow (a : ZMod q) :
    (C (ofZMod q k a) : MvPolynomial (Fin 2) k) ^ q = C (ofZMod q k a) := by
  rw [← map_pow, ofZMod_pow_card]

def substPoly (g : Matrix (Fin 2) (Fin 2) (ZMod q)) :
    MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  aeval fun j => ∑ i, C (ofZMod q k (g i j)) * X i

/--
@isnad1 id=eq.0h4v.s9.282db228c5f3 from=translated src=- shape=5a694d5c vocab=6c2a0fa1
-/
theorem substPoly_X (g : Matrix (Fin 2) (Fin 2) (ZMod q)) (j : Fin 2) :
    substPoly q k g (X j) = ∑ i, C (ofZMod q k (g i j)) * X i := by
  simp [substPoly]

/--
@isnad1 id=eq.0h4v.s9.e3ab4861e302 from=translated src=- shape=8a05dbd8 vocab=f20607fe
-/
theorem substPoly_mul (g h : Matrix (Fin 2) (Fin 2) (ZMod q)) :
    substPoly q k (g * h) = (substPoly q k g).comp (substPoly q k h) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [substPoly_X, AlgHom.comp_apply, map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
    Matrix.mul_apply, Fin.sum_univ_two, map_add]
  ring

/--
@isnad1 id=eq.0h2v.s8.9f60727cbcb1 from=translated src=- shape=660c1769 vocab=e83b12b7
-/
theorem substPoly_one : substPoly q k 1 = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  intro j
  fin_cases j <;> simp [substPoly_X, Matrix.one_apply]

/--
@isnad1 id=eq.0h3v.s9.2c275e7da414 from=translated src=- shape=ea449b3b vocab=5d6d7228
-/
theorem substPoly_drinfeldPoly (g : Matrix (Fin 2) (Fin 2) (ZMod q)) :
    substPoly q k g (drinfeldPoly q k) = C (ofZMod q k g.det) * drinfeldPoly q k := by
  haveI := charP_base q k
  simp only [drinfeldPoly, map_sub, map_mul, map_pow, substPoly_X, Fin.sum_univ_two, Matrix.det_fin_two]
  rw [add_pow_char, add_pow_char]
  simp only [mul_pow, C_ofZMod_pow]
  ring

private def slEnd (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) : CoordRing q k →ₐ[k] CoordRing q k :=
  Ideal.Quotient.liftₐ (drinfeldIdeal q k) ((mk q k).comp (substPoly q k (g : Matrix (Fin 2) (Fin 2) (ZMod q))))
    (by
      intro a ha
      rw [drinfeldIdeal, Ideal.mem_span_singleton'] at ha
      obtain ⟨b, rfl⟩ := ha
      rw [AlgHom.comp_apply, map_mul, map_sub, map_one, substPoly_drinfeldPoly,
        Matrix.SpecialLinearGroup.det_coe, map_one, C_1, one_mul]
      exact mk_mul_drinfeldPoly_sub_one q k _)

private theorem slEnd_mk (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) (p : MvPolynomial (Fin 2) k) :
    slEnd q k g (mk q k p) = mk q k (substPoly q k (g : Matrix (Fin 2) (Fin 2) (ZMod q)) p) :=
  rfl

private def slEndHom : Matrix.SpecialLinearGroup (Fin 2) (ZMod q) →* (CoordRing q k →ₐ[k] CoordRing q k) where
  toFun := slEnd q k
  map_one' := by
    apply algHom_ext
    apply MvPolynomial.algHom_ext
    intro j
    simp [slEnd_mk, Matrix.SpecialLinearGroup.coe_one, substPoly_one]
  map_mul' g h := by
    apply algHom_ext
    apply MvPolynomial.algHom_ext
    intro j
    simp [slEnd_mk, Matrix.SpecialLinearGroup.coe_mul, substPoly_mul]

def slAction : Matrix.SpecialLinearGroup (Fin 2) (ZMod q) →* (CoordRing q k ≃ₐ[k] CoordRing q k) :=
  (AlgEquiv.algHomUnitsEquiv k (CoordRing q k)).toMonoidHom.comp (slEndHom q k).toHomUnits

/--
@isnad1 id=eq.0h4v.s11.ce35249e2606 from=translated src=- shape=fbf2064d vocab=e27fee81
-/
theorem slAction_mk (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) (p : MvPolynomial (Fin 2) k) :
    slAction q k g (mk q k p) = mk q k (substPoly q k (g : Matrix (Fin 2) (Fin 2) (ZMod q)) p) :=
  slEnd_mk q k g p

/--
@isnad1 id=eq.0h3v.s10.b8a9cab07da8 from=translated src=- shape=60dea917 vocab=bdc3d9df
-/
theorem slAction_x (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) :
    slAction q k g (x q k) =
      algebraMap k _ (ofZMod q k ((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0)) * x q k +
        algebraMap k _ (ofZMod q k ((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0)) * y q k := by
  simp [x, y, slAction_mk, substPoly_X, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h3v.s10.1812669c0fce from=translated src=- shape=99ecbc28 vocab=bdc3d9df
-/
theorem slAction_y (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) :
    slAction q k g (y q k) =
      algebraMap k _ (ofZMod q k ((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1)) * x q k +
        algebraMap k _ (ofZMod q k ((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1)) * y q k := by
  simp [x, y, slAction_mk, substPoly_X, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h1v.s5.781d54f9aea9 from=translated src=- shape=522f31ce vocab=e6de7ef1
-/
theorem card_galoisField_two : Nat.card (GaloisField q 2) = q ^ 2 := GaloisField.card q 2 two_ne_zero

/--
@isnad1 id=eq.0h1v.s9.490724adedff from=translated src=- shape=ca1b3cd0 vocab=e2f3f84b
-/
theorem natCard_rootsOfUnity_galoisField_two :
    Nat.card (rootsOfUnity (q + 1) (GaloisField q 2)) = q + 1 := by
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hsplit : (q - 1) * (q + 1) + 1 = q ^ 2 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hq0
    rw [Nat.add_sub_cancel]
    ring
  have hcard : Nat.card (GaloisField q 2)ˣ = (q - 1) * (q + 1) := by
    rw [Nat.card_units, card_galoisField_two, ← hsplit, Nat.add_sub_cancel]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField q 2)ˣ)
  have hord : orderOf g = (q - 1) * (q + 1) := by
    rw [← hcard, orderOf_eq_card_of_forall_mem_zpowers hg]
  have hprim : IsPrimitiveRoot (g ^ (q - 1)) (q + 1) :=
    (IsPrimitiveRoot.orderOf g).pow (hord ▸ orderOf_pos g) hord
  exact hprim.card_rootsOfUnity'

def scalarOf (ζ : (GaloisField q 2)ˣ) : k := algebraMap (GaloisField q 2) k ζ

/--
@isnad1 id=eq.1h3v.s9.d376c8e27d22 from=translated src=- shape=e6137b8b vocab=fbb834c8
-/
theorem scalarOf_pow_of_mem {ζ : (GaloisField q 2)ˣ} (hζ : ζ ∈ rootsOfUnity (q + 1) (GaloisField q 2)) :
    scalarOf q k ζ ^ (q + 1) = 1 := by
  rw [mem_rootsOfUnity] at hζ
  rw [scalarOf, ← map_pow, ← Units.val_pow_eq_pow_val, hζ, Units.val_one, map_one]

private theorem scalarOf_one : scalarOf q k 1 = 1 := by
  simp [scalarOf]

private theorem scalarOf_mul (ζ η : (GaloisField q 2)ˣ) :
    scalarOf q k (ζ * η) = scalarOf q k ζ * scalarOf q k η := by
  simp [scalarOf]

private def muEnd (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) : CoordRing q k →ₐ[k] CoordRing q k :=
  Ideal.Quotient.liftₐ (drinfeldIdeal q k) ((mk q k).comp (scalePoly k (scalarOf q k ζ)))
    (by
      intro a ha
      rw [drinfeldIdeal, Ideal.mem_span_singleton'] at ha
      obtain ⟨b, rfl⟩ := ha
      rw [AlgHom.comp_apply, map_mul, map_sub, map_one, scalePoly_drinfeldPoly, scalarOf_pow_of_mem q k ζ.2,
        C_1, one_mul]
      exact mk_mul_drinfeldPoly_sub_one q k _)

private theorem muEnd_mk (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) (p : MvPolynomial (Fin 2) k) :
    muEnd q k ζ (mk q k p) = mk q k (scalePoly k (scalarOf q k ζ) p) :=
  rfl

private def muEndHom : rootsOfUnity (q + 1) (GaloisField q 2) →* (CoordRing q k →ₐ[k] CoordRing q k) where
  toFun := muEnd q k
  map_one' := by
    apply algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp [muEnd_mk, scalarOf_one, scalePoly_one]
  map_mul' ζ η := by
    apply algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp [muEnd_mk, scalarOf_mul, scalePoly_mul]

def muAction : rootsOfUnity (q + 1) (GaloisField q 2) →* (CoordRing q k ≃ₐ[k] CoordRing q k) :=
  (AlgEquiv.algHomUnitsEquiv k (CoordRing q k)).toMonoidHom.comp (muEndHom q k).toHomUnits

/--
@isnad1 id=eq.0h4v.s13.24c2ebfc484d from=translated src=- shape=981be5d7 vocab=e1a7d6db
-/
theorem muAction_mk (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) (p : MvPolynomial (Fin 2) k) :
    muAction q k ζ (mk q k p) = mk q k (scalePoly k (scalarOf q k ζ) p) :=
  muEnd_mk q k ζ p

/--
@isnad1 id=eq.0h3v.s13.cbf3300faeec from=translated src=- shape=8fe3b258 vocab=68ba035f
-/
theorem muAction_x (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) :
    muAction q k ζ (x q k) = algebraMap k _ (scalarOf q k ζ) * x q k := by
  simp [x, muAction_mk, scalePoly_X]

/--
@isnad1 id=eq.0h3v.s13.6327207f78e7 from=translated src=- shape=8fe3b258 vocab=3665c356
-/
theorem muAction_y (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) :
    muAction q k ζ (y q k) = algebraMap k _ (scalarOf q k ζ) * y q k := by
  simp [y, muAction_mk, scalePoly_X]

/--
@isnad1 id=eq.0h4v.s9.ab332f00dba1 from=translated src=- shape=d953dd24 vocab=b89c5fcd
-/
theorem substPoly_comp_scalePoly (g : Matrix (Fin 2) (Fin 2) (ZMod q)) (c : k) :
    (substPoly q k g).comp (scalePoly k c) = (scalePoly k c).comp (substPoly q k g) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, scalePoly_X, substPoly_X, map_mul, MvPolynomial.algHom_C,
    MvPolynomial.algebraMap_eq, Fin.sum_univ_two, map_add]
  ring

/--
@isnad1 id=eq.0h4v.s14.aba6ffe3db34 from=translated src=- shape=9ffed2d1 vocab=3d94db12
-/
theorem slAction_comm_muAction (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod q))
    (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) :
    slAction q k g * muAction q k ζ = muAction q k ζ * slAction q k g := by
  ext z
  obtain ⟨p, rfl⟩ := mk_surjective q k z
  simp only [AlgEquiv.mul_apply, slAction_mk, muAction_mk]
  exact congrArg (mk q k) (AlgHom.congr_fun (substPoly_comp_scalePoly q k (g : Matrix (Fin 2) (Fin 2) (ZMod q)) (scalarOf q k ζ)) p)

/--
@isnad1 id=eq.0h4v.s10.0c4fe543ac42 from=translated src=- shape=fae1e4ad vocab=bff2198f
-/
theorem scalePoly_substPoly_drinfeldPoly (g : Matrix (Fin 2) (Fin 2) (ZMod q)) (c : k) :
    scalePoly k c (substPoly q k g (drinfeldPoly q k)) =
      C (ofZMod q k g.det * c ^ (q + 1)) * drinfeldPoly q k := by
  simp only [substPoly_drinfeldPoly, map_mul, scalePoly_drinfeldPoly, MvPolynomial.algHom_C,
    MvPolynomial.algebraMap_eq]
  ring

def hChar : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ →* (GaloisField q 2)ˣ :=
  ((Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom).comp
      (Matrix.GeneralLinearGroup.det.comp (MonoidHom.fst _ _))) *
    ((powMonoidHom (q + 1)).comp (MonoidHom.snd _ _))

/--
@isnad1 id=eq.0h2v.s11.2ddc2a54c92b from=translated src=- shape=f17f8656 vocab=ad690147
-/
theorem coe_hChar_apply (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ) :
    ((hChar q p : (GaloisField q 2)ˣ) : GaloisField q 2) =
      algebraMap (ZMod q) (GaloisField q 2) (p.1 : Matrix (Fin 2) (Fin 2) (ZMod q)).det *
        ((p.2 : (GaloisField q 2)ˣ) : GaloisField q 2) ^ (q + 1) := by
  simp [hChar, Matrix.GeneralLinearGroup.val_det_apply]

def hSubgroup : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ) := (hChar q).ker

/--
@isnad1 id=iff.0h2v.s11.50d7c6d51fc9 from=translated src=- shape=06f4d534 vocab=843c4b8c
-/
theorem mem_hSubgroup_iff (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ) :
    p ∈ hSubgroup q ↔ hChar q p = 1 :=
  MonoidHom.mem_ker

private theorem hFactor {p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ}
    (hp : p ∈ hSubgroup q) :
    ofZMod q k (p.1 : Matrix (Fin 2) (Fin 2) (ZMod q)).det * scalarOf q k p.2 ^ (q + 1) = 1 := by
  have h := congrArg (fun u : (GaloisField q 2)ˣ => algebraMap (GaloisField q 2) k u) ((mem_hSubgroup_iff q p).mp hp)
  simp only [coe_hChar_apply, Units.val_one, map_one, map_mul, map_pow] at h
  simpa [ofZMod, scalarOf] using h

private def hEnd (p : hSubgroup q) : CoordRing q k →ₐ[k] CoordRing q k :=
  Ideal.Quotient.liftₐ (drinfeldIdeal q k)
    ((mk q k).comp ((scalePoly k (scalarOf q k (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) ×
      (GaloisField q 2)ˣ).2)).comp (substPoly q k ((p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) ×
      (GaloisField q 2)ˣ).1 : Matrix (Fin 2) (Fin 2) (ZMod q)))))
    (by
      intro a ha
      rw [drinfeldIdeal, Ideal.mem_span_singleton'] at ha
      obtain ⟨b, rfl⟩ := ha
      rw [AlgHom.comp_apply, AlgHom.comp_apply, map_mul, map_sub, map_one, map_mul, map_sub, map_one,
        scalePoly_substPoly_drinfeldPoly, hFactor q k p.2, C_1, one_mul]
      exact mk_mul_drinfeldPoly_sub_one q k _)

private theorem hEnd_mk (p : hSubgroup q) (f : MvPolynomial (Fin 2) k) :
    hEnd q k p (mk q k f) =
      mk q k (scalePoly k (scalarOf q k (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2)
        (substPoly q k ((p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 :
          Matrix (Fin 2) (Fin 2) (ZMod q)) f)) :=
  rfl

private def hEndHom : hSubgroup q →* (CoordRing q k →ₐ[k] CoordRing q k) where
  toFun := hEnd q k
  map_one' := by
    apply algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp [hEnd_mk, scalarOf_one, scalePoly_one, substPoly_one]
  map_mul' p₁ p₂ := by
    apply algHom_ext
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, AlgHom.mul_apply, hEnd_mk]
    simp only [Subgroup.coe_mul, Prod.fst_mul, Prod.snd_mul, Units.val_mul, scalarOf_mul, substPoly_X, scalePoly_X,
      map_mul, map_add, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, Matrix.mul_apply, Fin.sum_univ_two]
    ring

def hAction : hSubgroup q →* (CoordRing q k ≃ₐ[k] CoordRing q k) :=
  (AlgEquiv.algHomUnitsEquiv k (CoordRing q k)).toMonoidHom.comp (hEndHom q k).toHomUnits

/--
@isnad1 id=eq.0h4v.s14.d97b832938a2 from=translated src=- shape=8fa669f9 vocab=efc39fed
-/
theorem hAction_mk (p : hSubgroup q) (f : MvPolynomial (Fin 2) k) :
    hAction q k p (mk q k f) =
      mk q k (scalePoly k (scalarOf q k (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2)
        (substPoly q k ((p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 :
          Matrix (Fin 2) (Fin 2) (ZMod q)) f)) :=
  hEnd_mk q k p f

/--
@isnad1 id=mem.0h2v.s10.02d85b9c69f0 from=translated src=- shape=008e5bda vocab=72752f2b
-/
theorem toGL_one_mem_hSubgroup (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) :
    (Matrix.SpecialLinearGroup.toGL g, (1 : (GaloisField q 2)ˣ)) ∈ hSubgroup q := by
  rw [mem_hSubgroup_iff, Units.ext_iff, coe_hChar_apply]
  simp [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]

/--
@isnad1 id=mem.0h2v.s11.2323a0fc7d81 from=translated src=- shape=9312ec94 vocab=18b76287
-/
theorem one_mem_hSubgroup_of_mem (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) :
    ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)), (ζ : (GaloisField q 2)ˣ)) ∈ hSubgroup q := by
  rw [mem_hSubgroup_iff, Units.ext_iff, coe_hChar_apply]
  have hζ := (mem_rootsOfUnity _ _).mp ζ.2
  simp [← Units.val_pow_eq_pow_val, hζ]

/--
@isnad1 id=eq.0h3v.s14.f5ab0c11df4f from=translated src=- shape=bc79fd58 vocab=4b4503cb
-/
theorem slAction_eq_hAction (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) :
    slAction q k g = hAction q k ⟨_, toGL_one_mem_hSubgroup q g⟩ := by
  ext z
  obtain ⟨f, rfl⟩ := mk_surjective q k z
  rw [slAction_mk, hAction_mk]
  simp [scalarOf_one, scalePoly_one, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]

/--
@isnad1 id=eq.0h3v.s14.95cf05d48413 from=translated src=- shape=9ad53d67 vocab=ba5affc8
-/
theorem muAction_eq_hAction (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) :
    muAction q k ζ = hAction q k ⟨_, one_mem_hSubgroup_of_mem q ζ⟩ := by
  ext z
  obtain ⟨f, rfl⟩ := mk_surjective q k z
  rw [muAction_mk, hAction_mk]
  simp [substPoly_one]

end Actions

end DrinfeldCurve

end
