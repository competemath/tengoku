import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittVectorHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Definitions/Def_Dieudonne_WittGroupHopf.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Function
open scoped TensorProduct

universe u v w

namespace Deformation


def WittGroup.Coord (R : Type u) [CommRing R] (p : ℕ) (n : ℕ) (J : Type v) : Type (max u v) :=
  MvPolynomial (J × Fin n) R

namespace WittGroup

variable (R : Type u) [CommRing R] (p : ℕ) (n : ℕ) (J : Type v)

noncomputable instance instCommRing : CommRing (Coord R p n J) :=
  inferInstanceAs (CommRing (MvPolynomial (J × Fin n) R))

noncomputable instance instAlgebra : Algebra R (Coord R p n J) :=
  inferInstanceAs (Algebra R (MvPolynomial (J × Fin n) R))

noncomputable instance instInhabited : Inhabited (Coord R p n J) := ⟨0⟩

variable {R p n J}

noncomputable def X (j : J) (i : Fin n) : Coord R p n J := (MvPolynomial.X (j, i) : MvPolynomial (J × Fin n) R)

noncomputable def lift {A : Type w} [CommSemiring A] [Algebra R A] (f : J → Fin n → A) :
    Coord R p n J →ₐ[R] A :=
  (MvPolynomial.aeval fun ji : J × Fin n => f ji.1 ji.2 : MvPolynomial (J × Fin n) R →ₐ[R] A)

/--
@isnad1 id=eq.0h8v.s7.7f7a46a470ba from=translated src=- shape=ecfd8106 vocab=66b71f9d
-/
@[simp] theorem lift_X {A : Type w} [CommSemiring A] [Algebra R A] (f : J → Fin n → A) (j : J)
    (i : Fin n) : lift f (X j i : Coord R p n J) = f j i :=
  MvPolynomial.aeval_X _ (j, i)

/--
@isnad1 id=eq.1h7v.s8.9a0b8ca2b661 from=translated src=- shape=99973879 vocab=127ffbcb
-/
theorem algHom_ext {A : Type w} [Semiring A] [Algebra R A] {f g : Coord R p n J →ₐ[R] A}
    (h : ∀ j i, f (X j i) = g (X j i)) : f = g :=
  MvPolynomial.algHom_ext (fun ji : J × Fin n => h ji.1 ji.2)

variable (R p n) in

noncomputable def univ (j : J) : TruncatedWittVector p n (Coord R p n J) :=
  TruncatedWittVector.mk p fun i => X j i

/--
@isnad1 id=eq.0h6v.s5.e9af3933436a from=translated src=- shape=b037cc19 vocab=ae4a262e
-/
@[simp] theorem coeff_univ (j : J) (i : Fin n) : (univ R p n j).coeff i = X j i :=
  TruncatedWittVector.coeff_mk _ _

variable [hp : Fact p.Prime]

section MapMk

variable {S : Type*} {T : Type*} [CommRing S] [CommRing T]

/--
@isnad1 id=eq.0h6v.s7.b55321392496 from=translated src=- shape=1382a045 vocab=d9dbbc16
-/
theorem map_mk (g : S →+* T) (f : Fin n → S) :
    TruncWitt.map (p := p) g (TruncatedWittVector.mk p f) = TruncatedWittVector.mk p fun i => g (f i) :=
  TruncatedWittVector.ext fun i => by
    rw [TruncWitt.coeff_map, TruncatedWittVector.coeff_mk, TruncatedWittVector.coeff_mk]

/--
@isnad1 id=eq.0h3v.s5.6e43b9d7a657 from=translated src=- shape=f09f7fdf vocab=12606a32
-/
theorem mk_zero_eq : (TruncatedWittVector.mk p fun _ : Fin n => (0 : S)) = 0 :=
  TruncatedWittVector.ext fun i => by
    rw [TruncatedWittVector.coeff_mk, TruncatedWittVector.coeff_zero]

end MapMk

section Rehom

variable {S : Type*} {B : Type*} [NonAssocSemiring S] [NonAssocSemiring B]

omit hp in

def rehom (g : S → B) (h1 : g 1 = 1) (hm : ∀ x y, g (x * y) = g x * g y) (h0 : g 0 = 0)
    (ha : ∀ x y, g (x + y) = g x + g y) : S →+* B :=
  ⟨⟨⟨g, h1⟩, hm⟩, h0, ha⟩

omit hp in
/--
@isnad1 id=eq.4h4v.s7.dadb9ba90174 from=translated src=- shape=22d6de78 vocab=3ec2769b
-/
@[simp] theorem rehom_apply (g : S → B) (h1 : g 1 = 1) (hm : ∀ x y, g (x * y) = g x * g y)
    (h0 : g 0 = 0) (ha : ∀ x y, g (x + y) = g x + g y) (x : S) : rehom g h1 hm h0 ha x = g x := rfl

end Rehom

/--
@isnad1 id=eq.0h7v.s8.96f65cd37f4f from=translated src=- shape=8891dd3b vocab=5ce334c1
-/
theorem map_univ {B : Type w} [CommRing B] (g : Coord R p n J →+* B) (j : J) :
    TruncWitt.map (p := p) g (univ R p n j) = TruncatedWittVector.mk p fun i => g (X j i) :=
  map_mk g _

variable (R p n J)

noncomputable def univLeft (j : J) : TruncatedWittVector p n (Coord R p n J ⊗[R] Coord R p n J) :=
  TruncatedWittVector.mk p fun i => X j i ⊗ₜ[R] (1 : Coord R p n J)

noncomputable def univRight (j : J) : TruncatedWittVector p n (Coord R p n J ⊗[R] Coord R p n J) :=
  TruncatedWittVector.mk p fun i => (1 : Coord R p n J) ⊗ₜ[R] X j i

noncomputable def comul : Coord R p n J →ₐ[R] Coord R p n J ⊗[R] Coord R p n J :=
  lift fun j i => (univLeft R p n J j + univRight R p n J j).coeff i

noncomputable def counit : Coord R p n J →ₐ[R] R :=
  lift fun _ _ => 0

noncomputable def antipode : Coord R p n J →ₐ[R] Coord R p n J :=
  lift fun j i => (-univ R p n j).coeff i

variable {R p n J}

/--
@isnad1 id=eq.0h6v.s10.85560ba62ca8 from=translated src=- shape=de41dd73 vocab=620b6acc
-/
@[simp] theorem comul_X (j : J) (i : Fin n) :
    comul R p n J (X j i) = (univLeft R p n J j + univRight R p n J j).coeff i :=
  lift_X _ j i

omit hp in
/--
@isnad1 id=eq.0h6v.s7.89572a1bb753 from=translated src=- shape=db49b4ee vocab=927d838f
-/
@[simp] theorem counit_X (j : J) (i : Fin n) : counit R p n J (X j i) = 0 :=
  lift_X _ j i

/--
@isnad1 id=eq.0h6v.s7.a6ed64765d17 from=translated src=- shape=fd6c2355 vocab=5520a47a
-/
@[simp] theorem antipode_X (j : J) (i : Fin n) :
    antipode R p n J (X j i) = (-univ R p n j).coeff i :=
  lift_X _ j i

/--
@isnad1 id=eq.0h8v.s12.b0bc72fa262b from=translated src=- shape=18c79159 vocab=af43a245
-/
theorem ringHom_comul_X {B : Type w} [CommRing B] (g : Coord R p n J ⊗[R] Coord R p n J →+* B)
    (j : J) (i : Fin n) :
    g (comul R p n J (X j i)) =
      ((TruncatedWittVector.mk p fun i => g (X j i ⊗ₜ[R] (1 : Coord R p n J))) +
        (TruncatedWittVector.mk p fun i => g ((1 : Coord R p n J) ⊗ₜ[R] X j i))).coeff i := by
  rw [comul_X, ← TruncWitt.coeff_map (p := p) g, map_add, univLeft, univRight, map_mk, map_mk]

/--
@isnad1 id=eq.0h7v.s12.f3ccde15fbc0 from=translated src=- shape=b34b2b94 vocab=60089f34
-/
theorem mk_ringHom_comul {B : Type w} [CommRing B] (g : Coord R p n J ⊗[R] Coord R p n J →+* B)
    (j : J) :
    (TruncatedWittVector.mk p fun i => g (comul R p n J (X j i))) =
      (TruncatedWittVector.mk p fun i => g (X j i ⊗ₜ[R] (1 : Coord R p n J))) +
        (TruncatedWittVector.mk p fun i => g ((1 : Coord R p n J) ⊗ₜ[R] X j i)) :=
  TruncatedWittVector.ext fun i => by rw [TruncatedWittVector.coeff_mk, ringHom_comul_X]

/--
@isnad1 id=eq.0h8v.s8.90e22764ea76 from=translated src=- shape=896f265e vocab=aa49511f
-/
theorem ringHom_antipode_X {B : Type w} [CommRing B] (g : Coord R p n J →+* B) (j : J) (i : Fin n) :
    g (antipode R p n J (X j i)) = (-(TruncatedWittVector.mk p fun i => g (X j i))).coeff i := by
  rw [antipode_X, ← TruncWitt.coeff_map (p := p) g, map_neg, map_univ]

/--
@isnad1 id=eq.0h7v.s8.0124bf919140 from=translated src=- shape=892a61d8 vocab=d442594a
-/
theorem mk_ringHom_antipode {B : Type w} [CommRing B] (g : Coord R p n J →+* B) (j : J) :
    (TruncatedWittVector.mk p fun i => g (antipode R p n J (X j i))) =
      -(TruncatedWittVector.mk p fun i => g (X j i)) :=
  TruncatedWittVector.ext fun i => by rw [TruncatedWittVector.coeff_mk, ringHom_antipode_X]

section Axioms

variable (R p n J)

local notation "𝒪" => Coord R p n J
local notation "T" => Coord R p n J ⊗[R] (Coord R p n J ⊗[R] Coord R p n J)

/--
@isnad1 id=eq.0h4v.s13.e17f34c9c880 from=translated src=- shape=67756048 vocab=86a4a592
-/
theorem comul_coassoc :
    (Algebra.TensorProduct.assoc R R R 𝒪 𝒪 𝒪).toAlgHom.comp
        ((Algebra.TensorProduct.map (comul R p n J) (AlgHom.id R 𝒪)).comp (comul R p n J)) =
      (Algebra.TensorProduct.map (AlgHom.id R 𝒪) (comul R p n J)).comp (comul R p n J) := by
  refine algHom_ext fun j i => ?_

  set a : TruncatedWittVector p n T :=
    TruncatedWittVector.mk p fun i => X j i ⊗ₜ[R] ((1 : 𝒪) ⊗ₜ[R] (1 : 𝒪)) with ha
  set b : TruncatedWittVector p n T :=
    TruncatedWittVector.mk p fun i => (1 : 𝒪) ⊗ₜ[R] (X j i ⊗ₜ[R] (1 : 𝒪)) with hb
  set c : TruncatedWittVector p n T :=
    TruncatedWittVector.mk p fun i => (1 : 𝒪) ⊗ₜ[R] ((1 : 𝒪) ⊗ₜ[R] X j i) with hc

  let FL : 𝒪 ⊗[R] 𝒪 →ₐ[R] T :=
    (Algebra.TensorProduct.assoc R R R 𝒪 𝒪 𝒪).toAlgHom.comp
      (Algebra.TensorProduct.map (comul R p n J) (AlgHom.id R 𝒪))
  let FR : 𝒪 ⊗[R] 𝒪 →ₐ[R] T := Algebra.TensorProduct.map (AlgHom.id R 𝒪) (comul R p n J)
  let KL : 𝒪 ⊗[R] 𝒪 →ₐ[R] T :=
    (Algebra.TensorProduct.assoc R R R 𝒪 𝒪 𝒪).toAlgHom.comp
      (Algebra.TensorProduct.includeLeft : 𝒪 ⊗[R] 𝒪 →ₐ[R] (𝒪 ⊗[R] 𝒪) ⊗[R] 𝒪)
  let KR : 𝒪 ⊗[R] 𝒪 →ₐ[R] T :=
    (Algebra.TensorProduct.includeRight : 𝒪 ⊗[R] 𝒪 →ₐ[R] 𝒪 ⊗[R] (𝒪 ⊗[R] 𝒪))

  have eL := ringHom_comul_X (p := p) (rehom FL FL.map_one FL.map_mul FL.map_zero FL.map_add) j i
  have eR := ringHom_comul_X (p := p) (rehom FR FR.map_one FR.map_mul FR.map_zero FR.map_add) j i
  have fL := mk_ringHom_comul (p := p) (rehom KL KL.map_one KL.map_mul KL.map_zero KL.map_add) j
  have fR := mk_ringHom_comul (p := p) (rehom KR KR.map_one KR.map_mul KR.map_zero KR.map_add) j
  simp only [rehom_apply] at eL eR fL fR
  have hassoc : ∀ x y z : 𝒪, (Algebra.TensorProduct.assoc R R R 𝒪 𝒪 𝒪) ((x ⊗ₜ[R] y) ⊗ₜ[R] z) =
      x ⊗ₜ[R] (y ⊗ₜ[R] z) := fun x y z => Algebra.TensorProduct.assoc_tmul R R 𝒪 x y z

  have hFL1 : (TruncatedWittVector.mk p fun i => FL (X j i ⊗ₜ[R] (1 : 𝒪))) = a + b := by
    have hg : (TruncatedWittVector.mk p fun i => FL (X j i ⊗ₜ[R] (1 : 𝒪))) =
        TruncatedWittVector.mk p fun i => KL (comul R p n J (X j i)) := by
      refine congrArg _ (funext fun i => ?_)
      change (Algebra.TensorProduct.assoc R R R 𝒪 𝒪 𝒪)
        (Algebra.TensorProduct.map (comul R p n J) (AlgHom.id R 𝒪) (X j i ⊗ₜ[R] (1 : 𝒪))) =
        (Algebra.TensorProduct.assoc R R R 𝒪 𝒪 𝒪) (comul R p n J (X j i) ⊗ₜ[R] (1 : 𝒪))
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [hg, fL, ha, hb]
    congr 1
  have hFL2 : (TruncatedWittVector.mk p fun i => FL ((1 : 𝒪) ⊗ₜ[R] X j i)) = c := by
    rw [hc]
    refine congrArg _ (funext fun i => ?_)
    change (Algebra.TensorProduct.assoc R R R 𝒪 𝒪 𝒪)
      (Algebra.TensorProduct.map (comul R p n J) (AlgHom.id R 𝒪) ((1 : 𝒪) ⊗ₜ[R] X j i)) = _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, Algebra.TensorProduct.one_def]
    exact hassoc _ _ _
  have hFR1 : (TruncatedWittVector.mk p fun i => FR (X j i ⊗ₜ[R] (1 : 𝒪))) = a := by
    rw [ha]
    refine congrArg _ (funext fun i => ?_)
    change Algebra.TensorProduct.map (AlgHom.id R 𝒪) (comul R p n J) (X j i ⊗ₜ[R] (1 : 𝒪)) = _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, Algebra.TensorProduct.one_def]
  have hFR2 : (TruncatedWittVector.mk p fun i => FR ((1 : 𝒪) ⊗ₜ[R] X j i)) = b + c := by
    have hg : (TruncatedWittVector.mk p fun i => FR ((1 : 𝒪) ⊗ₜ[R] X j i)) =
        TruncatedWittVector.mk p fun i => KR (comul R p n J (X j i)) := by
      refine congrArg _ (funext fun i => ?_)
      change Algebra.TensorProduct.map (AlgHom.id R 𝒪) (comul R p n J) ((1 : 𝒪) ⊗ₜ[R] X j i) = _
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rfl
    rw [hg, fR, hb, hc]
    rfl
  have hL : ((Algebra.TensorProduct.assoc R R R 𝒪 𝒪 𝒪).toAlgHom.comp
      ((Algebra.TensorProduct.map (comul R p n J) (AlgHom.id R 𝒪)).comp (comul R p n J))) (X j i) =
      FL (comul R p n J (X j i)) := rfl
  have hR : ((Algebra.TensorProduct.map (AlgHom.id R 𝒪) (comul R p n J)).comp (comul R p n J)) (X j i) =
      FR (comul R p n J (X j i)) := rfl
  rw [hL, hR, eL, eR, hFL1, hFL2, hFR1, hFR2]
  exact congrArg (TruncatedWittVector.coeff i) (add_assoc a b c)

/--
@isnad1 id=eq.0h4v.s10.d219c248c2a2 from=translated src=- shape=0cb93123 vocab=1afe9215
-/
theorem comul_rTensor_counit :
    (Algebra.TensorProduct.map (counit R p n J) (AlgHom.id R 𝒪)).comp (comul R p n J) =
      (Algebra.TensorProduct.lid R 𝒪).symm := by
  refine algHom_ext fun j i => ?_
  let g : 𝒪 ⊗[R] 𝒪 →+* R ⊗[R] 𝒪 := (Algebra.TensorProduct.map (counit R p n J) (AlgHom.id R 𝒪)).toRingHom
  have h := ringHom_comul_X (p := p) g j i
  have hg1 : ∀ i, g (X j i ⊗ₜ[R] (1 : 𝒪)) = 0 := by
    intro i
    change Algebra.TensorProduct.map (counit R p n J) (AlgHom.id R 𝒪) (X j i ⊗ₜ[R] (1 : 𝒪)) = 0
    rw [Algebra.TensorProduct.map_tmul, counit_X, TensorProduct.zero_tmul]
  have hg2 : ∀ i, g ((1 : 𝒪) ⊗ₜ[R] X j i) = (1 : R) ⊗ₜ[R] X j i := by
    intro i
    change Algebra.TensorProduct.map (counit R p n J) (AlgHom.id R 𝒪) ((1 : 𝒪) ⊗ₜ[R] X j i) = _
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  simp only [hg1, hg2] at h
  change g (comul R p n J (X j i)) = (Algebra.TensorProduct.lid R 𝒪).symm (X j i)
  rw [h, mk_zero_eq, zero_add, TruncatedWittVector.coeff_mk]
  rfl

/--
@isnad1 id=eq.0h4v.s10.20eedb7b3fb8 from=translated src=- shape=57c4956d vocab=6306fb50
-/
theorem comul_lTensor_counit :
    (Algebra.TensorProduct.map (AlgHom.id R 𝒪) (counit R p n J)).comp (comul R p n J) =
      (Algebra.TensorProduct.rid R R 𝒪).symm := by
  refine algHom_ext fun j i => ?_
  let g : 𝒪 ⊗[R] 𝒪 →+* 𝒪 ⊗[R] R := (Algebra.TensorProduct.map (AlgHom.id R 𝒪) (counit R p n J)).toRingHom
  have h := ringHom_comul_X (p := p) g j i
  have hg1 : ∀ i, g (X j i ⊗ₜ[R] (1 : 𝒪)) = X j i ⊗ₜ[R] (1 : R) := by
    intro i
    change Algebra.TensorProduct.map (AlgHom.id R 𝒪) (counit R p n J) (X j i ⊗ₜ[R] (1 : 𝒪)) = _
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  have hg2 : ∀ i, g ((1 : 𝒪) ⊗ₜ[R] X j i) = 0 := by
    intro i
    change Algebra.TensorProduct.map (AlgHom.id R 𝒪) (counit R p n J) ((1 : 𝒪) ⊗ₜ[R] X j i) = 0
    rw [Algebra.TensorProduct.map_tmul, counit_X, TensorProduct.tmul_zero]
  simp only [hg1, hg2] at h
  change g (comul R p n J (X j i)) = (Algebra.TensorProduct.rid R R 𝒪).symm (X j i)
  rw [h, mk_zero_eq, add_zero, TruncatedWittVector.coeff_mk]
  rfl

end Axioms

variable (R p n J)

noncomputable instance instBialgebra : Bialgebra R (Coord R p n J) :=
  Bialgebra.ofAlgHom (comul R p n J) (counit R p n J) (comul_coassoc R p n J)
    (comul_rTensor_counit R p n J) (comul_lTensor_counit R p n J)

/--
@isnad1 id=eq.0h4v.s9.4f2e42cd16d5 from=translated src=- shape=6b4372c4 vocab=2bedf49a
-/
theorem comulAlgHom_eq : Bialgebra.comulAlgHom R (Coord R p n J) = comul R p n J :=
  AlgHom.ext fun _ => rfl

/--
@isnad1 id=eq.0h4v.s7.e7bba32ed009 from=translated src=- shape=d34f5e2c vocab=5d6f10b3
-/
theorem counitAlgHom_eq : Bialgebra.counitAlgHom R (Coord R p n J) = counit R p n J :=
  AlgHom.ext fun _ => rfl

/--
@isnad1 id=eq.0h5v.s11.532821fa944e from=translated src=- shape=c7c0b015 vocab=1728bca8
-/
theorem comul_def (x : Coord R p n J) : Coalgebra.comul (R := R) x = comul R p n J x := rfl

/--
@isnad1 id=eq.0h5v.s9.93efaef0ed79 from=translated src=- shape=3c298ccf vocab=34b92269
-/
theorem counit_def (x : Coord R p n J) : Coalgebra.counit (R := R) x = counit R p n J x := rfl

/--
@isnad1 id=eq.0h4v.s9.1ffc08010ed6 from=translated src=- shape=bf43df23 vocab=acc4dac2
-/
theorem antipode_rTensor_comul :
    (Algebra.TensorProduct.lift (antipode R p n J) (AlgHom.id R (Coord R p n J))
        (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom R (Coord R p n J)) =
      (Algebra.ofId R (Coord R p n J)).comp (Bialgebra.counitAlgHom R (Coord R p n J)) := by
  rw [comulAlgHom_eq, counitAlgHom_eq]
  refine algHom_ext fun j i => ?_
  let g : Coord R p n J ⊗[R] Coord R p n J →+* Coord R p n J :=
    (Algebra.TensorProduct.lift (antipode R p n J) (AlgHom.id R (Coord R p n J))
      (fun _ _ => Commute.all _ _)).toRingHom
  have h := ringHom_comul_X (p := p) g j i
  have hg1 : ∀ i, g (X j i ⊗ₜ[R] (1 : Coord R p n J)) = antipode R p n J (X j i) := by
    intro i
    change Algebra.TensorProduct.lift (antipode R p n J) (AlgHom.id R (Coord R p n J)) _
      (X j i ⊗ₜ[R] (1 : Coord R p n J)) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  have hg2 : ∀ i, g ((1 : Coord R p n J) ⊗ₜ[R] X j i) = X j i := by
    intro i
    change Algebra.TensorProduct.lift (antipode R p n J) (AlgHom.id R (Coord R p n J)) _
      ((1 : Coord R p n J) ⊗ₜ[R] X j i) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.id_apply]
  simp only [hg1, hg2] at h
  change g (comul R p n J (X j i)) = algebraMap R (Coord R p n J) (counit R p n J (X j i))
  rw [h, counit_X, map_zero]
  have hS : (TruncatedWittVector.mk p fun i => antipode R p n J (X j i)) = -univ R p n j := by
    have := mk_ringHom_antipode (p := p) (RingHom.id (Coord R p n J)) j
    simp only [RingHom.id_apply] at this
    exact this
  have hU : (TruncatedWittVector.mk p fun i => (X j i : Coord R p n J)) = univ R p n j := rfl
  rw [hS, hU, neg_add_cancel, TruncatedWittVector.coeff_zero]

/--
@isnad1 id=eq.0h4v.s9.3bfd519b4a90 from=translated src=- shape=d7196e61 vocab=acc4dac2
-/
theorem antipode_lTensor_comul :
    (Algebra.TensorProduct.lift (AlgHom.id R (Coord R p n J)) (antipode R p n J)
        (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom R (Coord R p n J)) =
      (Algebra.ofId R (Coord R p n J)).comp (Bialgebra.counitAlgHom R (Coord R p n J)) := by
  rw [comulAlgHom_eq, counitAlgHom_eq]
  refine algHom_ext fun j i => ?_
  let g : Coord R p n J ⊗[R] Coord R p n J →+* Coord R p n J :=
    (Algebra.TensorProduct.lift (AlgHom.id R (Coord R p n J)) (antipode R p n J)
      (fun _ _ => Commute.all _ _)).toRingHom
  have h := ringHom_comul_X (p := p) g j i
  have hg1 : ∀ i, g (X j i ⊗ₜ[R] (1 : Coord R p n J)) = X j i := by
    intro i
    change Algebra.TensorProduct.lift (AlgHom.id R (Coord R p n J)) (antipode R p n J) _
      (X j i ⊗ₜ[R] (1 : Coord R p n J)) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one, AlgHom.id_apply]
  have hg2 : ∀ i, g ((1 : Coord R p n J) ⊗ₜ[R] X j i) = antipode R p n J (X j i) := by
    intro i
    change Algebra.TensorProduct.lift (AlgHom.id R (Coord R p n J)) (antipode R p n J) _
      ((1 : Coord R p n J) ⊗ₜ[R] X j i) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  simp only [hg1, hg2] at h
  change g (comul R p n J (X j i)) = algebraMap R (Coord R p n J) (counit R p n J (X j i))
  rw [h, counit_X, map_zero]
  have hS : (TruncatedWittVector.mk p fun i => antipode R p n J (X j i)) = -univ R p n j := by
    have := mk_ringHom_antipode (p := p) (RingHom.id (Coord R p n J)) j
    simp only [RingHom.id_apply] at this
    exact this
  have hU : (TruncatedWittVector.mk p fun i => (X j i : Coord R p n J)) = univ R p n j := rfl
  rw [hS, hU, add_neg_cancel, TruncatedWittVector.coeff_zero]

noncomputable instance instHopfAlgebra : HopfAlgebra R (Coord R p n J) :=
  HopfAlgebra.ofAlgHom (antipode R p n J) (antipode_rTensor_comul R p n J) (antipode_lTensor_comul R p n J)

/--
@isnad1 id=eq.0h5v.s9.7e29c561feea from=translated src=- shape=7fc1fc40 vocab=b687877a
-/
theorem antipode_def (x : Coord R p n J) : HopfAlgebra.antipode R x = antipode R p n J x := rfl

/--
@isnad1 id=iscocomm.0h4v.s7.598d629194de from=translated src=- shape=226c6dcc vocab=4b43237d
-/
instance instIsCocomm : Coalgebra.IsCocomm R (Coord R p n J) := by
  refine ⟨?_⟩
  have h : (Algebra.TensorProduct.comm R (Coord R p n J) (Coord R p n J)).toAlgHom.comp (comul R p n J) =
      comul R p n J := by
    refine algHom_ext fun j i => ?_
    let g : Coord R p n J ⊗[R] Coord R p n J →+* Coord R p n J ⊗[R] Coord R p n J :=
      (Algebra.TensorProduct.comm R (Coord R p n J) (Coord R p n J)).toAlgHom.toRingHom
    change g (comul R p n J (X j i)) = comul R p n J (X j i)
    rw [ringHom_comul_X, comul_X, add_comm]
    rfl
  refine LinearMap.ext fun x => ?_
  exact AlgHom.congr_fun h x

variable {R p n J}

section Points

variable {A : Type w} [CommRing A] [Algebra R A]

noncomputable def pointsEquiv : (Coord R p n J →ₐ[R] A) ≃ (J → TruncatedWittVector p n A) where
  toFun φ j := TruncatedWittVector.mk p fun i => φ (X j i)
  invFun x := lift fun j i => (x j).coeff i
  left_inv φ := algHom_ext fun j i => by rw [lift_X, TruncatedWittVector.coeff_mk]
  right_inv x := funext fun j => TruncatedWittVector.ext fun i => by
    rw [TruncatedWittVector.coeff_mk, lift_X]

omit hp in
/--
@isnad1 id=eq.0h7v.s8.c9f0951d02a8 from=translated src=- shape=a6f41a65 vocab=7a309ddd
-/
theorem pointsEquiv_apply (φ : Coord R p n J →ₐ[R] A) (j : J) :
    pointsEquiv φ j = TruncatedWittVector.mk p fun i => φ (X j i) := rfl

omit hp in
/--
@isnad1 id=eq.0h8v.s8.8e13f9ee3511 from=translated src=- shape=5865dab1 vocab=ed5f2c74
-/
theorem coeff_pointsEquiv (φ : Coord R p n J →ₐ[R] A) (j : J) (i : Fin n) :
    (pointsEquiv φ j).coeff i = φ (X j i) := TruncatedWittVector.coeff_mk _ _

/--
@isnad1 id=eq.0h7v.s9.55d8348c136d from=translated src=- shape=146c1833 vocab=b2b966d3
-/
theorem pointsEquiv_eq_map_univ (φ : Coord R p n J →ₐ[R] A) (j : J) :
    pointsEquiv φ j = TruncWitt.map (p := p) φ.toRingHom (univ R p n j) := (map_univ φ.toRingHom j).symm

omit hp in
/--
@isnad1 id=eq.0h8v.s8.443fbbd2cd1e from=translated src=- shape=59979cc3 vocab=dda1188b
-/
@[simp] theorem pointsEquiv_symm_apply_X (x : J → TruncatedWittVector p n A) (j : J) (i : Fin n) :
    pointsEquiv.symm x (X j i : Coord R p n J) = (x j).coeff i := lift_X _ j i

/--
@isnad1 id=eq.0h7v.s10.1966b892c20a from=translated src=- shape=57ca5974 vocab=8e17f807
-/
theorem pointsEquiv_mul (φ ψ : WithConv (Coord R p n J →ₐ[R] A)) :
    pointsEquiv (φ * ψ).ofConv = pointsEquiv φ.ofConv + pointsEquiv ψ.ofConv := by
  funext j
  rw [Pi.add_apply, pointsEquiv_apply, pointsEquiv_apply, pointsEquiv_apply]
  have key : ∀ i, (φ * ψ).ofConv (X j i) =
      (Algebra.TensorProduct.lift φ.ofConv ψ.ofConv (fun _ _ => Commute.all _ _)).toRingHom
        (comul R p n J (X j i)) := by
    intro i
    rw [AlgHom.convMul_apply, comul_def]
    rfl
  simp only [key]
  rw [mk_ringHom_comul]
  congr 1
  · refine congrArg _ (funext fun i => ?_)
    change Algebra.TensorProduct.lift φ.ofConv ψ.ofConv _ (X j i ⊗ₜ[R] (1 : Coord R p n J)) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  · refine congrArg _ (funext fun i => ?_)
    change Algebra.TensorProduct.lift φ.ofConv ψ.ofConv _ ((1 : Coord R p n J) ⊗ₜ[R] X j i) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]

/--
@isnad1 id=eq.0h5v.s9.d84d0e364ab1 from=translated src=- shape=4b03db82 vocab=db76fc71
-/
theorem pointsEquiv_one : pointsEquiv (1 : WithConv (Coord R p n J →ₐ[R] A)).ofConv = 0 := by
  funext j
  rw [Pi.zero_apply, pointsEquiv_apply]
  refine TruncatedWittVector.ext fun i => ?_
  rw [TruncatedWittVector.coeff_mk, TruncatedWittVector.coeff_zero, AlgHom.convOne_apply, counit_def,
    counit_X, map_zero]

/--
@isnad1 id=eq.0h6v.s9.1523f53e890d from=translated src=- shape=fc445167 vocab=b130c0f5
-/
theorem pointsEquiv_comp_antipode (φ : Coord R p n J →ₐ[R] A) :
    pointsEquiv (φ.comp (antipode R p n J)) = -pointsEquiv φ := by
  funext j
  rw [Pi.neg_apply, pointsEquiv_apply, pointsEquiv_apply]
  exact mk_ringHom_antipode φ.toRingHom j

end Points

/--
@isnad1 id=mem.0h5v.s7.63a10e14fd1c from=translated src=- shape=cec34dec vocab=14380bd5
-/
theorem univ_mem_wittHom (j : J) : univ R p n j ∈ wittHom R p n (Coord R p n J) := by
  rw [mem_wittHom_iff]
  have hΔ : (comulRingHom R (Coord R p n J) : Coord R p n J →+* Coord R p n J ⊗[R] Coord R p n J) =
      (comul R p n J).toRingHom := RingHom.ext fun x => rfl
  rw [hΔ, map_univ, map_univ, map_univ]
  refine TruncatedWittVector.ext fun i => ?_
  rw [TruncatedWittVector.coeff_mk]
  exact comul_X j i

noncomputable def univHom (j : J) : wittHom R p n (Coord R p n J) := ⟨univ R p n j, univ_mem_wittHom j⟩

/--
@isnad1 id=eq.0h5v.s8.dbc082711c2e from=translated src=- shape=9761c8c7 vocab=944804a5
-/
@[simp] theorem coe_univHom (j : J) : (univHom (R := R) (p := p) (n := n) j : TruncatedWittVector p n (Coord R p n J)) =
    univ R p n j := rfl

omit hp in

/--
@isnad1 id=ne.0h6v.s6.c43c9f4275a9 from=translated src=- shape=744d31f9 vocab=01d9ed61
-/
theorem X_ne_zero [Nontrivial R] (j : J) (i : Fin n) : (X j i : Coord R p n J) ≠ 0 :=
  MvPolynomial.X_ne_zero (R := R) (j, i)

end WittGroup

end Deformation
