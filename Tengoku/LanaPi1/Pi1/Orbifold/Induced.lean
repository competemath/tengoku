module

public import Tengoku.LanaPi1.Pi1.Orbifold.GaloisAction
public import Tengoku.LanaPi1.Pi1.Orbifold.EtaleOfAlgebra
public import Tengoku.LanaPi1.Pi1.Orbicurve.EtaleInertia

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Induced covers

Let `D : GaloisData k t` and let `U ⊴ H` be an open normal subgroup contained in `H_L`
(a `GaloisData.Level`), with fixed field `L_U ⊇ L` and coordinate ring `R_U`. The group `H` acts
on `R_U`. The **induced algebra** `Ind = (A → R_U)` (the algebra of `H_L`-equivariant functions
`H/U → R_U`, trivialized by a section `sec : A → H`) carries the semilinear action

  `(a • φ)(b) = (sec b · sec(a⁻¹ b)⁻¹) • φ(a⁻¹ b)`

of `A = H ⧸ H_L`. When every inertia element of `S` lies in `U`, `R_U` is étale over `R` (the
étale criterion `AffOrbicurve.etale_iff_inertia`), so `Ind` is finite étale over `R` and defines
an object `V.X` of `EquivEtale R A`, the cover of `[Spec R / A]` corresponding to the `H`-set
`H/U`. It has a distinguished fibre element `V.f₀` (evaluation at `1`), with
`σ • f₀ = f₀ ↔ σ ∈ U` (`GaloisData.Level.mem_U_of_fibreSmul_f₀`).
-/

@[expose] public section
namespace Tengoku.LanaPi1 end Tengoku.LanaPi1 open Tengoku.LanaPi1 
universe u

open CategoryTheory Tengoku.LanaPi1.AffOrbicurve IntermediateField.algebraAdjoinAdjoin

namespace Pi1.Orbifold

noncomputable section

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

namespace GaloisData

variable (D : GaloisData k t)

/-- **A level** of `D`: an open normal subgroup `U` of `H` contained in `H_L` and containing the
inertia elements `S`.-/
structure Level where
  /-- The subgroup.-/
  U : Subgroup D.H
  /-- `U` is normal in `H`.-/
  normal : U.Normal
  /-- `U` is open.-/
  isOpen : IsOpen (U : Set D.H)
  /-- `U ≤ H_L`.-/
  le : U ≤ D.HL.subgroupOf D.H
  /-- `U` contains the inertia elements.-/
  S_le : ∀ σ : D.H, (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ D.S → σ ∈ U

namespace Level

variable {D} (V : D.Level)

/-- The subgroup `U` as a subgroup of `Gal`.-/
def Ug : Subgroup (Ω ≃ₐ[K₀ k t] Ω) := V.U.map D.H.subtype

/--
@isnad1 id=iff.0h6v.s13.5171f7d1bcae from=translated src=- shape=9ce3cd8c vocab=8ae47ff0
-/
lemma mem_Ug {σ : D.H} : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ V.Ug ↔ σ ∈ V.U :=
  Subgroup.mem_map_iff_mem (Subgroup.subtype_injective _)

/--
@isnad1 id=le.0h5v.s9.670829c5c561 from=translated src=- shape=8313d55e vocab=92767244
-/
lemma Ug_le : V.Ug ≤ D.HL := by
  rintro _ ⟨σ, hσ, rfl⟩
  exact (Subgroup.mem_subgroupOf).1 (V.le hσ)

/--
@isnad1 id=isopen.0h5v.s9.abca0f2b5416 from=translated src=- shape=d9a2cfb4 vocab=8c9dcdb6
-/
lemma isOpen_Ug : IsOpen (V.Ug : Set (Ω ≃ₐ[K₀ k t] Ω)) := by
  simp only [Ug, Subgroup.coe_map, Subgroup.coe_subtype]
  exact D.isOpen_H.isOpenMap_subtype_val _ V.isOpen

/--
@isnad1 id=isclosed.0h5v.s9.e9d31e825482 from=translated src=- shape=d9a2cfb4 vocab=299acadf
-/
lemma isClosed_Ug : IsClosed (V.Ug : Set (Ω ≃ₐ[K₀ k t] Ω)) :=
  Subgroup.isClosed_of_isOpen _ V.isOpen_Ug

/-- The fixed field `L_U` of `U`.-/
def LU : IntermediateField (K₀ k t) Ω := IntermediateField.fixedField V.Ug

/--
@isnad1 id=le.0h5v.s8.2fb542076961 from=translated src=- shape=c651ac63 vocab=06b8c2f3
-/
lemma L_le : D.L ≤ V.LU := IntermediateField.fixedField_le V.Ug_le

/--
@isnad1 id=mem.2h7v.s10.244c70d88bbb from=translated src=- shape=f66d0fd0 vocab=6234f3a8
-/
lemma stable : ∀ g ∈ D.H, ∀ x ∈ V.LU, g x ∈ V.LU := by
  refine mem_fixedField_of_normalizes fun g hg u hu => ?_
  obtain ⟨u, hu, rfl⟩ := hu
  have := V.normal.conj_mem u hu ⟨g, hg⟩⁻¹
  exact ⟨_, this, by simp⟩

/-- The coordinate ring `R_U` of `L_U`.-/
abbrev RU : Type u := CoordRing k t V.LU

instance : Algebra D.R V.RU := CoordRing.algOfLE V.L_le

instance : IsScalarTower D.R V.RU Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The action of `H` on `R_U`.-/
def actU : D.H →* RingAut V.RU := coordAut V.LU D.H V.stable

/--
@isnad1 id=eq.0h7v.s14.f5ca294b4154 from=translated src=- shape=15dad082 vocab=6202b676
-/
lemma algebraMap_actU (g : D.H) (x : V.RU) :
    algebraMap V.RU Ω (V.actU g x) = (g : Ω ≃ₐ[K₀ k t] Ω) (algebraMap V.RU Ω x) := rfl

/--
@isnad1 id=eq.0h8v.s15.0ee7bd565a6f from=translated src=- shape=c9243cf9 vocab=6a470b20
-/
lemma actU_apply_actU (g h : D.H) (x : V.RU) : V.actU g (V.actU h x) = V.actU (g * h) x := by
  rw [map_mul]; rfl

/-- **The induced algebra** `A → R_U`.-/
def Ind : Type u := D.A → V.RU

instance : CommRing V.Ind := inferInstanceAs (CommRing (D.A → V.RU))

instance : Algebra D.R V.Ind := inferInstanceAs (Algebra D.R (D.A → V.RU))

/--
@isnad1 id=eq.0h7v.s9.5c38b56ce0cd from=translated src=- shape=2f60aaa0 vocab=be2fc1a4
-/
lemma algebraMap_Ind_apply (r : D.R) (b : D.A) :
    (algebraMap D.R V.Ind r : D.A → V.RU) b = algebraMap D.R V.RU r := rfl

/-- The action of `A` on the induced algebra.-/
def indSmul (a : D.A) (φ : V.Ind) : V.Ind :=
  fun b => V.actU (D.sec b * (D.sec (a⁻¹ * b))⁻¹) ((φ : D.A → V.RU) (a⁻¹ * b))

/--
@isnad1 id=eq.0h8v.s14.3b0fa731c686 from=translated src=- shape=7cf8e30f vocab=faff7971
-/
lemma indSmul_apply (a : D.A) (φ : V.Ind) (b : D.A) :
    (V.indSmul a φ : D.A → V.RU) b =
      V.actU (D.sec b * (D.sec (a⁻¹ * b))⁻¹) ((φ : D.A → V.RU) (a⁻¹ * b)) := rfl

/--
@isnad1 id=eq.0h6v.s10.4df26628c3fd from=translated src=- shape=4ee1ad6c vocab=37f05f19
-/
lemma indSmul_one (φ : V.Ind) : V.indSmul 1 φ = φ := by
  funext b
  simp [indSmul_apply]

/--
@isnad1 id=eq.0h8v.s10.dc3c0d538699 from=translated src=- shape=59051393 vocab=4c0379c1
-/
lemma indSmul_mul (a a' : D.A) (φ : V.Ind) :
    V.indSmul (a * a') φ = V.indSmul a (V.indSmul a' φ) := by
  funext b
  simp only [indSmul_apply, actU_apply_actU, mul_inv_rev, mul_assoc]
  congr 2
  group

/-- The action of `a ∈ A` on the induced algebra, as a ring automorphism.-/
def indAut (a : D.A) : V.Ind ≃+* V.Ind where
  toFun := V.indSmul a
  invFun := V.indSmul a⁻¹
  left_inv φ := by rw [← indSmul_mul, inv_mul_cancel, indSmul_one]
  right_inv φ := by rw [← indSmul_mul, mul_inv_cancel, indSmul_one]
  map_mul' φ ψ := funext fun b => map_mul (V.actU _) _ _
  map_add' φ ψ := funext fun b => map_add (V.actU _) _ _

/--
@isnad1 id=eq.0h7v.s9.adb4021fbe74 from=translated src=- shape=0e56dae2 vocab=19cbfed0
-/
lemma indAut_apply (a : D.A) (φ : V.Ind) : V.indAut a φ = V.indSmul a φ := rfl

/-- The lift `A →* SemilinearAut R A Ind` of the action of `A`.-/
def ρ : D.A →* SemilinearAut D.R D.A V.Ind where
  toFun a := ⟨a, V.indAut a, fun r => by
    funext b
    refine CoordRing.ext ?_
    rw [indAut_apply, indSmul_apply, algebraMap_actU, algebraMap_Ind_apply,
      algebraMap_Ind_apply]
    conv_rhs => rw [← D.mk_sec_mul_sec_inv a b]
    rfl⟩
  map_one' := SemilinearAut.ext rfl (RingEquiv.ext fun φ => V.indSmul_one φ)
  map_mul' a a' := SemilinearAut.ext rfl (RingEquiv.ext fun φ => V.indSmul_mul a a' φ)

/-- Evaluation at `1`: the distinguished fibre element of the induced algebra.-/
def ev : V.Ind →ₐ[D.R] Ω :=
  (IsScalarTower.toAlgHom D.R V.RU Ω).comp (Pi.evalAlgHom D.R (fun _ : D.A => V.RU) 1)

section Etale

variable [IsGalois (K₀ k t) Ω]

variable [CharZero k]

end Etale

end Level

end GaloisData

end

end Pi1.Orbifold
-- Tengoku: root names of this library moved to Tengoku.LanaPi1 so they do not collide with other libraries (generated)
