import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped DualNumber RightActions

universe u

namespace Representation

variable (k : Type*) {A : Type*} [CommRing k] [Ring A] [Algebra k A]
variable {G : Type*} [Monoid G]

@[simps]
def adjointAux (u : Aˣ) : A →ₗ[k] A where
  toFun a := ↑u * a * ↑u⁻¹
  map_add' a b := by rw [mul_add, add_mul]
  map_smul' c a := by
    rw [RingHom.id_apply, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

@[simp]
lemma adjointAux_one : adjointAux k (1 : Aˣ) = LinearMap.id := by
  ext a
  simp

lemma adjointAux_mul (u v : Aˣ) :
    adjointAux k (u * v) = (adjointAux k u).comp (adjointAux k v) := by
  ext a
  simp only [adjointAux_apply, LinearMap.comp_apply, mul_inv_rev, Units.val_mul, mul_assoc]

def adjoint (ρ₀ : G →* Aˣ) : Representation k G A where
  toFun g := adjointAux k (ρ₀ g)
  map_one' := by
    ext a
    simp
  map_mul' g h := by
    ext a
    simp only [map_mul, adjointAux_mul, LinearMap.comp_apply, Module.End.mul_apply]

@[simp]
lemma adjoint_apply (ρ₀ : G →* Aˣ) (g : G) (a : A) :
    adjoint k ρ₀ g a = ↑(ρ₀ g) * a * ↑(ρ₀ g)⁻¹ := rfl

end Representation

namespace TrivSqZeroExt

variable {A : Type*} [Ring A]

end TrivSqZeroExt

namespace groupCohomology

open TrivSqZeroExt

variable {k A G : Type u} [CommRing k] [Ring A] [Algebra k A] [Group G]

noncomputable abbrev adjointRep (k : Type u) [CommRing k] [Algebra k A] (ρ₀ : G →* Aˣ) :
    Rep k G :=
  Rep.of (Representation.adjoint k ρ₀)

@[simp]
lemma adjointRep_ρ_apply (ρ₀ : G →* Aˣ) (g : G) (a : A) :
    (adjointRep k ρ₀).ρ g a = ↑(ρ₀ g) * a * ↑(ρ₀ g)⁻¹ := rfl

def IsDualLift (ρ₀ : G →* Aˣ) (ρ : G →* (A[ε])ˣ) : Prop :=
  ∀ g, ((ρ g : A[ε])).fst = ↑(ρ₀ g)

def dualLiftToCochain (ρ₀ : G →* Aˣ) (ρ : G →* (A[ε])ˣ) (g : G) : A :=
  ((ρ g : A[ε])).snd * ↑(ρ₀ g)⁻¹

lemma dualLiftToCochain_mem_cocycles₁ {ρ₀ : G →* Aˣ} {ρ : G →* (A[ε])ˣ}
    (hρ : IsDualLift ρ₀ ρ) :
    dualLiftToCochain ρ₀ ρ ∈ cocycles₁ (adjointRep k ρ₀) := by
  rw [mem_cocycles₁_iff]
  intro g h
  show dualLiftToCochain ρ₀ ρ (g * h)
      = ↑(ρ₀ g) * dualLiftToCochain ρ₀ ρ h * ↑(ρ₀ g)⁻¹ + dualLiftToCochain ρ₀ ρ g
  unfold dualLiftToCochain
  simp only [map_mul, Units.val_mul, snd_mul, mul_inv_rev, hρ g, hρ h, smul_eq_mul,
    op_smul_eq_mul, add_mul, mul_assoc, Units.mul_inv_cancel_left]

noncomputable def dualLiftToCocycle (k : Type u) [CommRing k] [Algebra k A]
    {ρ₀ : G →* Aˣ} {ρ : G →* (A[ε])ˣ} (hρ : IsDualLift ρ₀ ρ) :
    cocycles₁ (adjointRep k ρ₀) :=
  ⟨dualLiftToCochain ρ₀ ρ, dualLiftToCochain_mem_cocycles₁ hρ⟩

@[simp]
lemma dualLiftToCocycle_coe {ρ₀ : G →* Aˣ} {ρ : G →* (A[ε])ˣ} (hρ : IsDualLift ρ₀ ρ) :
    ((dualLiftToCocycle k hρ : cocycles₁ (adjointRep k ρ₀)) : G → A)
      = dualLiftToCochain ρ₀ ρ := rfl

end groupCohomology
