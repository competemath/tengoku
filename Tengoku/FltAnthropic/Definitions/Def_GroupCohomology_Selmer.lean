import Tengoku.Seed.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Tengoku.Seed.RepresentationTheory.Invariants
import Tengoku.Seed.LinearAlgebra.Dual.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open CategoryTheory Module

universe u

namespace Representation

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

def twist (ρ : Representation k G V) (χ : G →* kˣ) : Representation k G V where
  toFun g := (χ g : k) • ρ g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, Units.val_mul, mul_smul, smul_mul_assoc, mul_smul_comm]

/--
@isnad1 id=eq.0h6v.s9.2287ea03b666 from=translated src=- shape=abb88097 vocab=977edc0f
-/
lemma twist_apply (ρ : Representation k G V) (χ : G →* kˣ) (g : G) :
    ρ.twist χ g = (χ g : k) • ρ g := rfl

/--
@isnad1 id=eq.0h7v.s9.bf1b709eee88 from=translated src=- shape=a66d0c42 vocab=977edc0f
-/
lemma twist_apply_apply (ρ : Representation k G V) (χ : G →* kˣ) (g : G) (v : V) :
    ρ.twist χ g v = (χ g : k) • ρ g v := rfl

/--
@isnad1 id=eq.0h4v.s7.47f2eb05f8f7 from=translated src=- shape=19941848 vocab=ed3c6dad
-/
@[simp]
lemma twist_one (ρ : Representation k G V) : ρ.twist 1 = ρ := by
  ext g v
  simp [twist_apply_apply]

end Representation

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

noncomputable abbrev twist (A : Rep k G) (χ : G →* kˣ) : Rep k G :=
  Rep.of (A.ρ.twist χ)

noncomputable abbrev dualTwist (A : Rep k G) (χ : G →* kˣ) : Rep k G :=
  Rep.of (A.ρ.dual.twist χ)

/--
@isnad1 id=eq.0h6v.s11.ff3bd4ec9a03 from=translated src=- shape=4459f167 vocab=de216ee6
-/
lemma dualTwist_ρ_apply (A : Rep k G) (χ : G →* kˣ) (g : G) (f : Module.Dual k A) :
    (A.dualTwist χ).ρ g f = (χ g : k) • (f ∘ₗ A.ρ g⁻¹) := rfl

/--
@isnad1 id=eq.0h4v.s8.fac4cf83e188 from=translated src=- shape=54c3d114 vocab=0746d897
-/
lemma finrank_dualTwist (k : Type u) [Field k] {G : Type u} [Group G] (A : Rep k G)
    (χ : G →* kˣ) [FiniteDimensional k A] :
    finrank k (A.dualTwist χ) = finrank k A :=
  Subspace.dual_finrank_eq

end Rep

namespace groupCohomology

variable {k : Type u} [Field k]
variable {Γ : Type u} [Group Γ]
variable {ι : Type u} [Fintype ι] {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M : Rep k Γ)

noncomputable abbrev locRes (v : ι) : H1 M ⟶ H1 (Rep.res (loc v) M) :=
  map (loc v) (𝟙 (Rep.res (loc v) M)) 1

noncomputable def selmer (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) :
    Submodule k (H1 M) :=
  ⨅ v, (L v).comap (locRes loc M v).hom

omit [Fintype ι] in
/--
@isnad1 id=iff.0h8v.s11.52b094d93daf from=translated src=- shape=28deb6e3 vocab=6ec6073b
-/
lemma mem_selmer_iff (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) (x : H1 M) :
    x ∈ selmer loc M L ↔ ∀ v, (locRes loc M v).hom x ∈ L v := by
  simp [selmer, Submodule.mem_iInf]

omit [Fintype ι] in

/--
@isnad1 id=le.1h8v.s10.452c8234f7a5 from=translated src=- shape=9209e136 vocab=f4d21a07
-/
lemma selmer_mono {L L' : ∀ v, Submodule k (H1 (Rep.res (loc v) M))}
    (h : ∀ v, L v ≤ L' v) : selmer loc M L ≤ selmer loc M L' :=
  iInf_mono fun v => Submodule.comap_mono (h v)

omit [Fintype ι] in

/--
@isnad1 id=le.0h7v.s10.85983a4e8999 from=translated src=- shape=d75bd3c1 vocab=fc5126b0
-/
lemma selmer_bot_le (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) :
    selmer loc M (fun _ => ⊥) ≤ selmer loc M L :=
  selmer_mono loc M fun _ => bot_le

omit [Fintype ι] in

/--
@isnad1 id=subsingl.0h7v.s9.871be3123b32 from=translated src=- shape=a3884fc7 vocab=ce2223ce
-/
lemma subsingleton_selmer_of_subsingleton (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M)))
    [Subsingleton (H1 M)] : Subsingleton (selmer loc M L) :=
  inferInstance

def orthogonal {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (B : V →ₗ[k] W →ₗ[k] k) (L : Submodule k V) : Submodule k W :=
  L.dualAnnihilator.comap B.flip

/--
@isnad1 id=iff.0h6v.s9.edc290a82d44 from=translated src=- shape=d8d99840 vocab=f6f55909
-/
@[simp]
lemma mem_orthogonal_iff {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (B : V →ₗ[k] W →ₗ[k] k) (L : Submodule k V) (w : W) :
    w ∈ orthogonal B L ↔ ∀ x ∈ L, B x w = 0 := by
  simp only [orthogonal, Submodule.mem_comap, Submodule.mem_dualAnnihilator]
  exact forall₂_congr fun x _ => by rw [LinearMap.flip_apply]

/--
@isnad1 id=eq.0h4v.s8.a274e2fd1c0d from=translated src=- shape=494ae053 vocab=a09f5ec8
-/
@[simp]
lemma orthogonal_bot {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (B : V →ₗ[k] W →ₗ[k] k) : orthogonal B (⊥ : Submodule k V) = ⊤ := by
  ext w
  simp only [mem_orthogonal_iff, Submodule.mem_top, iff_true]
  rintro x rfl
  simp

/--
@isnad1 id=le.1h6v.s8.0eb6bdb828b1 from=translated src=- shape=e499870e vocab=d524806c
-/
lemma orthogonal_anti {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (B : V →ₗ[k] W →ₗ[k] k) {L L' : Submodule k V} (h : L ≤ L') :
    orthogonal B L' ≤ orthogonal B L :=
  Submodule.comap_mono (Submodule.dualAnnihilator_anti h)

variable (M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)

noncomputable def dualConditions (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) (v : ι) :
    Submodule k (H1 (Rep.res (loc v) M')) :=
  orthogonal (pairing v) (L v)

def greenbergWilesEq (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) : Prop :=
  finrank k (selmer loc M L)
      + finrank k M'.ρ.invariants
      + ∑ v, finrank k (Rep.res (loc v) M).ρ.invariants
    = finrank k (selmer loc M' (dualConditions loc M M' pairing L))
      + finrank k M.ρ.invariants
      + ∑ v, finrank k (L v)

structure IsGreenbergWilesDatum (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) : Prop where

  finite_selmer : FiniteDimensional k (selmer loc M L)

  finite_dualSelmer :
    FiniteDimensional k (selmer loc M' (dualConditions loc M M' pairing L))

  finite_local : ∀ v, FiniteDimensional k (L v)

  formula : greenbergWilesEq loc M M' pairing L

/--
@isnad1 id=le.1h9v.s12.e69a964a3f99 from=translated src=- shape=65d649b3 vocab=92c37a99
-/
theorem finrank_selmer_le_of_isGreenbergWilesDatum
    {L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))}
    (h : IsGreenbergWilesDatum loc M M' pairing L) :
    finrank k (selmer loc M L)
      ≤ finrank k (selmer loc M' (dualConditions loc M M' pairing L))
        + finrank k M.ρ.invariants + ∑ v, finrank k (L v) := by
  have := h.formula
  unfold greenbergWilesEq at this
  omega

def localTermBalanced (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) : Prop :=
  ∀ v, finrank k (L v) = finrank k (Rep.res (loc v) M).ρ.invariants

end groupCohomology
