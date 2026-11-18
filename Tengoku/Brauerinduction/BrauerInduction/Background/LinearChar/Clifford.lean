import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.AbelianGroup
import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.CentralKernel
import Tengoku.Brauerinduction.BrauerInduction.Background.LinearChar.Mackey
import Tengoku.Brauerinduction.BrauerInduction.Background.LinearChar.OneDimensional
import Tengoku.Brauerinduction.BrauerInduction.Background.LinearChar.QuotientDescent
import Tengoku.Brauerinduction.BrauerInduction.Background.Group.Nilpotent
import Tengoku.Brauerinduction.BrauerInduction.Background.Fintype.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Clifford theory for nilpotent groups

This file formalizes the Clifford-theoretic monomiality theorem for finite
nilpotent groups. In the present development, it is the key ingredient in the
proof of `BrauerSpanChar.le_BrauerSpanLin`: since Brauer-elementary groups are
nilpotent, their irreducible characters are induced from linear characters of
subgroups.

The same argument supplies the monomiality step in Serre's proof of Brauer
induction; see Serre [1977, §10.5, Theorems 19–20], especially the appeal after
Theorem 20 to §8.5, Theorem 16.

The main ingredients are:

* a simple representation restricts nontrivially to a linear character on a
  normal abelian subgroup;
* the associated inertia subgroup induces back to the original representation;
* if the central kernel is trivial, this inertia subgroup is proper;
* if the central kernel is nontrivial, the representation descends to a smaller
  quotient.

Combining these cases proves that every simple representation of a finite
nilpotent group over an algebraically closed field of characteristic zero is
induced from a linear character of a subgroup.
-/

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
variable {G : Type u} [Group G] [Finite G]

open CategoryTheory

namespace FDRep

/--
If an element acts trivially on a representation, then every element of its
normal closure acts trivially.-/
private lemma rho_trivial_of_mem_normalClosure_singleton
    {k : Type u} [CommRing k]
    {G : Type v} [Group G]
    (ρ : FDRep k G)
    {c z : G}
    (hc : ρ.ρ c = LinearMap.id)
    (hz : z ∈ Subgroup.normalClosure ({c} : Set G)) :
    ρ.ρ z = LinearMap.id := by
  let K : Subgroup G := MonoidHom.ker ρ.ρ
  have hK_normal : K.Normal := by
    infer_instance
  have hcK : c ∈ K := by
    change ρ.ρ c = 1
    exact MonoidHom.mem_ker.mp hc
  have hle : Subgroup.normalClosure ({c} : Set G) ≤ K := by
    intro x hx
    exact Subgroup.normalClosure_le_normal
      (by
        intro y hy
        simp only [Set.mem_singleton_iff] at hy
        subst y
        exact hcK)
      hx
  have hzK : z ∈ K := hle hz
  change ρ.ρ z = 1 at hzK
  change ρ.ρ z = (1 : ρ →ₗ[k] ρ)
  exact hzK

/--
Inducing a linear character from the top subgroup gives the corresponding
representation of `G`.-/
noncomputable def indLin_top_iso_self
    {k : Type u} [Field k] [CharZero k]
    (ψ : (⊤ : Subgroup G) →* kˣ) :
    FDRep.indLin (k := k) (⊤ : Subgroup G) ψ ≅
      FDRep.ofTop (G := G) (k := k)
        (FDRep.ofLinearChar
          (G := (⊤ : Subgroup G)) (k := k) ψ) := by
  unfold FDRep.indLin
  exact
    FDRep.indTopIsoOfTop
      (G := G) (k := k)
      (FDRep.ofLinearChar
        (G := (⊤ : Subgroup G)) (k := k) ψ)

end FDRep

namespace LinearChar

/--
If `g` and `a` do not commute, then the commutator `g * a * g⁻¹ * a⁻¹` is
nontrivial.-/
private lemma commutator_ne_one_of_mul_ne {G : Type v} [Group G]
    {g a : G} (hga : g * a ≠ a * g) :
    g * a * g⁻¹ * a⁻¹ ≠ 1 := by
  intro hc
  apply hga
  have hconj : g * a * g⁻¹ = a := by
    apply mul_inv_eq_one.mp
    simpa [mul_assoc] using hc
  calc
    g * a = (g * a * g⁻¹) * g := by
      simp [mul_assoc]
    _ = a * g := by
      rw [hconj]

/--
If the central kernel of a simple representation is trivial, and `A` is a
normal abelian subgroup strictly larger than the center, then any linear
character of `A` occurring in `ρ|_A` has proper inertia.
@isnad1 id=ne.3h5v.s10.21991c1b4591 from=translated src=- shape=4981f9d7 vocab=72a97455
-/
theorem inertia_ne_top_of_centralKernel_eq_bot
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : Type v} [Group G]
    [Group.IsNilpotent G]
    (ρ : FDRep k G) [Simple ρ]
    (hck : FDRep.centralKernel ρ = ⊥)
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (hA : Subgroup.center G < A)
    (ψ : A →* kˣ)
    (hW : LinearChar.psiEigenspace ρ A ψ ≠ ⊥) :
    LinearChar.inertia ψ ≠ ⊤ := by
  intro hI

  have hA_scalar :
      ∀ a : A, ρ.ρ (a : G) = (ψ a : k) • LinearMap.id :=
    rho_eq_smul_of_inertia_eq_top ρ A ψ hI hW

  -- Since `A` is strictly larger than the center, choose a noncentral element of `A`.
  obtain ⟨a, haA, ha_not_center⟩ : ∃ a : G, a ∈ A ∧ a ∉ Subgroup.center G := by
    by_contra h'; push Not at h'; exact (not_le_of_gt hA) h'

  -- Since `a` is not central, choose `g` with `g * a ≠ a * g`.
  obtain ⟨g, hga_ne⟩ : ∃ g : G, g * a ≠ a * g := by
    by_contra h; push Not at h; exact ha_not_center ((Subgroup.mem_center_iff).2 h)

  -- The commutator is nontrivial.
  let c : G := g * a * g⁻¹ * a⁻¹
  have hc_ne_one : c ≠ 1 := by
    dsimp [c]; exact commutator_ne_one_of_mul_ne hga_ne

  -- But because `a` acts by scalar on `ρ`, its conjugate also acts by the same scalar,
  -- so the commutator acts trivially.
  have hc_trivial :
      ρ.ρ c = LinearMap.id := by
    let aA : A := ⟨a, haA⟩
    have ha_scalar :
        ρ.ρ a = (ψ aA : k) • LinearMap.id := by
      simpa [aA] using hA_scalar aA
    have hainv_scalar :
        ρ.ρ a⁻¹ = (ψ aA⁻¹ : k) • LinearMap.id := by
      simpa [aA] using hA_scalar aA⁻¹
    dsimp [c]
    rw [map_mul, map_mul, map_mul]
    rw [ha_scalar, hainv_scalar]
    ext v
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
      map_smul, smul_smul]
    simp only [map_inv, Units.val_inv_eq_inv_val, ne_eq, Units.ne_zero, not_false_eq_true,
      inv_mul_cancel₀, Representation.self_inv_apply, one_smul]

  -- From the nontrivial normal closure of `c`, nilpotence gives a nontrivial central
  -- element in that normal closure.
  obtain ⟨z, hz_center, hz_nc, hz_ne⟩ :
      ∃ z : G,
        z ∈ Subgroup.center G ∧
        z ∈ Subgroup.normalClosure ({c} : Set G) ∧
        z ≠ 1 := by
    -- nilpotent group lemma: nontrivial normal subgroup meets center nontrivially
    exact Group.exists_center_mem_normalClosure_singleton_of_ne_one hc_ne_one

  -- Since `c` acts trivially, everything in its normal closure acts trivially.
  have hz_trivial :
      ρ.ρ z = LinearMap.id := by
      exact FDRep.rho_trivial_of_mem_normalClosure_singleton ρ hc_trivial hz_nc

  -- A nontrivial central element acting trivially lies in the central kernel,
  -- contradicting `centralKernel ρ = ⊥`.
  have hz_ck : z ∈ FDRep.centralKernel ρ := by
    exact
      (FDRep.center_coe_mem_centralKernel_iff ρ ⟨z, hz_center⟩).2 hz_trivial

  have hz_one : z = 1 := by
    have : z ∈ (⊥ : Subgroup G) := by
      simpa [hck] using hz_ck
    simpa using this

  exact hz_ne hz_one

end LinearChar

namespace FDRep

end FDRep
