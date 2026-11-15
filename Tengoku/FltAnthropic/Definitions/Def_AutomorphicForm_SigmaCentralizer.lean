import Tengoku.Seed.GroupTheory.Subgroup.Centralizer
import Tengoku.Seed.Tactic.Group

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace AutomorphicForm

variable {G : Type*} [Group G]

def sigmaCentralizer (σ : G →* G) (δ : G) : Subgroup G where
  carrier := {t | t * δ * (σ t)⁻¹ = δ}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, one_mul, map_one, inv_one, mul_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    have key : a * b * δ * (σ (a * b))⁻¹ = a * (b * δ * (σ b)⁻¹) * (σ a)⁻¹ := by
      simp only [map_mul, mul_inv_rev]
      group
    rw [key, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_inv, inv_inv]
    have h2 : δ * σ a = a * δ := by
      calc δ * σ a = (a * δ * (σ a)⁻¹) * σ a := by rw [ha]
        _ = a * δ := by group
    calc a⁻¹ * δ * σ a = a⁻¹ * (δ * σ a) := by group
      _ = a⁻¹ * (a * δ) := by rw [h2]
      _ = δ := by group

/--
@isnad1 id=iff.0h4v.s7.793eb74d23b7 from=translated src=- shape=37664d6f vocab=1c901497
-/
@[simp] theorem mem_sigmaCentralizer_iff {σ : G →* G} {δ t : G} :
    t ∈ sigmaCentralizer σ δ ↔ t * δ * (σ t)⁻¹ = δ := Iff.rfl

/--
@isnad1 id=iff.0h4v.s7.be6eec7a5b0d from=translated src=- shape=bb5c8933 vocab=1c901497
-/
theorem mem_sigmaCentralizer_iff_fixed {σ : G →* G} {δ t : G} :
    t ∈ sigmaCentralizer σ δ ↔ δ * σ t * δ⁻¹ = t := by
  rw [mem_sigmaCentralizer_iff, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
  exact eq_comm

/--
@isnad1 id=iff.0h4v.s7.876e2b85298f from=translated src=- shape=ec5f67ef vocab=1c901497
-/
theorem mem_sigmaCentralizer_iff_inv {σ : G →* G} {δ t : G} :
    t ∈ sigmaCentralizer σ δ ↔ t⁻¹ * δ * σ t = δ := by
  rw [mem_sigmaCentralizer_iff, mul_inv_eq_iff_eq_mul, mul_assoc, inv_mul_eq_iff_eq_mul]
  exact eq_comm

/--
@isnad1 id=eq.0h2v.s5.aa0cf52f26e7 from=translated src=- shape=09f66ff0 vocab=660f5254
-/
theorem sigmaCentralizer_id (δ : G) :
    sigmaCentralizer (MonoidHom.id G) δ = Subgroup.centralizer {δ} := by
  ext t
  rw [mem_sigmaCentralizer_iff, Subgroup.mem_centralizer_singleton_iff, MonoidHom.id_apply,
    mul_inv_eq_iff_eq_mul]

/--
@isnad1 id=eq.0h2v.s6.54102946693b from=translated src=- shape=5153ba62 vocab=608423e2
-/
theorem sigmaCentralizer_one_eq_bot (δ : G) :
    sigmaCentralizer (1 : G →* G) δ = ⊥ := by
  ext t
  rw [mem_sigmaCentralizer_iff, Subgroup.mem_bot]
  constructor
  · intro h
    have h1 : t * δ = δ := by
      simpa using h
    exact mul_right_cancel (by rw [one_mul]; exact h1)
  · rintro rfl
    simp
