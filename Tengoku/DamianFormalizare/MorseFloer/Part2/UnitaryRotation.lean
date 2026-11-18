import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A unitary taking one unit vector to another

For unit vectors `u, v ∈ ℂⁿ` with `v ≠ -u`, the matrix

  `R(u, v) = 1 + (v - u) u* - (1 + ⟨v, u⟩)⁻¹ (u + v) (v* - ⟨v, u⟩ u*)`

is unitary, takes `u` to `v`, is the identity when `u = v`, and depends continuously on
`(u, v)` wherever `1 + ⟨v, u⟩ ≠ 0`. Here `⟨a, b⟩ = a* b`.

It is the tool that lifts homotopies of the first column of a loop of unitary matrices to
homotopies of the loop itself, which is how `π₁(U(n))` is reduced to `π₁(U(n - 1))` in
`Part2/UnitaryLoops.lean`, with no fibre bundle and no local section.
-/

open Matrix

namespace MorseFloer
namespace UnitaryLoops

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Hermitian product `⟨u, v⟩ = u* v`.-/
def herm (u v : ι → ℂ) : ℂ := star u ⬝ᵥ v

omit [DecidableEq ι] in
/--
@isnad1 id=eq.0h3v.s5.89c1d58e00e0 from=translated src=- shape=f31dc1de vocab=8edc2cee
-/
theorem star_herm (u v : ι → ℂ) : star (herm u v) = herm v u := by
  rw [herm, herm, Matrix.star_dotProduct, star_star]

/-- The unitary `R(u, v)` taking `u` to `v`.-/
noncomputable def rot (u v : ι → ℂ) : Matrix ι ι ℂ :=
  1 + vecMulVec (v - u) (star u) -
    (1 + herm v u)⁻¹ • vecMulVec (u + v) (star v - herm v u • star u)

/--
@isnad1 id=eq.0h4v.s7.7a17c4623c3f from=translated src=- shape=9c44e075 vocab=86c7a57d
-/
theorem rot_mulVec (u v x : ι → ℂ) :
    rot u v *ᵥ x = x + herm u x • (v - u) -
      ((1 + herm v u)⁻¹ * (herm v x - herm v u * herm u x)) • (u + v) := by
  simp only [rot, add_mulVec, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
    sub_dotProduct, smul_dotProduct, op_smul_eq_smul, smul_eq_mul, herm, smul_smul]

/--
@isnad1 id=eq.0h3v.s8.df18c7c60716 from=translated src=- shape=84e97b42 vocab=89d19ac9
-/
theorem rot_conjTranspose (u v : ι → ℂ) :
    (rot u v)ᴴ = 1 + vecMulVec u (star v - star u) -
      (1 + herm u v)⁻¹ • vecMulVec (v - herm u v • u) (star u + star v) := by
  simp only [rot, conjTranspose_add, conjTranspose_sub, conjTranspose_one, conjTranspose_smul,
    conjTranspose_vecMulVec, star_sub, star_add, star_star, star_smul, star_inv₀, star_one,
    star_herm]

/--
@isnad1 id=eq.0h4v.s8.823420743138 from=translated src=- shape=495986d3 vocab=237d3254
-/
theorem rot_conjTranspose_mulVec (u v y : ι → ℂ) :
    (rot u v)ᴴ *ᵥ y = y + (herm v y - herm u y) • u -
      ((1 + herm u v)⁻¹ * (herm u y + herm v y)) • (v - herm u v • u) := by
  rw [rot_conjTranspose]
  simp only [add_mulVec, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
    sub_dotProduct, add_dotProduct, op_smul_eq_smul, herm, smul_smul]

variable {u v : ι → ℂ}

/-- `R(u, v)` takes `u` to `v`.
@isnad1 id=eq.1h3v.s5.89267fabefbb from=translated src=- shape=0505cd59 vocab=35edb4e7
-/
theorem rot_mulVec_self (hu : herm u u = 1) : rot u v *ᵥ u = v := by
  rw [rot_mulVec, hu, one_smul, mul_one, sub_self, mul_zero, zero_smul, sub_zero,
    add_sub_cancel]

/-- `R(u, u) = 1`.
@isnad1 id=eq.1h2v.s5.9ae6e2060e64 from=translated src=- shape=f7feb65c vocab=f5cea37d
-/
theorem rot_self (hu : herm u u = 1) : rot u u = 1 := by
  rw [rot, sub_self, zero_vecMulVec, add_zero, hu, one_smul, sub_self, vecMulVec_zero,
    smul_zero, sub_zero]

/-- **`R(u, v)` is unitary** when `u` and `v` are unit vectors and `1 + ⟨v, u⟩ ≠ 0`.
@isnad1 id=eq.3h3v.s7.f32637368dfd from=translated src=- shape=e927f05f vocab=339f932b
-/
theorem rot_conjTranspose_mul (hu : herm u u = 1) (hv : herm v v = 1)
    (h : 1 + herm v u ≠ 0) : (rot u v)ᴴ * rot u v = 1 := by
  have h' : 1 + herm u v ≠ 0 := by
    rw [← star_herm, ← star_one, ← star_add, ne_eq, star_eq_zero]; exact h
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    rot_mulVec, rot_conjTranspose_mulVec]
  -- expand the Hermitian products of `R(u, v) x` with `u` and `v`
  simp only [herm, dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hu hv h h' ⊢
  rw [hu, hv]
  set α := star v ⬝ᵥ u
  set β := star u ⬝ᵥ v
  set a := star u ⬝ᵥ x
  set b := star v ⬝ᵥ x
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/--
@isnad1 id=mem.3h3v.s7.4ba653fa9e97 from=translated src=- shape=7d7e6de0 vocab=cde45bf6
-/
theorem rot_mem_unitaryGroup (hu : herm u u = 1) (hv : herm v v = 1) (h : 1 + herm v u ≠ 0) :
    rot u v ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  exact rot_conjTranspose_mul hu hv h

/-- `R(u, v)` depends continuously on `(u, v)` where `1 + ⟨v, u⟩ ≠ 0`.
@isnad1 id=continuo.3h4v.s7.40cff7480180 from=translated src=- shape=40b9c4b9 vocab=2407d9fa
-/
theorem continuous_rot {X : Type*} [TopologicalSpace X] {u v : X → ι → ℂ} (hu : Continuous u)
    (hv : Continuous v) (h : ∀ x, 1 + herm (v x) (u x) ≠ 0) :
    Continuous fun x => rot (u x) (v x) := by
  have hh : ∀ {a b : X → ι → ℂ}, Continuous a → Continuous b →
      Continuous fun x => herm (a x) (b x) := fun ha hb => by
    simp only [herm, dotProduct]
    fun_prop
  have hvm : ∀ {a b : X → ι → ℂ}, Continuous a → Continuous b →
      Continuous fun x => vecMulVec (a x) (b x) := fun ha hb => by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [vecMulVec_apply]
    fun_prop
  unfold rot
  refine (continuous_const.add (hvm (hv.sub hu) hu.star)).sub
    (((continuous_const.add (hh hv hu)).inv₀ h).smul
      (hvm (hu.add hv) (hv.star.sub ((hh hv hu).smul hu.star))))

end UnitaryLoops
end MorseFloer
