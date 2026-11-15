import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ExplicitLift
import Tengoku.Seed.Algebra.Group.Submonoid.Membership
import Tengoku.Seed.LinearAlgebra.Matrix.Trace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace LanglandsTunnell.Lift48

open FLT.ExplicitLift Matrix

abbrev Mat : Type := Matrix (Fin 2) (Fin 2) (ℤ√(-2))

def K48 : List Mat := [
  !![⟨1, 0⟩, ⟨0, 0⟩; ⟨0, 0⟩, ⟨1, 0⟩],
  !![⟨-1, 0⟩, ⟨1, 0⟩; ⟨-1, 0⟩, ⟨0, 0⟩],
  !![⟨1, 0⟩, ⟨-1, 0⟩; ⟨0, -1⟩, ⟨-1, 1⟩],
  !![⟨0, 0⟩, ⟨-1, 0⟩; ⟨1, 0⟩, ⟨-1, 0⟩],
  !![⟨-1, -1⟩, ⟨0, 1⟩; ⟨-1, 0⟩, ⟨1, 0⟩],
  !![⟨0, 0⟩, ⟨1, 0⟩; ⟨1, 0⟩, ⟨0, -1⟩],
  !![⟨1, 1⟩, ⟨0, -1⟩; ⟨2, 0⟩, ⟨-1, -1⟩],
  !![⟨0, 1⟩, ⟨1, -1⟩; ⟨1, 1⟩, ⟨0, -1⟩],
  !![⟨1, 0⟩, ⟨-1, -1⟩; ⟨0, 0⟩, ⟨-1, 0⟩],
  !![⟨1, -1⟩, ⟨-1, 0⟩; ⟨-1, -1⟩, ⟨0, 1⟩],
  !![⟨-1, 0⟩, ⟨0, 0⟩; ⟨-1, 1⟩, ⟨1, 0⟩],
  !![⟨0, -1⟩, ⟨-1, 1⟩; ⟨-1, 0⟩, ⟨1, 1⟩],
  !![⟨-1, 0⟩, ⟨1, 1⟩; ⟨-1, 1⟩, ⟨2, 0⟩],
  !![⟨-1, 1⟩, ⟨1, 0⟩; ⟨0, 1⟩, ⟨1, 0⟩],
  !![⟨-1, 0⟩, ⟨0, 1⟩; ⟨-1, 0⟩, ⟨1, 1⟩],
  !![⟨-2, 0⟩, ⟨1, 1⟩; ⟨-1, 1⟩, ⟨1, 0⟩],
  !![⟨0, 1⟩, ⟨1, 0⟩; ⟨1, 0⟩, ⟨0, 0⟩],
  !![⟨-1, 1⟩, ⟨2, 0⟩; ⟨0, 1⟩, ⟨1, -1⟩],
  !![⟨0, 1⟩, ⟨1, -1⟩; ⟨1, 0⟩, ⟨-1, -1⟩],
  !![⟨1, 0⟩, ⟨0, 0⟩; ⟨1, -1⟩, ⟨-1, 0⟩],
  !![⟨1, 0⟩, ⟨0, -1⟩; ⟨0, -1⟩, ⟨-1, 0⟩],
  !![⟨2, 0⟩, ⟨-1, -1⟩; ⟨1, -1⟩, ⟨-2, 0⟩],
  !![⟨0, -1⟩, ⟨-1, 0⟩; ⟨-1, -1⟩, ⟨-1, 1⟩],
  !![⟨1, -1⟩, ⟨-2, 0⟩; ⟨-1, -1⟩, ⟨-1, 1⟩],
  !![⟨0, -1⟩, ⟨-1, 1⟩; ⟨-1, -1⟩, ⟨0, 1⟩],
  !![⟨-1, 0⟩, ⟨0, 0⟩; ⟨0, 0⟩, ⟨-1, 0⟩],
  !![⟨1, -1⟩, ⟨-1, 0⟩; ⟨0, -1⟩, ⟨-1, 0⟩],
  !![⟨1, 0⟩, ⟨-1, -1⟩; ⟨1, -1⟩, ⟨-2, 0⟩],
  !![⟨1, -1⟩, ⟨-2, 0⟩; ⟨0, -1⟩, ⟨-1, 1⟩],
  !![⟨0, -1⟩, ⟨-1, 0⟩; ⟨-1, 0⟩, ⟨0, 0⟩],
  !![⟨-1, -1⟩, ⟨-1, 1⟩; ⟨-1, 0⟩, ⟨0, 1⟩],
  !![⟨-1, -1⟩, ⟨-1, 1⟩; ⟨-2, 0⟩, ⟨1, 1⟩],
  !![⟨-1, 0⟩, ⟨0, 1⟩; ⟨0, 1⟩, ⟨1, 0⟩],
  !![⟨-2, 0⟩, ⟨1, 1⟩; ⟨-1, 1⟩, ⟨2, 0⟩],
  !![⟨-1, 0⟩, ⟨1, 0⟩; ⟨0, 1⟩, ⟨1, -1⟩],
  !![⟨-1, 1⟩, ⟨1, 0⟩; ⟨1, 1⟩, ⟨0, -1⟩],
  !![⟨-1, 0⟩, ⟨1, 1⟩; ⟨0, 0⟩, ⟨1, 0⟩],
  !![⟨-1, 1⟩, ⟨2, 0⟩; ⟨1, 1⟩, ⟨1, -1⟩],
  !![⟨0, 1⟩, ⟨1, 0⟩; ⟨1, 1⟩, ⟨1, -1⟩],
  !![⟨1, 1⟩, ⟨1, -1⟩; ⟨2, 0⟩, ⟨-1, -1⟩],
  !![⟨1, 1⟩, ⟨1, -1⟩; ⟨1, 0⟩, ⟨0, -1⟩],
  !![⟨1, 0⟩, ⟨0, -1⟩; ⟨1, 0⟩, ⟨-1, -1⟩],
  !![⟨2, 0⟩, ⟨-1, -1⟩; ⟨1, -1⟩, ⟨-1, 0⟩],
  !![⟨1, 0⟩, ⟨-1, 0⟩; ⟨1, 0⟩, ⟨0, 0⟩],
  !![⟨1, 1⟩, ⟨0, -1⟩; ⟨1, 0⟩, ⟨-1, 0⟩],
  !![⟨0, 0⟩, ⟨-1, 0⟩; ⟨-1, 0⟩, ⟨0, 1⟩],
  !![⟨-1, -1⟩, ⟨0, 1⟩; ⟨-2, 0⟩, ⟨1, 1⟩],
  !![⟨0, 0⟩, ⟨1, 0⟩; ⟨-1, 0⟩, ⟨1, 0⟩]
]

def W48 : List (List (Fin 2)) := [
  [],
  [0],
  [1],
  [0, 0],
  [0, 1],
  [1, 0],
  [1, 1],
  [0, 0, 1],
  [0, 1, 0],
  [0, 1, 1],
  [1, 0, 0],
  [1, 0, 1],
  [1, 1, 0],
  [1, 1, 1],
  [0, 0, 1, 0],
  [0, 0, 1, 1],
  [0, 1, 0, 0],
  [0, 1, 0, 1],
  [0, 1, 1, 0],
  [0, 1, 1, 1],
  [1, 0, 1, 0],
  [1, 0, 1, 1],
  [1, 1, 0, 0],
  [1, 1, 0, 1],
  [1, 1, 1, 0],
  [1, 1, 1, 1],
  [0, 0, 1, 0, 0],
  [0, 0, 1, 0, 1],
  [0, 0, 1, 1, 0],
  [0, 0, 1, 1, 1],
  [0, 1, 0, 1, 0],
  [0, 1, 0, 1, 1],
  [0, 1, 1, 0, 0],
  [0, 1, 1, 0, 1],
  [0, 1, 1, 1, 0],
  [1, 0, 1, 0, 0],
  [1, 0, 1, 0, 1],
  [1, 0, 1, 1, 0],
  [1, 0, 1, 1, 1],
  [1, 1, 0, 1, 0],
  [1, 1, 0, 1, 1],
  [1, 1, 1, 0, 0],
  [1, 1, 1, 0, 1],
  [1, 1, 1, 1, 0],
  [0, 0, 1, 1, 1, 0],
  [0, 1, 1, 1, 0, 0],
  [1, 0, 1, 1, 1, 0],
  [1, 1, 1, 1, 0, 0]
]

def evalWord : List (Fin 2) → Mat
  | [] => 1
  | 0 :: w => Slift * evalWord w
  | 1 :: w => Tlift * evalWord w

/--
@isnad1 id=eq.0h0v.s3.f08e5fbbdfaa from=translated src=- shape=301eebb9 vocab=6f773f5c
-/
theorem K48_eq_map_evalWord : K48 = W48.map evalWord := by decide

/--
@isnad1 id=eq.0h0v.s3.dae5a7ac5d47 from=translated src=- shape=b3c4969c vocab=59bdac9f
-/
theorem length_K48 : K48.length = 48 := by decide

/--
@isnad1 id=nodup.0h0v.s1.f4ead4d3e2da from=translated src=- shape=25b03439 vocab=1a82f0e2
-/
theorem nodup_K48 : K48.Nodup := by decide

/--
@isnad1 id=mem.0h0v.s5.939f87b5298c from=translated src=- shape=d52416c9 vocab=19a80fed
-/
theorem one_mem_K48 : (1 : Mat) ∈ K48 := by decide

/--
@isnad1 id=mem.0h0v.s4.28ae1cf8ce7a from=translated src=- shape=81ae8f40 vocab=8971e992
-/
theorem Slift_mem_K48 : Slift ∈ K48 := by decide

/--
@isnad1 id=mem.0h0v.s4.cc859bab4f4f from=translated src=- shape=81ae8f40 vocab=79fc6afa
-/
theorem Tlift_mem_K48 : Tlift ∈ K48 := by decide

/--
@isnad1 id=mem.1h1v.s7.bd430861c785 from=translated src=- shape=9d58cdca vocab=c60df9af
-/
theorem Slift_mul_mem_K48 : ∀ k ∈ K48, Slift * k ∈ K48 := by decide

/--
@isnad1 id=mem.1h1v.s7.000c455707c8 from=translated src=- shape=9d58cdca vocab=5eadc8cb
-/
theorem Tlift_mul_mem_K48 : ∀ k ∈ K48, Tlift * k ∈ K48 := by decide

/--
@isnad1 id=mem.0h1v.s7.484ef12396c5 from=translated src=- shape=a3f2a479 vocab=9552d859
-/
theorem evalWord_mem_closure (w : List (Fin 2)) :
    evalWord w ∈ Submonoid.closure ({Slift, Tlift} : Set Mat) := by
  induction w with
  | nil => exact Submonoid.one_mem _
  | cons a w ih =>
    match a with
    | 0 => exact Submonoid.mul_mem _ (Submonoid.subset_closure (by simp)) ih
    | 1 => exact Submonoid.mul_mem _ (Submonoid.subset_closure (by simp)) ih

/--
@isnad1 id=iff.0h1v.s7.90acc7d3873f from=translated src=- shape=4377831e vocab=c06657c8
-/
theorem mem_closure_iff_mem_K48 (k : Mat) :
    k ∈ Submonoid.closure ({Slift, Tlift} : Set Mat) ↔ k ∈ K48 := by
  constructor
  · intro hk
    induction hk using Submonoid.closure_induction_left with
    | one => exact one_mem_K48
    | mul_left x hx y hy ih =>
      rcases hx with rfl | rfl
      · exact Slift_mul_mem_K48 y ih
      · exact Tlift_mul_mem_K48 y ih
  · intro hk
    have h := K48_eq_map_evalWord ▸ hk
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 h
    exact evalWord_mem_closure w

/--
@isnad1 id=mem.1h1v.s8.f3dba4c57855 from=translated src=- shape=5890c369 vocab=5eadc8cb
-/
theorem negTcube_mul_mem_K48 : ∀ k ∈ K48, -(Tlift * Tlift * Tlift) * k ∈ K48 := by decide

def pw (A : Mat) : ℕ → Mat
  | 0 => 1
  | n + 1 => A * pw A n

/--
@isnad1 id=eq.0h2v.s5.4b01ba20218a from=translated src=- shape=f5c09d68 vocab=be5d05d8
-/
theorem pw_eq_pow (A : Mat) (n : ℕ) : pw A n = A ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pw, ih, pow_succ']

def det2 (A : Mat) : ℤ√(-2) := A 0 0 * A 1 1 - A 0 1 * A 1 0

/--
@isnad1 id=eq.0h1v.s5.ae5eff50d2f9 from=translated src=- shape=a64c3fde vocab=bd2c4769
-/
theorem det2_eq_det (A : Mat) : det2 A = A.det := (Matrix.det_fin_two A).symm

def tr2 (A : Mat) : ℤ√(-2) := A 0 0 + A 1 1

/--
@isnad1 id=eq.0h1v.s5.81728b1899ee from=translated src=- shape=a64c3fde vocab=3872b868
-/
theorem tr2_eq_trace (A : Mat) : tr2 A = A.trace := (Matrix.trace_fin_two A).symm

def IsPM1 (A : Mat) : Prop := A = 1 ∨ A = -1

instance : DecidablePred IsPM1 := fun A => inferInstanceAs (Decidable (A = 1 ∨ A = -1))

def IsProjOrder (n : ℕ) (A : Mat) : Prop := IsPM1 (pw A n) ∧ ∀ m ∈ List.range' 1 (n - 1), ¬ IsPM1 (pw A m)

instance (n : ℕ) : DecidablePred (IsProjOrder n) := fun A =>
  inferInstanceAs (Decidable (IsPM1 (pw A n) ∧ ∀ m ∈ List.range' 1 (n - 1), ¬ IsPM1 (pw A m)))

/--
@isnad1 id=or.1h1v.s5.cbd585684296 from=translated src=- shape=c4e40d43 vocab=4465a859
-/
theorem K48_projOrder_cases : ∀ k ∈ K48, IsPM1 k ∨ IsProjOrder 2 k ∨ IsProjOrder 3 k ∨ IsProjOrder 4 k := by
  decide

/--
@isnad1 id=or.1h1v.s6.0a799aaec1b7 from=translated src=- shape=52e37c16 vocab=ca8a2a01
-/
theorem K48_det_cases : ∀ k ∈ K48, det2 k = 1 ∨ det2 k = -1 := by decide

/--
@isnad1 id=and.2h1v.s7.bfab415d0a60 from=translated src=- shape=127baad4 vocab=885dbdbd
-/
theorem K48_row_central : ∀ k ∈ K48, IsPM1 k → det2 k = 1 ∧ (tr2 k = 2 ∨ tr2 k = -2) := by decide

/--
@isnad1 id=eq.3h1v.s6.41daf7f9f4de from=translated src=- shape=37d036af vocab=c14b9377
-/
theorem K48_row_two_odd : ∀ k ∈ K48, IsProjOrder 2 k → det2 k = -1 → tr2 k = 0 := by decide

/--
@isnad1 id=and.3h1v.s7.8c64a4305f1d from=translated src=- shape=17875797 vocab=3d68107b
-/
theorem K48_row_two_even : ∀ k ∈ K48, IsProjOrder 2 k → det2 k = 1 → tr2 k = 0 ∧ pw k 4 = 1 := by decide

/--
@isnad1 id=and.2h1v.s6.29a225e00097 from=translated src=- shape=dace75be vocab=5b6b6461
-/
theorem K48_row_three : ∀ k ∈ K48, IsProjOrder 3 k → det2 k = 1 ∧ tr2 k * tr2 k = det2 k := by decide

/--
@isnad1 id=and.2h1v.s7.4abdd23e9fae from=translated src=- shape=a592e508 vocab=95ea42d8
-/
theorem K48_row_four : ∀ k ∈ K48, IsProjOrder 4 k → det2 k = -1 ∧ (tr2 k = ⟨0, 1⟩ ∨ tr2 k = ⟨0, -1⟩) := by
  decide

/--
@isnad1 id=and.2h1v.s9.eef5df8a1b20 from=translated src=- shape=6e958c8e vocab=7442e264
-/
theorem K48_row_four_classes : ∀ k ∈ K48, IsProjOrder 4 k →
    (tr2 k = ⟨0, 1⟩ → ∃ g ∈ K48, g * k = Tlift * g) ∧ (tr2 k = ⟨0, -1⟩ → ∃ g ∈ K48, g * k = -Tlift * g) := by
  decide

/--
@isnad1 id=and.0h0v.s8.d33b46d5aac3 from=translated src=- shape=8b6f1214 vocab=6b821ee6
-/
theorem K48_order8_pair :
    (∀ g ∈ K48, g * Tlift ≠ -Tlift * g) ∧ -Tlift ∈ K48 ∧ IsProjOrder 4 (-Tlift) ∧ (∀ k ∈ K48, -k ∈ K48) := by
  decide

/--
@isnad1 id=iff.1h1v.s5.d205f9e58764 from=translated src=- shape=3a62da7b vocab=65e25697
-/
theorem K48_star_trace_iff : ∀ k ∈ K48, star (tr2 k) = tr2 k ↔ ¬ IsProjOrder 4 k := by decide

/--
@isnad1 id=and.0h0v.s8.c32711e076bf from=translated src=- shape=75142c10 vocab=ff58fd5d
-/
theorem K48_rows_nonvacuous :
    (∃ k ∈ K48, IsProjOrder 3 k ∧ tr2 k ≠ 0) ∧
    (∃ k ∈ K48, IsProjOrder 4 k ∧ tr2 k * tr2 k ≠ det2 k) ∧
    (∃ k ∈ K48, IsProjOrder 2 k ∧ tr2 k ≠ ⟨0, 1⟩ ∧ tr2 k ≠ ⟨0, -1⟩) ∧
    (∃ k ∈ K48, IsProjOrder 2 k ∧ det2 k = -1) ∧ (∃ k ∈ K48, IsProjOrder 2 k ∧ det2 k = 1) := by
  decide

/--
@isnad1 id=and.0h0v.s10.0162072c0880 from=translated src=- shape=69c83a4f vocab=7baae1da
-/
theorem K48_census :
    (K48.filter IsPM1).length = 2 ∧
    (K48.filter fun k => IsProjOrder 2 k ∧ det2 k = -1).length = 12 ∧
    (K48.filter fun k => IsProjOrder 2 k ∧ det2 k = 1).length = 6 ∧
    (K48.filter (IsProjOrder 3)).length = 16 ∧
    (K48.filter (IsProjOrder 4)).length = 12 ∧
    (K48.filter fun k => tr2 k = 0).length = 18 ∧ (K48.filter fun k => tr2 k = 1).length = 8 ∧
    (K48.filter fun k => tr2 k = -1).length = 8 ∧ (K48.filter fun k => tr2 k = ⟨0, 1⟩).length = 6 ∧
    (K48.filter fun k => tr2 k = ⟨0, -1⟩).length = 6 ∧ (K48.filter fun k => tr2 k = 2).length = 1 ∧
    (K48.filter fun k => tr2 k = -2).length = 1 := by
  decide

def Q8 : List Mat := K48.filter fun k => det2 k = 1 ∧ pw k 4 = 1

/--
@isnad1 id=eq.0h0v.s3.4962148c48c8 from=translated src=- shape=b3c4969c vocab=641fbe27
-/
theorem length_Q8 : Q8.length = 8 := by decide

/--
@isnad1 id=or.1h1v.s4.e92128fc50ec from=translated src=- shape=cf144a5b vocab=f992c6bf
-/
theorem Q8_projOrder : ∀ q ∈ Q8, IsPM1 q ∨ IsProjOrder 2 q := by decide

/--
@isnad1 id=mem.0h0v.s5.4e46e7ffbe5f from=translated src=- shape=d52416c9 vocab=2fd2a81d
-/
theorem one_mem_Q8 : (1 : Mat) ∈ Q8 := by decide

/--
@isnad1 id=mem.2h2v.s7.38ebf7aaaf6f from=translated src=- shape=bf7dc4ab vocab=ac088f62
-/
theorem Q8_mul_closed : ∀ a ∈ Q8, ∀ b ∈ Q8, a * b ∈ Q8 := by decide

/--
@isnad1 id=and.1h1v.s7.04d67cc27673 from=translated src=- shape=416ab918 vocab=b4b2d10a
-/
theorem Q8_mul_cube : ∀ q ∈ Q8, q * pw q 3 = 1 ∧ pw q 3 ∈ Q8 := by decide

/--
@isnad1 id=ex.2h2v.s7.c6a2eb54e7cd from=translated src=- shape=fefcff45 vocab=0eb070b1
-/
theorem Q8_normal : ∀ g ∈ K48, ∀ q ∈ Q8, ∃ q' ∈ Q8, g * q = q' * g := by decide

def C4 : List Mat := [1, pw Tlift 2, pw Tlift 4, pw Tlift 6]

/--
@isnad1 id=mem.1h1v.s4.f75dfd407724 from=translated src=- shape=92d89710 vocab=eaab8035
-/
theorem C4_sub_Q8 : ∀ c ∈ C4, c ∈ Q8 := by decide

/--
@isnad1 id=mem.2h2v.s7.fa5003e8c695 from=translated src=- shape=bf7dc4ab vocab=b448a7ca
-/
theorem C4_mul_closed : ∀ a ∈ C4, ∀ b ∈ C4, a * b ∈ C4 := by decide

/--
@isnad1 id=and.0h0v.s6.e2166f2f2962 from=translated src=- shape=55bca3f9 vocab=f622a9fb
-/
theorem length_C4 : C4.length = 4 ∧ C4.Nodup ∧ (Q8.filter fun q => q ∈ C4).length = 4 := by decide

/--
@isnad1 id=and.2h2v.s8.ccba918bfc3b from=translated src=- shape=a6a7dcff vocab=dd61c9fc
-/
theorem C4_conj : ∀ x ∈ Q8, ∀ c ∈ C4, x * c * pw x 3 ∈ C4 ∧ (x ∉ C4 → x * c * pw x 3 = pw c 3) := by decide

abbrev GInt : Type := ℤ√(-1)

def psi (k : Mat) : GInt :=
  if k = 1 then 1 else if k = pw Tlift 2 then ⟨0, 1⟩ else if k = pw Tlift 4 then -1
  else if k = pw Tlift 6 then ⟨0, -1⟩ else 0

/--
@isnad1 id=eq.0h0v.s5.8bb631a626fb from=translated src=- shape=1ac31801 vocab=85ab4c82
-/
theorem psi_one : psi 1 = 1 := by decide

/--
@isnad1 id=eq.2h2v.s7.131e933786fc from=translated src=- shape=387e8619 vocab=2eebbd0a
-/
theorem psi_mul : ∀ a ∈ C4, ∀ b ∈ C4, psi (a * b) = psi a * psi b := by decide

/--
@isnad1 id=and.0h0v.s8.fd738fc038e8 from=translated src=- shape=b1e8a5dd vocab=cd82e3e5
-/
theorem psi_faithful :
    psi (pw Tlift 2) = ⟨0, 1⟩ ∧ (⟨0, 1⟩ : GInt) * ⟨0, 1⟩ = -1 ∧ (∀ a ∈ C4, psi a = 1 → a = 1) ∧
    (C4.map psi = [1, ⟨0, 1⟩, -1, ⟨0, -1⟩]) := by
  decide

/--
@isnad1 id=ex.2h1v.s7.45fa088550cf from=translated src=- shape=d48ecffa vocab=f1f9a284
-/
theorem psi_ne_psi_conj : ∀ x ∈ Q8, x ∉ C4 → ∃ c ∈ C4, psi (x * c * pw x 3) ≠ psi c := by decide

def indPsiNum (g : Mat) : GInt := (Q8.map fun x => psi (x * g * pw x 3)).sum

/--
@isnad1 id=and.1h1v.s6.4f67b3e142cd from=translated src=- shape=e428279d vocab=9a5386c2
-/
theorem indPsi_identity :
    ∀ g ∈ Q8, (tr2 g).im = 0 ∧ (indPsiNum g).im = 0 ∧ 4 * (tr2 g).re = (indPsiNum g).re := by decide

/--
@isnad1 id=or.1h1v.s8.55ff292c4bbb from=translated src=- shape=66eb5357 vocab=63c82000
-/
theorem Q8_trace_values : ∀ g ∈ Q8, (g = 1 ∧ tr2 g = 2) ∨ (g = -1 ∧ tr2 g = -2) ∨ (¬ IsPM1 g ∧ tr2 g = 0) := by
  decide

def P16 : List Mat := K48.filter fun g => ∃ t ∈ [Tlift, pw Tlift 3, pw Tlift 5, pw Tlift 7], g * Tlift = t * g

/--
@isnad1 id=eq.0h0v.s3.38db6ed2dfbd from=translated src=- shape=b3c4969c vocab=57e2631f
-/
theorem length_P16 : P16.length = 16 := by decide

/--
@isnad1 id=and.0h0v.s6.e43de111dd54 from=translated src=- shape=a6fab4bf vocab=91f425bc
-/
theorem one_mem_P16 : (1 : Mat) ∈ P16 ∧ Tlift ∈ P16 ∧ Slift ∉ P16 := by decide

/--
@isnad1 id=mem.2h2v.s7.8a88c37dc26a from=translated src=- shape=bf7dc4ab vocab=4f2d5991
-/
theorem P16_mul_closed : ∀ a ∈ P16, ∀ b ∈ P16, a * b ∈ P16 := by decide

/--
@isnad1 id=mem.1h1v.s4.170425f83b11 from=translated src=- shape=92d89710 vocab=4b47825c
-/
theorem Q8_sub_P16 : ∀ q ∈ Q8, q ∈ P16 := by decide

def cosetReps : List Mat := [1, Slift, Slift * Slift]

/--
@isnad1 id=perm.0h0v.s6.604b6fb1d134 from=translated src=- shape=efb065ae vocab=11c57f41
-/
theorem cosets_partition : ((cosetReps.flatMap fun g => P16.map fun p => g * p).Perm K48) := by decide

def fixedCosets (k : Mat) : ℕ := (cosetReps.filter fun g => ∃ p ∈ P16, k * g = g * p).length

/--
@isnad1 id=eq.2h1v.s4.8c1e9f41b310 from=translated src=- shape=b73d59ed vocab=4cd17eba
-/
theorem fixedCosets_row_four : ∀ k ∈ K48, IsProjOrder 4 k → fixedCosets k = 1 := by decide

/--
@isnad1 id=eq.2h1v.s4.1780291c8ce5 from=translated src=- shape=b73d59ed vocab=4cd17eba
-/
theorem fixedCosets_row_three : ∀ k ∈ K48, IsProjOrder 3 k → fixedCosets k = 0 := by decide

/--
@isnad1 id=eq.3h1v.s6.6171c3d91f63 from=translated src=- shape=58b13e09 vocab=584970fc
-/
theorem fixedCosets_row_two_odd : ∀ k ∈ K48, IsProjOrder 2 k → det2 k = -1 → fixedCosets k = 1 := by decide

/--
@isnad1 id=and.1h1v.s6.06ef8787162f from=translated src=- shape=e130af52 vocab=bf6b2995
-/
theorem fixedCosets_row_two_even_and_central :
    ∀ k ∈ K48, (IsProjOrder 2 k → det2 k = 1 → fixedCosets k = 3) ∧ (IsPM1 k → fixedCosets k = 3) := by
  decide

/--
@isnad1 id=iff.0h1v.s7.0994d7188041 from=translated src=- shape=2fa51d78 vocab=ab72ddd9
-/
theorem isPM1_iff (A : Mat) : IsPM1 A ↔ A = 1 ∨ A = -1 := Iff.rfl

/--
@isnad1 id=iff.0h2v.s8.4a9f44e6ab36 from=translated src=- shape=9eab872b vocab=a6b74e26
-/
theorem isProjOrder_iff (n : ℕ) (A : Mat) :
    IsProjOrder n A ↔ (A ^ n = 1 ∨ A ^ n = -1) ∧ ∀ m, 1 ≤ m → m < n → ¬ (A ^ m = 1 ∨ A ^ m = -1) := by
  unfold IsProjOrder IsPM1
  simp only [pw_eq_pow, List.mem_range'_1]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, fun m h1 h2 => h' m ⟨h1, by omega⟩⟩
  · rintro ⟨h, h'⟩
    exact ⟨h, fun m hm => h' m hm.1 (by omega)⟩

/--
@isnad1 id=and.1h1v.s9.4e327d7181cd from=translated src=- shape=4bbc1a65 vocab=8761da62
-/
theorem trace_table (k : Mat) (hk : k ∈ Submonoid.closure ({Slift, Tlift} : Set Mat)) :
    (IsProjOrder 2 k → k.trace = 0) ∧
    (IsProjOrder 3 k → k.det = 1 ∧ k.trace ^ 2 = k.det) ∧
    (IsProjOrder 4 k → k.det = -1 ∧ (k.trace = ⟨0, 1⟩ ∨ k.trace = ⟨0, -1⟩)) := by
  rw [mem_closure_iff_mem_K48] at hk
  rw [← det2_eq_det, ← tr2_eq_trace]
  refine ⟨fun h2 => ?_, fun h3 => ?_, fun h4 => K48_row_four k hk h4⟩
  · rcases K48_det_cases k hk with hd | hd
    · exact (K48_row_two_even k hk h2 hd).1
    · exact K48_row_two_odd k hk h2 hd
  · obtain ⟨hd, ht⟩ := K48_row_three k hk h3
    exact ⟨hd, by rw [sq]; exact ht⟩

/--
@isnad1 id=and.1h1v.s8.10ac430cbbf9 from=translated src=- shape=4c021f83 vocab=32081849
-/
theorem fixedCosets_table (k : Mat) (hk : k ∈ Submonoid.closure ({Slift, Tlift} : Set Mat)) :
    (IsProjOrder 4 k → fixedCosets k = 1) ∧ (IsProjOrder 3 k → fixedCosets k = 0) ∧
    (IsProjOrder 2 k → k.det = -1 → fixedCosets k = 1) ∧ (IsProjOrder 2 k → k.det = 1 → fixedCosets k = 3) ∧
    (IsPM1 k → fixedCosets k = 3) := by
  rw [mem_closure_iff_mem_K48] at hk
  rw [← det2_eq_det]
  exact ⟨fixedCosets_row_four k hk, fixedCosets_row_three k hk, fixedCosets_row_two_odd k hk,
    (fixedCosets_row_two_even_and_central k hk).1, (fixedCosets_row_two_even_and_central k hk).2⟩

/--
@isnad1 id=and.1h1v.s7.fae00022b284 from=translated src=- shape=30ef4d3b vocab=f465b907
-/
theorem trace_eq_indPsi (g : Mat) (hg : g ∈ Q8) :
    (g.trace).im = 0 ∧ (indPsiNum g).im = 0 ∧ 4 * (g.trace).re = (indPsiNum g).re := by
  rw [← tr2_eq_trace]; exact indPsi_identity g hg

section DetUniversal

variable {M : Type*} [CommGroup M]

abbrev G48 : Submonoid Mat := Submonoid.closure ({Slift, Tlift} : Set Mat)

/--
@isnad1 id=mem.0h0v.s7.c019b2750b38 from=translated src=- shape=81ae8f40 vocab=7d31a41a
-/
theorem Slift_mem_G48 : Slift ∈ G48 := Submonoid.subset_closure (by simp)

/--
@isnad1 id=mem.0h0v.s7.8b8ab403e800 from=translated src=- shape=81ae8f40 vocab=05028736
-/
theorem Tlift_mem_G48 : Tlift ∈ G48 := Submonoid.subset_closure (by simp)

abbrev sG : G48 := ⟨Slift, Slift_mem_G48⟩

abbrev tG : G48 := ⟨Tlift, Tlift_mem_G48⟩

/--
@isnad1 id=eq.0h0v.s10.30377aba3447 from=translated src=- shape=90796d49 vocab=03a68c5d
-/
theorem Slift_comm_witness :
    Slift * Slift * (Tlift * Slift * Tlift * Tlift) = Tlift * Slift * Tlift * Tlift * Slift := by decide

/--
@isnad1 id=eq.0h0v.s10.9b8b54288e2a from=translated src=- shape=1fa95ab9 vocab=03a68c5d
-/
theorem Tlift_sq_comm_witness :
    Tlift * Tlift * (Slift * Tlift * Tlift) * Slift = Slift * (Slift * Tlift * Tlift) := by decide

/--
@isnad1 id=eq.0h2v.s10.45a9db262733 from=translated src=- shape=40c1f9ac vocab=2929ce92
-/
theorem hom_Slift_eq_one (φ : G48 →* M) : φ sG = 1 := by
  have h : sG * sG * (tG * sG * tG * tG) = tG * sG * tG * tG * sG := Subtype.ext Slift_comm_witness
  have h' := congrArg φ h
  simp only [map_mul] at h'
  have e : φ sG * (φ sG * φ sG * (φ tG * φ tG * φ tG)) = 1 * (φ sG * φ sG * (φ tG * φ tG * φ tG)) := by
    calc φ sG * (φ sG * φ sG * (φ tG * φ tG * φ tG))
          = φ sG * φ sG * (φ tG * φ sG * φ tG * φ tG) := by ac_rfl
      _ = φ tG * φ sG * φ tG * φ tG * φ sG := h'
      _ = 1 * (φ sG * φ sG * (φ tG * φ tG * φ tG)) := by rw [one_mul]; ac_rfl
  exact mul_right_cancel e

/--
@isnad1 id=eq.0h2v.s11.7f474d26cb7b from=translated src=- shape=fb50c2da vocab=33516648
-/
theorem hom_Tlift_sq_eq_one (φ : G48 →* M) : φ tG * φ tG = 1 := by
  have h : tG * tG * (sG * tG * tG) * sG = sG * (sG * tG * tG) := Subtype.ext Tlift_sq_comm_witness
  have h' := congrArg φ h
  simp only [map_mul] at h'
  have e : φ tG * φ tG * (φ sG * φ sG * (φ tG * φ tG)) = 1 * (φ sG * φ sG * (φ tG * φ tG)) := by
    calc φ tG * φ tG * (φ sG * φ sG * (φ tG * φ tG))
          = φ tG * φ tG * (φ sG * φ tG * φ tG) * φ sG := by ac_rfl
      _ = φ sG * (φ sG * φ tG * φ tG) := h'
      _ = 1 * (φ sG * φ sG * (φ tG * φ tG)) := by rw [one_mul]; ac_rfl
  exact mul_right_cancel e

/--
@isnad1 id=eq.2h3v.s11.51aad607267c from=translated src=- shape=b6f8878a vocab=53632898
-/
theorem hom_evalWord (φ : G48 →* M) (hS : Slift.det = 1) (hT : Tlift.det = -1) (w : List (Fin 2)) :
    φ ⟨evalWord w, evalWord_mem_closure w⟩ = if (evalWord w).det = 1 then 1 else φ tG := by
  induction w with
  | nil =>
    have h1 : (⟨evalWord [], evalWord_mem_closure []⟩ : G48) = 1 := Subtype.ext rfl
    rw [h1, map_one, show evalWord [] = (1 : Mat) from rfl, Matrix.det_one, ite_eq_left rfl]
  | cons a w ih =>
    have hdet : (evalWord w).det = 1 ∨ (evalWord w).det = -1 := by
      rw [← det2_eq_det]
      exact K48_det_cases _ ((mem_closure_iff_mem_K48 _).1 (evalWord_mem_closure w))
    have hne : (-1 : ℤ√(-2)) ≠ 1 := by decide
    match a with
    | 0 =>
      have h0 : (⟨evalWord (0 :: w), evalWord_mem_closure (0 :: w)⟩ : G48) =
          sG * ⟨evalWord w, evalWord_mem_closure w⟩ := Subtype.ext rfl
      rw [h0, map_mul, hom_Slift_eq_one, one_mul, ih, show evalWord (0 :: w) = Slift * evalWord w from rfl,
        Matrix.det_mul, hS, one_mul]
    | 1 =>
      have h0 : (⟨evalWord (1 :: w), evalWord_mem_closure (1 :: w)⟩ : G48) =
          tG * ⟨evalWord w, evalWord_mem_closure w⟩ := Subtype.ext rfl
      rw [h0, map_mul, ih, show evalWord (1 :: w) = Tlift * evalWord w from rfl, Matrix.det_mul, hT]
      rcases hdet with h | h
      · rw [h, ite_eq_left rfl, mul_one, mul_one, ite_eq_right hne]
      · rw [h, ite_eq_right hne, neg_mul_neg, one_mul, ite_eq_left rfl, hom_Tlift_sq_eq_one]

/--
@isnad1 id=eq.2h3v.s11.9b9169afa196 from=translated src=- shape=20f006a3 vocab=d0b9cce7
-/
theorem hom_factors_through_det (φ : G48 →* M) (hS : Slift.det = 1) (hT : Tlift.det = -1) (k : G48) :
    φ k = if (k : Mat).det = 1 then 1 else φ tG := by
  obtain ⟨k, hk⟩ := k
  have hK : k ∈ K48 := (mem_closure_iff_mem_K48 k).1 hk
  rw [K48_eq_map_evalWord] at hK
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hK
  exact hom_evalWord φ hS hT w

/--
@isnad1 id=iff.3h3v.s11.fc827e31bbba from=translated src=- shape=b1e6a3c0 vocab=14b694a4
-/
theorem hom_eq_one_iff_det_eq_one (φ : G48 →* M) (hS : Slift.det = 1) (hT : Tlift.det = -1) (hφ : φ ≠ 1)
    (k : G48) : φ k = 1 ↔ (k : Mat).det = 1 := by
  have htG : φ tG ≠ 1 := fun h1 => hφ (MonoidHom.ext fun j => by
    rw [hom_factors_through_det φ hS hT j, h1, ite_self, MonoidHom.one_apply])
  rw [hom_factors_through_det φ hS hT k]
  constructor
  · intro h
    by_contra hd
    rw [ite_eq_right hd] at h
    exact htG h
  · intro h
    rw [ite_eq_left h]

end DetUniversal

end LanglandsTunnell.Lift48
