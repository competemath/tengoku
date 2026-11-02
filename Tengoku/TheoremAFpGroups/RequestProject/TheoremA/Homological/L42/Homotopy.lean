module

public import Tengoku.TheoremAFpGroups.RequestProject.TheoremA.Homological.L42.Tensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lemma 4.2, part 2: the contracting homotopy of `F ⊗_ℤ F`

From the integral contraction `σ` of `F` we build `Σ = σ ⊗ 1 + ιε ⊗ σ` on bigraded families and
compute `DΣ + ΣD` componentwise.  Consequences: cycles of total degree `1, …, k` are boundaries
(`DΣz = z`), and in degree `0` and `m = k + 1` we identify the correction terms.
-/

@[expose] public section

namespace TheoremA

open TensorProduct

universe u

variable {B : Type u} [Group B] {k : ℕ}

namespace L42

variable {R : Res B k} (C : Contr R)

/-- `x ↦ ε(x) x₀`.-/
noncomputable def ιε : F R 0 →ₗ[ℤ] F R 0 := (LinearMap.toSpanSingleton ℤ (F R 0) C.x0) ∘ₗ εZ R

@[simp] theorem ιε_apply (x : F R 0) : ιε C x = R.ε x • C.x0 := rfl

theorem c0' : dZ R 0 ∘ₗ C.σ 0 + ιε C = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, ιε_apply, LinearMap.id_apply]
  exact C.c0 x

theorem ci' (i : ℕ) (hi : i < k) :
    dZ R (i + 1) ∘ₗ C.σ (i + 1) + C.σ i ∘ₗ dZ R i = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply]
  exact C.ci i hi x

theorem ιε_dZ : ιε C ∘ₗ dZ R 0 = 0 := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, ιε_apply, LinearMap.zero_apply]
  rw [show R.ε (dZ R 0 x) = 0 from R.ε_d x, zero_smul]

theorem ιε_ιε : ιε C ∘ₗ ιε C = ιε C := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, ιε_apply, map_zsmul, C.hx0, one_smul]

/-- The raw components of `Σ z`.-/
noncomputable def SigF (z : Qm R) : ∀ p q, T R p q
  | p + 1, q => map (C.σ p) LinearMap.id (z p q)
  | 0, q + 1 => map (ιε C) (C.σ q) (z 0 q)
  | 0, 0 => 0

/-- The contracting homotopy `Σ`.-/
noncomputable def Sig : Qm R →+ Qm R where
  toFun := SigF C
  map_zero' := by
    funext p q; rcases p with _ | p <;> rcases q with _ | q <;> simp [SigF]
  map_add' z w := by
    funext p q; rcases p with _ | p <;> rcases q with _ | q <;> simp [SigF]

@[simp] theorem Sig_succ (z : Qm R) (p q : ℕ) :
    Sig C z (p + 1) q = map (C.σ p) LinearMap.id (z p q) := rfl
@[simp] theorem Sig_zero_succ (z : Qm R) (q : ℕ) :
    Sig C z 0 (q + 1) = map (ιε C) (C.σ q) (z 0 q) := rfl
@[simp] theorem Sig_zero_zero (z : Qm R) : Sig C z 0 0 = 0 := rfl

/-- `z` is concentrated in total degree `n`.-/
def IsDeg (n : ℕ) (z : Qm R) : Prop := ∀ p q, p + q ≠ n → z p q = 0

theorem IsDeg.Sig {n : ℕ} {z : Qm R} (h : IsDeg n z) : IsDeg (n + 1) (Sig C z) := by
  intro p q hpq
  rcases p with _ | p <;> rcases q with _ | q
  · rfl
  · simp [h 0 q (by omega)]
  · simp [h p 0 (by omega)]
  · simp [h p (q + 1) (by omega)]

theorem IsDeg.D {n : ℕ} {z : Qm R} (h : IsDeg (n + 1) z) : IsDeg n (D R z) := by
  intro p q hpq
  simp [D_apply, h (p + 1) q (by omega), h p (q + 1) (by omega)]

theorem IsDeg.actQ {n : ℕ} {z : Qm R} (h : IsDeg n z) (b c : B) : IsDeg n (actQ R b c z) := by
  intro p q hpq; simp [h p q hpq]

theorem sign_succ (i : ℕ) {M : Type*} [AddCommGroup M] (x : M) :
    ((-1 : ℤ) ^ (i + 1)) • x = -(((-1 : ℤ) ^ i) • x) := by
  rw [pow_succ, mul_neg_one, neg_smul]

theorem map_add_id {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    (a b : M →ₗ[ℤ] P) (g : N →ₗ[ℤ] N) (t : M ⊗[ℤ] N) :
    map a g t + map b g t = map (a + b) g t := by
  rw [map_add_left]; rfl

theorem map_id_add {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    (f : M →ₗ[ℤ] M) (a b : N →ₗ[ℤ] P) (t : M ⊗[ℤ] N) :
    map f a t + map f b t = map f (a + b) t := by
  rw [map_add_right]; rfl

end L42

end TheoremA
