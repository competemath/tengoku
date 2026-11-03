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

/--
@isnad1 id=eq.0h5v.s9.4f1bdaa2f6ac from=translated src=- shape=d487800a vocab=83f62d2f
-/
@[simp] theorem ιε_apply (x : F R 0) : ιε C x = R.ε x • C.x0 := rfl

/--
@isnad1 id=eq.0h4v.s10.035d4f5c2d4f from=translated src=- shape=3eb9327b vocab=d407eac4
-/
theorem c0' : dZ R 0 ∘ₗ C.σ 0 + ιε C = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, ιε_apply, LinearMap.id_apply]
  exact C.c0 x

/--
@isnad1 id=eq.1h5v.s11.254f2b8fbf68 from=translated src=- shape=47f0c9b5 vocab=935dd4fa
-/
theorem ci' (i : ℕ) (hi : i < k) :
    dZ R (i + 1) ∘ₗ C.σ (i + 1) + C.σ i ∘ₗ dZ R i = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply]
  exact C.ci i hi x

/--
@isnad1 id=eq.0h4v.s10.fb70ea288440 from=translated src=- shape=d57616bb vocab=25dc15f9
-/
theorem ιε_dZ : ιε C ∘ₗ dZ R 0 = 0 := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, ιε_apply, LinearMap.zero_apply]
  rw [show R.ε (dZ R 0 x) = 0 from R.ε_d x, zero_smul]

/--
@isnad1 id=eq.0h4v.s9.2162bb01bb0e from=translated src=- shape=082b01a7 vocab=4055d16e
-/
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

/--
@isnad1 id=eq.0h7v.s12.dc5b588c3d83 from=translated src=- shape=58ac74cd vocab=79b2ecaf
-/
@[simp] theorem Sig_succ (z : Qm R) (p q : ℕ) :
    Sig C z (p + 1) q = map (C.σ p) LinearMap.id (z p q) := rfl
/--
@isnad1 id=eq.0h6v.s12.4cfe730cce33 from=translated src=- shape=5ef6a91b vocab=d52057ff
-/
@[simp] theorem Sig_zero_succ (z : Qm R) (q : ℕ) :
    Sig C z 0 (q + 1) = map (ιε C) (C.σ q) (z 0 q) := rfl
/--
@isnad1 id=eq.0h5v.s10.d70a4693882e from=translated src=- shape=1dcce76e vocab=503275e1
-/
@[simp] theorem Sig_zero_zero (z : Qm R) : Sig C z 0 0 = 0 := rfl

/-- `z` is concentrated in total degree `n`.-/
def IsDeg (n : ℕ) (z : Qm R) : Prop := ∀ p q, p + q ≠ n → z p q = 0

/--
@isnad1 id=isdeg.1h6v.s9.529f1377fa98 from=translated src=- shape=13724669 vocab=817f3700
-/
theorem IsDeg.Sig {n : ℕ} {z : Qm R} (h : IsDeg n z) : IsDeg (n + 1) (Sig C z) := by
  intro p q hpq
  rcases p with _ | p <;> rcases q with _ | q
  · rfl
  · simp [h 0 q (by omega)]
  · simp [h p 0 (by omega)]
  · simp [h p (q + 1) (by omega)]

/--
@isnad1 id=isdeg.1h5v.s9.7895bca2b277 from=translated src=- shape=e7e215e2 vocab=70eaa590
-/
theorem IsDeg.D {n : ℕ} {z : Qm R} (h : IsDeg (n + 1) z) : IsDeg n (D R z) := by
  intro p q hpq
  simp [D_apply, h (p + 1) q (by omega), h p (q + 1) (by omega)]

/--
@isnad1 id=isdeg.1h7v.s9.6eddcb84b4d7 from=translated src=- shape=48895f51 vocab=84ad6ab2
-/
theorem IsDeg.actQ {n : ℕ} {z : Qm R} (h : IsDeg n z) (b c : B) : IsDeg n (actQ R b c z) := by
  intro p q hpq; simp [h p q hpq]

/--
@isnad1 id=eq.0h3v.s6.e9bc69ac6cb3 from=translated src=- shape=25301722 vocab=95d20907
-/
theorem sign_succ (i : ℕ) {M : Type*} [AddCommGroup M] (x : M) :
    ((-1 : ℤ) ^ (i + 1)) • x = -(((-1 : ℤ) ^ i) • x) := by
  rw [pow_succ, mul_neg_one, neg_smul]

/--
@isnad1 id=eq.0h7v.s10.7677bf9d8ea5 from=translated src=- shape=37a30e93 vocab=697449cd
-/
theorem map_add_id {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    (a b : M →ₗ[ℤ] P) (g : N →ₗ[ℤ] N) (t : M ⊗[ℤ] N) :
    map a g t + map b g t = map (a + b) g t := by
  rw [map_add_left]; rfl

/--
@isnad1 id=eq.0h7v.s10.bec0847391b8 from=translated src=- shape=7660f7f5 vocab=697449cd
-/
theorem map_id_add {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    (f : M →ₗ[ℤ] M) (a b : N →ₗ[ℤ] P) (t : M ⊗[ℤ] N) :
    map f a t + map f b t = map f (a + b) t := by
  rw [map_add_right]; rfl

end L42

end TheoremA
