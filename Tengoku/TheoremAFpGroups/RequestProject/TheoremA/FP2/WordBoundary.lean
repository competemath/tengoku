module

public import Tengoku.TheoremAFpGroups.RequestProject.TheoremA.FP2.Augmentation
public import Tengoku.TheoremAFpGroups.RequestProject.TheoremA.RelPres.Class

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Word boundaries (Fox derivatives) via a semidirect product

Let `G` be a group, `x : Fin n → G` any tuple (no generation hypothesis) and
`q = FreeGroup.lift x : F → G`, `F = FreeGroup (Fin n)`.  With `Λ = ℤ[G]` acting on the left:

* `boundaryAct V : G →* MulAut (Multiplicative V)` is the action `v ↦ [g] • v` of `G` on a left
  `Λ`-module `V` (written multiplicatively), and `BdExt V = Multiplicative V ⋊ G` is Mathlib's
  semidirect product, with multiplication `(u,g)(v,h) = (u + [g]•v, g h)`.
* `wordHom x : F →* BdExt (FreeMod G n)` sends `a_i ↦ (e_i, x_i)`; its second coordinate is `q`
  (`right_wordHom`).
* `wordBoundary x u : FreeMod G n` is its first coordinate `D_x(u)`.

Main identities:
* `wordBoundary_one`, `wordBoundary_of : D(a_i) = e_i`,
  `wordBoundary_mul : D(u v) = D(u) + [q u] • D(v)`,
  `wordBoundary_inv : D(u⁻¹) = -([q(u)⁻¹] • D(u))`, `wordBoundary_of_inv`;
* `genBoundary_wordBoundary : d(D u) = [q u] - 1`;
* `wordBoundary_conj : q r = 1 → D(u r u⁻¹) = [q u] • D(r)`;
* raw-word versions `rawBoundary` with `rawBoundary_append`, `rawBoundary_inv`,
  `rawBoundary_pos`, `rawBoundary_neg`.
-/

@[expose] public section

namespace TheoremA

universe u v

variable {G : Type u} [Group G]

/-- Left multiplication by `[g]` on a left `ℤ[G]`-module, as a multiplicative automorphism of
`Multiplicative V`.-/
noncomputable def boundaryActAux (V : Type v) [AddCommGroup V] [Module (ZG G) V] (g : G) :
    MulAut (Multiplicative V) where
  toFun w := Multiplicative.ofAdd (MonoidAlgebra.of ℤ G g • w.toAdd)
  invFun w := Multiplicative.ofAdd (MonoidAlgebra.of ℤ G g⁻¹ • w.toAdd)
  left_inv w := by
    simp only [toAdd_ofAdd, smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul, ofAdd_toAdd]
  right_inv w := by
    simp only [toAdd_ofAdd, smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul, ofAdd_toAdd]
  map_mul' a b := by
    simp [smul_add]

/-- The action `g ↦ ([g] • ·)` of `G` on a left `ℤ[G]`-module `V`.-/
noncomputable def boundaryAct (V : Type v) [AddCommGroup V] [Module (ZG G) V] :
    G →* MulAut (Multiplicative V) where
  toFun := boundaryActAux V
  map_one' := by
    ext w; simp only [boundaryActAux, map_one, one_smul, ofAdd_toAdd]; rfl
  map_mul' g h := by
    ext w; simp [boundaryActAux, smul_smul]

/--
@isnad1 id=eq.0h4v.s9.875f161d48ae from=translated src=- shape=d7cbe6eb vocab=f39a4ff2
-/
@[simp] theorem boundaryAct_apply (V : Type v) [AddCommGroup V] [Module (ZG G) V] (g : G)
    (w : Multiplicative V) :
    boundaryAct V g w = Multiplicative.ofAdd (MonoidAlgebra.of ℤ G g • w.toAdd) := rfl

/-- The semidirect product `V ⋊ G` for a left `ℤ[G]`-module `V`:
`(u,g)(v,h) = (u + [g]•v, g h)`.-/
abbrev BdExt (G : Type u) [Group G] (V : Type v) [AddCommGroup V] [Module (ZG G) V] :=
  Multiplicative V ⋊[boundaryAct (G := G) V] G

/-- The first coordinate of `BdExt`, read additively.
@isnad1 id=eq.0h4v.s8.9a8d5857a779 from=translated src=- shape=0ec7607e vocab=e9b8ef62
-/
theorem BdExt.left_mul {V : Type v} [AddCommGroup V] [Module (ZG G) V] (a b : BdExt G V) :
    (a * b).left.toAdd = a.left.toAdd + MonoidAlgebra.of ℤ G a.right • b.left.toAdd := by
  rw [SemidirectProduct.mul_left]; rfl

/-- The map `BdExt V → BdExt W` induced by a `ℤ[G]`-linear map.-/
noncomputable def BdExt.map {V W : Type v} [AddCommGroup V] [Module (ZG G) V]
    [AddCommGroup W] [Module (ZG G) W] (f : V →ₗ[ZG G] W) : BdExt G V →* BdExt G W :=
  SemidirectProduct.map (AddMonoidHom.toMultiplicative f.toAddMonoidHom) (MonoidHom.id G)
    (fun g => by ext w; simp)

/--
@isnad1 id=eq.0h5v.s9.2263d62b1168 from=translated src=- shape=29608254 vocab=36337666
-/
@[simp] theorem BdExt.map_left {V W : Type v} [AddCommGroup V] [Module (ZG G) V]
    [AddCommGroup W] [Module (ZG G) W] (f : V →ₗ[ZG G] W) (a : BdExt G V) :
    (BdExt.map f a).left.toAdd = f a.left.toAdd := rfl

/--
@isnad1 id=eq.0h5v.s8.38ad0f674e50 from=translated src=- shape=46848fcc vocab=1cfb7448
-/
@[simp] theorem BdExt.map_right {V W : Type v} [AddCommGroup V] [Module (ZG G) V]
    [AddCommGroup W] [Module (ZG G) W] (f : V →ₗ[ZG G] W) (a : BdExt G V) :
    (BdExt.map f a).right = a.right := rfl

variable {n : ℕ}

/-- The standard basis vector `e_i` of `ℤ[G]^n`.-/
noncomputable abbrev stdBasis (G : Type u) [Group G] {n : ℕ} (i : Fin n) : FreeMod G n :=
  Pi.single i 1

/-- `Φ : F → V ⋊ G`, `a_i ↦ (e_i, x_i)`.-/
noncomputable def wordHom (x : Fin n → G) : FreeGroup (Fin n) →* BdExt G (FreeMod G n) :=
  FreeGroup.lift fun i => ⟨Multiplicative.ofAdd (stdBasis G i), x i⟩

/-- The second coordinate of `Φ` is `q = FreeGroup.lift x`.
@isnad1 id=eq.0h4v.s10.1b6484964724 from=translated src=- shape=e3a47fad vocab=4da908fd
-/
theorem right_wordHom (x : Fin n → G) (u : FreeGroup (Fin n)) :
    (wordHom x u).right = FreeGroup.lift x u := by
  have : SemidirectProduct.rightHom.comp (wordHom x) = FreeGroup.lift x := by
    ext i; simp [wordHom]
  exact DFunLike.congr_fun this u

/-- **The word boundary** `D_x(u) ∈ ℤ[G]^n`: the first coordinate of `Φ(u)`.-/
noncomputable def wordBoundary (x : Fin n → G) (u : FreeGroup (Fin n)) : FreeMod G n :=
  (wordHom x u).left.toAdd

/--
@isnad1 id=eq.0h3v.s6.e1e7343e5e44 from=translated src=- shape=8f22081e vocab=97982ec5
-/
@[simp] theorem wordBoundary_one (x : Fin n → G) : wordBoundary x 1 = 0 := by
  simp [wordBoundary]

/--
@isnad1 id=eq.0h4v.s5.756f631239d8 from=translated src=- shape=79bb0967 vocab=68282447
-/
@[simp] theorem wordBoundary_of (x : Fin n → G) (i : Fin n) :
    wordBoundary x (FreeGroup.of i) = stdBasis G i := by
  simp [wordBoundary, wordHom]

/-- `D(u v) = D(u) + [q u] • D(v)`.
@isnad1 id=eq.0h5v.s9.603f32a24c96 from=translated src=- shape=103ab18f vocab=94ee0ca4
-/
theorem wordBoundary_mul (x : Fin n → G) (u w : FreeGroup (Fin n)) :
    wordBoundary x (u * w) =
      wordBoundary x u + MonoidAlgebra.of ℤ G (FreeGroup.lift x u) • wordBoundary x w := by
  simp only [wordBoundary, map_mul, BdExt.left_mul, right_wordHom]

/-- `D(u⁻¹) = -([q(u)⁻¹] • D(u))`.
@isnad1 id=eq.0h4v.s9.f07e9278836d from=translated src=- shape=774c24c6 vocab=e7d5b8c9
-/
theorem wordBoundary_inv (x : Fin n → G) (u : FreeGroup (Fin n)) :
    wordBoundary x u⁻¹ =
      -(MonoidAlgebra.of ℤ G (FreeGroup.lift x u)⁻¹ • wordBoundary x u) := by
  have h := wordBoundary_mul x u⁻¹ u
  rw [inv_mul_cancel, wordBoundary_one, map_inv] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- `D(a_i⁻¹) = -([x_i⁻¹] • e_i)`.
@isnad1 id=eq.0h4v.s8.219bae86cef6 from=translated src=- shape=3240b2cc vocab=d7d9b63b
-/
theorem wordBoundary_of_inv (x : Fin n → G) (i : Fin n) :
    wordBoundary x (FreeGroup.of i)⁻¹ = -(MonoidAlgebra.of ℤ G (x i)⁻¹ • stdBasis G i) := by
  rw [wordBoundary_inv, wordBoundary_of, FreeGroup.lift_apply_of]

/-- `d(D u) = [q u] - 1`.
@isnad1 id=eq.0h4v.s9.c8967650422f from=translated src=- shape=47fdf6e5 vocab=aa932637
-/
theorem genBoundary_wordBoundary (x : Fin n → G) (u : FreeGroup (Fin n)) :
    genBoundary x (wordBoundary x u) = gm1 (FreeGroup.lift x u) := by
  induction u using FreeGroup.induction_on with
  | one => rw [wordBoundary_one, map_zero, map_one, gm1, map_one, sub_self]
  | of i => rw [wordBoundary_of, genBoundary_single, FreeGroup.lift_apply_of]
  | inv_of i _ =>
    rw [wordBoundary_of_inv, map_neg, map_smul, genBoundary_single, (FreeGroup.lift x).map_inv,
      FreeGroup.lift_apply_of]
    simp only [gm1, smul_eq_mul, mul_sub, ← map_mul, inv_mul_cancel, map_one, mul_one]
    abel
  | mul a b ha hb =>
    rw [wordBoundary_mul, map_add, map_smul, ha, hb, map_mul]
    simp only [gm1, smul_eq_mul, mul_sub, map_mul, mul_one]
    abel

/-- Conjugation formula: if `q r = 1` then `D(u r u⁻¹) = [q u] • D(r)`.
@isnad1 id=eq.1h5v.s9.eb68a5ae06d9 from=translated src=- shape=286ad2ff vocab=010c2d0c
-/
theorem wordBoundary_conj (x : Fin n → G) (u : FreeGroup (Fin n)) {r : FreeGroup (Fin n)}
    (hr : FreeGroup.lift x r = 1) :
    wordBoundary x (u * r * u⁻¹) = MonoidAlgebra.of ℤ G (FreeGroup.lift x u) • wordBoundary x r := by
  rw [wordBoundary_mul, wordBoundary_mul, wordBoundary_inv, map_mul, hr, mul_one,
    smul_neg, smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  abel

/-! ### Raw words -/

open RelPres

/-- The boundary of a raw word: `D_x(eval w)`.-/
noncomputable def rawBoundary (x : Fin n → G) (w : RawWord (Fin n)) : FreeMod G n :=
  wordBoundary x (RawWord.eval w)

/--
@isnad1 id=eq.0h3v.s6.6ce5e530b6be from=translated src=- shape=3b4448b5 vocab=53bcf169
-/
@[simp] theorem rawBoundary_nil (x : Fin n → G) : rawBoundary x [] = 0 := by
  simp [rawBoundary]

/--
@isnad1 id=eq.0h5v.s9.04446d98c915 from=translated src=- shape=f4bbb8bc vocab=cd3633ab
-/
theorem rawBoundary_append (x : Fin n → G) (v w : RawWord (Fin n)) :
    rawBoundary x (v ++ w) = rawBoundary x v +
      MonoidAlgebra.of ℤ G (FreeGroup.lift x (RawWord.eval v)) • rawBoundary x w := by
  simp only [rawBoundary, RawWord.eval_append, wordBoundary_mul]

/--
@isnad1 id=eq.0h4v.s9.32b5c32003a9 from=translated src=- shape=3f9d20e9 vocab=04c44c72
-/
theorem rawBoundary_inv (x : Fin n → G) (w : RawWord (Fin n)) :
    rawBoundary x (RawWord.inv w) =
      -(MonoidAlgebra.of ℤ G (FreeGroup.lift x (RawWord.eval w))⁻¹ • rawBoundary x w) := by
  simp only [rawBoundary, RawWord.eval_inv, wordBoundary_inv]

/--
@isnad1 id=eq.0h4v.s5.ee5694436b9e from=translated src=- shape=cd8fd489 vocab=e1d033a3
-/
@[simp] theorem rawBoundary_pos (x : Fin n → G) (i : Fin n) :
    rawBoundary x [(i, true)] = stdBasis G i := by
  simp [rawBoundary]

/--
@isnad1 id=eq.0h4v.s8.91cb800f85f6 from=translated src=- shape=8a1ce6c3 vocab=97eec28e
-/
@[simp] theorem rawBoundary_neg (x : Fin n → G) (i : Fin n) :
    rawBoundary x [(i, false)] = -(MonoidAlgebra.of ℤ G (x i)⁻¹ • stdBasis G i) := by
  simp only [rawBoundary, RawWord.eval_neg, wordBoundary_of_inv]

/--
@isnad1 id=eq.0h4v.s9.83f202e15041 from=translated src=- shape=23ed2abd vocab=89aa6b25
-/
theorem genBoundary_rawBoundary (x : Fin n → G) (w : RawWord (Fin n)) :
    genBoundary x (rawBoundary x w) = gm1 (FreeGroup.lift x (RawWord.eval w)) :=
  genBoundary_wordBoundary x _

end TheoremA
