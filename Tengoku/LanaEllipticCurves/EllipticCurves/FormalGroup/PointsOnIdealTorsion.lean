/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.PointsOnIdeal
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.MulByN

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `Ê(𝔪)` has no prime-to-`p` torsion

Let `A` be a commutative ring that is `I`-adically complete (`IsAdicComplete I A`; the case of a
complete DVR with maximal ideal `𝔪` and residue characteristic `p` is `I = 𝔪`) and let
`F : FormalGroup A`.  The ideal `I` carries the abelian group `Ê(𝔪) = F.OnIdeal I` with addition
`x ⊕ y = F(x, y)` (constructed in `PointsOnIdeal`).  Following Silverman (AEC IV.3 Thm 3.2(b),
VII.2.2) we prove that **multiplication by `m` is bijective whenever `(m : A)` is a unit** — in
particular for `m` coprime to the residue characteristic `p` — so `Ê(𝔪)` is uniquely `m`-divisible
and has no nontrivial prime-to-`p` torsion.

The proof rests on two bricks:

* the *multiplication-by-`n` series* `[n](z) = F.mulByN n` and its compositional inverse
  `[n]⁻¹ = mulByNInv` when `(n : A)` is a unit (`MulByN`);
* the `I`-adic evaluation `adicEval` and its *transport / composition* law
  `adicEval_subst : (f ∘ g)(x) = f(g(x))` (proved here from `PointsOnIdeal.adicEvalMv_subst`).

The key identification is `nsmul_val : (m • x).val = [m](x)`: the group-theoretic `m`-fold sum on
`Ê(𝔪)` is computed by `I`-adic substitution of the series `[m]`.  Composing with `[m]⁻¹` through
`adicEval_subst` then yields a two-sided inverse to `x ↦ m • x`.

## Main results

* `PowerSeries.adicEval_subst` — the univariate transport law for `adicEval`.
* `FormalGroup.OnIdeal.nsmul_val` — `(m • x).val = adicEval I x.property (F.mulByN m)`.
* `FormalGroup.OnIdeal.nsmul_bijective` — for `IsUnit (m : A)`, `x ↦ m • x` is bijective.
* `FormalGroup.OnIdeal.eq_zero_of_nsmul_eq_zero` — for `IsUnit (m : A)`, `m • x = 0 → x = 0`.

## References

Silverman, *The Arithmetic of Elliptic Curves*, IV.3 Thm 3.2, VII.2.2.
-/

open scoped Topology

noncomputable section

namespace PowerSeries

variable {A : Type*} [CommRing A] (I : Ideal A) [IsAdicComplete I A]

/-- `adicEval` at two equal points agree (the membership proof is irrelevant). -/
theorem adicEval_congr_point {x y : A} (hx : x ∈ I) (hy : y ∈ I) (h : x = y)
    (f : PowerSeries A) : adicEval I hx f = adicEval I hy f := by
  subst h; rfl

/-- **Transport / composition law for `I`-adic evaluation.**  Substituting `g` into `f` and then
evaluating `I`-adically at `x` equals evaluating `f` at the point `g(x)`: `(f ∘ g)(x) = f(g(x))`.
Derived from the multivariate transport lemma `PowerSeries.adicEvalMv_subst` in the univariate
(`Unit`-indexed) case. -/
theorem adicEval_subst {x : A} (hx : x ∈ I) {g : PowerSeries A} (hg : PowerSeries.HasSubst g)
    (hgc : constantCoeff g = 0) (f : PowerSeries A) :
    adicEval I hx (f.subst g) = adicEval I (adicEval_mem hx hgc) f := by
  rw [PowerSeries.subst_def, adicEval_eq_adicEvalMv I hx,
    adicEvalMv_subst I (fun _ : Unit => hx) hg.const (fun _ => hgc) f,
    adicEval_eq_adicEvalMv I (adicEval_mem hx hgc)]
  apply adicEvalMv_congr
  funext s
  exact (adicEval_eq_adicEvalMv I hx g).symm

end PowerSeries

namespace FormalGroup

variable {A : Type*} [CommRing A] {F : FormalGroup A} {I : Ideal A} [IsAdicComplete I A]

open PowerSeries

namespace OnIdeal

/-- **The multiplication-by-`m` series computes the `ℕ`-action on `Ê(𝔪)`.**  The `m`-fold group sum
`m • x` on `F.OnIdeal I` is the `I`-adic evaluation of the series `[m](z) = F.mulByN m` at `x`. -/
theorem nsmul_val (m : ℕ) (x : OnIdeal F I) :
    (m • x).val = adicEval I x.property (F.mulByN m) := by
  induction m with
  | zero => simp only [zero_nsmul, zero_val, mulByN_zero, map_zero]
  | succ k ih =>
    rw [succ_nsmul, add_val, mulByN_succ, adicEval_eq_adicEvalMv]
    unfold fgAdd
    rw [OnIdeal.fold (F := F) (fun _ : Unit => x.property)
      (hasSubst_cons (F.constantCoeff_mulByN k) PowerSeries.constantCoeff_X)
      (F.constantCoeff_mulByN k) PowerSeries.constantCoeff_X]
    refine adicEvalMv_congr I ?_ _ _ _
    funext s
    fin_cases s
    · change (k • x).val = adicEvalMv I (fun _ : Unit => x.property) (F.mulByN k)
      rw [ih, adicEval_eq_adicEvalMv]
    · change x.val = adicEvalMv I (fun _ : Unit => x.property) PowerSeries.X
      rw [PowerSeries.X_apply]
      exact (adicEvalMv_X I (fun _ : Unit => x.property) ()).symm

/-- The candidate inverse of multiplication-by-`m` on `Ê(𝔪)` when `(m : A)` is a unit: the `I`-adic
substitution of the compositional inverse series `[m]⁻¹ = mulByNInv`. -/
def divByUnit {m : ℕ} (hn : IsUnit (m : A)) (x : OnIdeal F I) : OnIdeal F I :=
  ⟨adicEval I x.property (mulByNInv (F := F) hn),
    adicEval_mem x.property (constantCoeff_mulByNInv hn)⟩

@[simp] theorem divByUnit_val {m : ℕ} (hn : IsUnit (m : A)) (x : OnIdeal F I) :
    (divByUnit hn x).val = adicEval I x.property (mulByNInv (F := F) hn) := rfl

/-- `divByUnit` is a left inverse of multiplication-by-`m`: `[m]⁻¹([m](x)) = x`. -/
theorem divByUnit_nsmul {m : ℕ} (hn : IsUnit (m : A)) (x : OnIdeal F I) :
    divByUnit hn (m • x) = x := by
  apply OnIdeal.ext
  change adicEval I (m • x).property (mulByNInv (F := F) hn) = x.val
  rw [adicEval_congr_point I (m • x).property
      (adicEval_mem x.property (F.constantCoeff_mulByN m)) (nsmul_val m x),
    ← adicEval_subst I x.property (hasSubst_mulByN F m) (F.constantCoeff_mulByN m)
      (mulByNInv (F := F) hn),
    subst_mulByNInv_left hn, adicEval_X]

/-- `divByUnit` is a right inverse of multiplication-by-`m`: `[m]([m]⁻¹(x)) = x`. -/
theorem nsmul_divByUnit {m : ℕ} (hn : IsUnit (m : A)) (x : OnIdeal F I) :
    m • divByUnit hn x = x := by
  apply OnIdeal.ext
  rw [nsmul_val m (divByUnit hn x)]
  change adicEval I (adicEval_mem x.property (constantCoeff_mulByNInv hn)) (F.mulByN m) = x.val
  rw [← adicEval_subst I x.property (hasSubst_mulByNInv hn) (constantCoeff_mulByNInv hn)
      (F.mulByN m), subst_mulByNInv_right hn, adicEval_X]

/-- **Multiplication-by-`m` is bijective on `Ê(𝔪)` when `(m : A)` is a unit.**  In particular for
`m` coprime to the residue characteristic, `Ê(𝔪)` is uniquely `m`-divisible.  (Silverman AEC
IV.3 Thm 3.2(b), VII.2.2.) -/
theorem nsmul_bijective {m : ℕ} (hn : IsUnit (m : A)) :
    Function.Bijective (fun x : OnIdeal F I => m • x) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨divByUnit hn, divByUnit_nsmul hn, nsmul_divByUnit hn⟩

/-- Multiplication-by-`m` is injective on `Ê(𝔪)` when `(m : A)` is a unit. -/
theorem nsmul_injective {m : ℕ} (hn : IsUnit (m : A)) :
    Function.Injective (fun x : OnIdeal F I => m • x) :=
  (nsmul_bijective hn).injective

/-- Multiplication-by-`m` is surjective on `Ê(𝔪)` when `(m : A)` is a unit: `Ê(𝔪)` is
`m`-divisible. -/
theorem nsmul_surjective {m : ℕ} (hn : IsUnit (m : A)) :
    Function.Surjective (fun x : OnIdeal F I => m • x) :=
  (nsmul_bijective hn).surjective

/-- **`Ê(𝔪)` has no nontrivial prime-to-`p` torsion.**  When `(m : A)` is a unit (e.g. `m` coprime
to the residue characteristic `p`), the only `m`-torsion point is `0`.  This is the torsion-freeness
input consumed by the injectivity of reduction on prime-to-`p` torsion. -/
theorem eq_zero_of_nsmul_eq_zero {m : ℕ} (hn : IsUnit (m : A)) {x : OnIdeal F I}
    (h : m • x = 0) : x = 0 := by
  refine nsmul_injective hn ?_
  change m • x = m • (0 : OnIdeal F I)
  rw [h, smul_zero]

end OnIdeal

end FormalGroup

end
