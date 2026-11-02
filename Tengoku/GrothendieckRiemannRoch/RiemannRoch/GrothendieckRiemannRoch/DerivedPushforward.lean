/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.KTheory.Presentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Derived pushforward from finite long exact cohomology sequences

The higher direct images of a short exact sequence do not form short exact sequences degree by
degree.  They form a long exact sequence, and its finite alternating sum is additive.  This file
implements that argument in an arbitrary additive commutative group and then uses the universal
property of an exact Grothendieck group to construct a derived pushforward homomorphism.

The geometric layer must supply the actual higher-direct-image classes, a uniform vanishing
bound, and the image/coimage decompositions encoded by `LongExactWitness`.  Additivity of the
resulting virtual pushforward is proved here rather than assumed.
-/

noncomputable section

open scoped BigOperators

universe u v w

namespace GrothendieckRiemannRoch

variable {A : Type v} [AddCommGroup A]

/-- The finite alternating sum through degree `n`.-/
def alternatingSum (n : ℕ) (term : ℕ → A) : A :=
  ∑ i ∈ Finset.range (n + 1), ((-1 : ℤ) ^ i) • term i

/-- Additive homomorphisms commute with finite alternating sums.-/
theorem map_alternatingSum {B : Type w} [AddCommGroup B] (f : A →+ B)
    (n : ℕ) (term : ℕ → A) :
    f (alternatingSum n term) = alternatingSum n (fun i => f (term i)) := by
  simp [alternatingSum]

/-- Adjacent boundary terms cancel in an alternating sum.  The displayed endpoint is retained
so that the actual bounded long-exact-sequence theorem only has to set it to zero.-/
theorem alternating_boundary_sum (w : ℕ → A) (hzero : w 0 = 0) (n : ℕ) :
    (∑ i ∈ Finset.range n, ((-1 : ℤ) ^ i) • (w i + w (i + 1))) =
      -(((-1 : ℤ) ^ n) • w n) := by
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hsign : ((-1 : ℤ) ^ (n + 1)) = -((-1 : ℤ) ^ n) := by
        rw [pow_succ]
        simp
      rw [hsign]
      simp only [smul_add, neg_smul]
      abel

/-- Image-class data for a finite long exact sequence
`Aᵢ → Bᵢ → Cᵢ → Aᵢ₊₁`.

Here `uᵢ`, `vᵢ`, and `wᵢ` are the successive image classes.  The three decomposition equations
are precisely the short-exact relations obtained from kernels and images.-/
structure LongExactWitness (n : ℕ) (a b c : ℕ → A) where
  /-- Image class of `Aᵢ → Bᵢ`.-/
  u : ℕ → A
  /-- Image class of `Bᵢ → Cᵢ`.-/
  v : ℕ → A
  /-- Image class of `Cᵢ₋₁ → Aᵢ`.-/
  w : ℕ → A
  /-- The incoming image in degree zero vanishes.-/
  leftBoundary : w 0 = 0
  /-- The outgoing image after the chosen vanishing bound vanishes.-/
  rightBoundary : w (n + 1) = 0
  /-- Kernel/image decomposition of `Aᵢ`.-/
  leftDecomposition : ∀ i, a i = w i + u i
  /-- Kernel/image decomposition of `Bᵢ`.-/
  middleDecomposition : ∀ i, b i = u i + v i
  /-- Kernel/image decomposition of `Cᵢ`.-/
  rightDecomposition : ∀ i, c i = v i + w (i + 1)

/-- A bounded long exact sequence gives additivity of finite alternating sums.-/
theorem LongExactWitness.euler_additive {n : ℕ} {a b c : ℕ → A}
    (W : LongExactWitness n a b c) :
    alternatingSum n b = alternatingSum n a + alternatingSum n c := by
  unfold alternatingSum
  have hb :
      (∑ i ∈ Finset.range (n + 1), ((-1 : ℤ) ^ i) • b i) =
        ∑ i ∈ Finset.range (n + 1), ((-1 : ℤ) ^ i) • (W.u i + W.v i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [W.middleDecomposition]
  have ha :
      (∑ i ∈ Finset.range (n + 1), ((-1 : ℤ) ^ i) • a i) =
        ∑ i ∈ Finset.range (n + 1), ((-1 : ℤ) ^ i) • (W.w i + W.u i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [W.leftDecomposition]
  have hc :
      (∑ i ∈ Finset.range (n + 1), ((-1 : ℤ) ^ i) • c i) =
        ∑ i ∈ Finset.range (n + 1), ((-1 : ℤ) ^ i) • (W.v i + W.w (i + 1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [W.rightDecomposition]
  rw [hb, ha, hc]
  have hboundary :
      (∑ i ∈ Finset.range (n + 1),
        ((-1 : ℤ) ^ i) • (W.w i + W.w (i + 1))) = 0 := by
    rw [alternating_boundary_sum W.w W.leftBoundary]
    rw [W.rightBoundary]
    simp
  let su : A := ∑ i ∈ Finset.range (n + 1), ((-1 : ℤ) ^ i) • W.u i
  let sv : A := ∑ i ∈ Finset.range (n + 1), ((-1 : ℤ) ^ i) • W.v i
  let sw : A := ∑ i ∈ Finset.range (n + 1), ((-1 : ℤ) ^ i) • W.w i
  let sw' : A := ∑ i ∈ Finset.range (n + 1), ((-1 : ℤ) ^ i) • W.w (i + 1)
  have huv :
      (∑ i ∈ Finset.range (n + 1), ((-1 : ℤ) ^ i) • (W.u i + W.v i)) =
        su + sv := by
    simp only [smul_add, Finset.sum_add_distrib]
    rfl
  have hwu :
      (∑ i ∈ Finset.range (n + 1), ((-1 : ℤ) ^ i) • (W.w i + W.u i)) =
        sw + su := by
    simp only [smul_add, Finset.sum_add_distrib]
    rfl
  have hvw :
      (∑ i ∈ Finset.range (n + 1), ((-1 : ℤ) ^ i) • (W.v i + W.w (i + 1))) =
        sv + sw' := by
    simp only [smul_add, Finset.sum_add_distrib]
    rfl
  rw [huv, hwu, hvw]
  have hbnd : sw + sw' = 0 := by
    dsimp only [sw, sw']
    simpa only [smul_add, Finset.sum_add_distrib] using hboundary
  calc
    su + sv = su + sv + (sw + sw') := by rw [hbnd, add_zero]
    _ = (sw + su) + (sv + sw') := by abel

variable {Object : Type u} {Exact : Object → Object → Object → Prop}

/-- Derived pushforward on an exact Grothendieck group, constructed from bounded higher-image
classes and their long exact sequences.-/
def derivedPushforward (n : ℕ) (higherClass : Object → ℕ → A)
    (hlong : ∀ X Y Z, Exact X Y Z →
      LongExactWitness n (higherClass X) (higherClass Y) (higherClass Z)) :
    ExactGrothendieck.Group Object Exact →+ A :=
  ExactGrothendieck.lift (fun X => alternatingSum n (higherClass X)) fun X Y Z h =>
    (hlong X Y Z h).euler_additive

@[simp]
theorem derivedPushforward_classOf (n : ℕ) (higherClass : Object → ℕ → A)
    (hlong : ∀ X Y Z, Exact X Y Z →
      LongExactWitness n (higherClass X) (higherClass Y) (higherClass Z))
    (X : Object) :
    derivedPushforward n higherClass hlong (ExactGrothendieck.classOf Object Exact X) =
      alternatingSum n (higherClass X) :=
  ExactGrothendieck.lift_classOf _ _ _

/-- Degreewise derived base change implies a commuting square for the constructed virtual
derived pushforwards.-/
theorem derivedPushforward_baseChange_of_degreewise
    {Object' : Type v} {Exact' : Object' → Object' → Object' → Prop}
    {B : Type w} [AddCommGroup B]
    (n : ℕ) (higherClass : Object → ℕ → A)
    (higherClass' : Object' → ℕ → B)
    (hlong : ∀ X Y Z, Exact X Y Z →
      LongExactWitness n (higherClass X) (higherClass Y) (higherClass Z))
    (hlong' : ∀ X Y Z, Exact' X Y Z →
      LongExactWitness n (higherClass' X) (higherClass' Y) (higherClass' Z))
    (pullObject : Object → Object')
    (hpull : ∀ X Y Z, Exact X Y Z →
      Exact' (pullObject X) (pullObject Y) (pullObject Z))
    (pullTarget : A →+ B)
    (hdegree : ∀ X i, pullTarget (higherClass X i) = higherClass' (pullObject X) i) :
    pullTarget.comp (derivedPushforward n higherClass hlong) =
      (derivedPushforward n higherClass' hlong').comp
        (ExactGrothendieck.map pullObject hpull) := by
  apply ExactGrothendieck.hom_ext Object Exact
  intro X
  simp only [AddMonoidHom.comp_apply, derivedPushforward_classOf,
    ExactGrothendieck.map_classOf]
  rw [map_alternatingSum]
  congr 1
  funext i
  exact hdegree X i

end GrothendieckRiemannRoch
