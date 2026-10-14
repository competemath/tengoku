/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Tengoku

public import Tengoku.LeanPool.LeanPool.ComputableReal.AuxLemmas

/-!
# Interval-Cauchy real sequences

A `ComputableℝSeq` carries a sequence of rational intervals (`ℚInterval`) that
converge to a single real number, with proofs that the lower and upper rational
bounds are valid and Cauchy-equivalent. This file develops the basic interval
arithmetic on `ℚInterval` and the algebraic operations (addition, negation,
multiplication, inversion) on `ComputableℝSeq`, culminating in a commutative
semiring structure.

The interval sequence is an arbitrary function `ℕ → ℚInterval`, with no recursiveness
requirement, so membership in this type is not computability in the computable-analysis
sense. Addition, negation, and multiplication are executable interval arithmetic, while
`sign` (and hence inversion and division, which need a nonzero witness) is defined
classically and is `noncomputable`.
-/

@[expose] public section

namespace QInterval

/-- Notation `ℚInterval` for a nonempty rational interval. -/
scoped notation "ℚInterval" => NonemptyInterval ℚ

/-- A real lies in a `ℚInterval` when it is between the lower and upper bounds. -/
scoped instance (priority := 100) instMemℝℚInterval : Membership ℝ ℚInterval :=
  ⟨fun s a => s.fst ≤ a ∧ a ≤ s.snd⟩

section mul
/-- Multiplication on intervals of ℚ. TODO: Should generalize to any LinearOrderedField... -/
def mulPair (x y : ℚInterval) : ℚInterval :=
  let ⟨⟨xl,xu⟩,_⟩ := x
  let ⟨⟨yl,yu⟩,_⟩ := y
  ⟨⟨min (min (xl*yl) (xu*yl)) (min (xl*yu) (xu*yu)),
    max (max (xl*yl) (xu*yl)) (max (xl*yu) (xu*yu))⟩,
    by simp only [le_max_iff, min_le_iff, le_refl, true_or, or_true, or_self]⟩

/-- Multiplication of intervals by a ℚ. TODO: Should generalize to any LinearOrderedField -/
def mulQ (x : ℚInterval) (y : ℚ) : ℚInterval :=
  if h : y ≥ 0 then
    ⟨⟨x.fst * y, x.snd * y⟩, by dsimp; nlinarith [x.2]⟩
  else
    ⟨⟨x.snd * y, x.fst * y⟩, by dsimp; nlinarith [x.2]⟩

/-- Interval multiplication on `ℚInterval`. -/
scoped instance instMulQInterval : Mul (ℚInterval) :=
  ⟨mulPair⟩

/-- Multiplication of a `ℚInterval` by a rational scalar. -/
scoped instance instHMulQIntervalQ : HMul (ℚInterval) ℚ (ℚInterval) :=
  ⟨mulQ⟩

/-- Division of a `ℚInterval` by a rational scalar. -/
scoped instance instHDivQIntervalQ : HDiv (ℚInterval) ℚ (ℚInterval) :=
  ⟨fun x y ↦ x * y⁻¹⟩

private theorem multiplication_bounds {a x b : ℝ} (c : ℝ) (hax : a ≤ x) (hxb : x ≤ b) :
    min (a * c) (b * c) ≤ x * c ∧ x * c ≤ max (a * c) (b * c) := by
  rcases le_total 0 c with hc | hc
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hax hc),
      (mul_le_mul_of_nonneg_right hxb hc).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hxb hc),
      (mul_le_mul_of_nonpos_right hax hc).trans (le_max_left _ _)⟩

private theorem mulPair_bounds {x y : ℚInterval} {xv yv : ℝ} (hx : xv ∈ x) (hy : yv ∈ y) :
    (mulPair x y).fst ≤ xv * yv ∧ xv * yv ≤ (mulPair x y).snd := by
  obtain ⟨hxl, hxu⟩ := hx
  obtain ⟨hyl, hyu⟩ := hy
  have hl := multiplication_bounds (x.fst : ℝ) hyl hyu
  have hu := multiplication_bounds (x.snd : ℝ) hyl hyu
  have h := multiplication_bounds yv hxl hxu
  dsimp [mulPair]
  push_cast
  rw [min_min_min_comm, max_max_max_comm]
  simp only [mul_comm] at hl hu h ⊢
  exact ⟨(min_le_min hl.1 hu.1).trans h.1, h.2.trans (max_le_max hl.2 hu.2)⟩

/--
@isnad1 id=le.2h4v.s5.38ce612f808f from=translated src=- shape=5fbb5c4a vocab=02606cfc
-/
theorem mulPair_lb_is_lb {x y : ℚInterval} : ∀ xv ∈ x, ∀ yv ∈ y,
    (mulPair x y).fst ≤ xv * yv := by
  intro xv hx yv hy
  exact (mulPair_bounds hx hy).1

/--
@isnad1 id=le.2h4v.s5.4a03297fb768 from=translated src=- shape=5fbb5c4a vocab=b7e995e6
-/
theorem mulPair_ub_is_ub {x y : ℚInterval} : ∀ xv ∈ x, ∀ yv ∈ y,
    (mulPair x y).snd ≥ xv * yv := by
  intro xv hx yv hy
  exact (mulPair_bounds hx hy).2

/--
@isnad1 id=mem.2h4v.s5.589d19e5e621 from=translated src=- shape=9ffbcb13 vocab=5036b6a1
-/
theorem mem_mulPair {x y : ℚInterval} : ∀ xv ∈ x, ∀ yv ∈ y, xv * yv ∈ mulPair x y :=
  fun _ hx _ hy ↦ ⟨mulPair_lb_is_lb _ hx _ hy, mulPair_ub_is_ub _ hx _ hy⟩

end mul

/-- The constant interval at a rational number. -/
scoped instance instRatCastQInterval : RatCast ℚInterval :=
  ⟨fun q ↦ NonemptyInterval.pure q⟩

/-- The constant interval at a numeric literal. -/
scoped instance instOfNatQInterval : OfNat ℚInterval n :=
  ⟨NonemptyInterval.pure n⟩

end QInterval

/-- Structure for sequences that converge to some real number from above and below. `lub` is a
  function that gives upper *and* lower bounds, bundled so it can reuse computation; it is an
  arbitrary function `ℕ → ℚInterval`, with no recursiveness requirement. `hcl` and `hcu`
  assert that the two bounds are Cauchy sequences, `hlub` asserts that they're valid
  lower and upper bounds, and `heq'` asserts that they converge to a common value. Use
  `ComputableℝSeq.mk` to construct with regards to a reference real value.

  The defs `lb`, `ub` are the actual CauSeq's , `val` is the associated real number,
  and `hlb`, `hub`, and `heq` relate `lb` `ub` and `val` to each other. -/
structure ComputableℝSeq where
  mk' ::
  /-- The bundled lower and upper rational bounds at each step `n`. -/
  lub : ℕ → NonemptyInterval ℚ
  hcl : IsCauSeq abs fun n ↦ (lub n).fst
  hcu : IsCauSeq abs fun n ↦ (lub n).snd
  hlub : ∀n, (lub n).fst ≤ (Real.mk ⟨fun n ↦ (lub n).fst, hcl⟩) ∧
    (lub n).snd ≥ (Real.mk ⟨fun n ↦ (lub n).fst, hcl⟩)
  heq' : let lb : CauSeq ℚ abs := ⟨fun n ↦ (lub n).fst, hcl⟩
        let ub : CauSeq ℚ abs := ⟨fun n ↦ (lub n).snd, hcu⟩
        lb ≈ ub

namespace ComputableℝSeq

open scoped QInterval
/-- The lower-bound Cauchy sequence of a `ComputableℝSeq`. -/
def lb (x : ComputableℝSeq) : CauSeq ℚ abs := ⟨fun n ↦ (x.lub n).fst, x.hcl⟩
/-- The upper-bound Cauchy sequence of a `ComputableℝSeq`. -/
def ub (x : ComputableℝSeq) : CauSeq ℚ abs := ⟨fun n ↦ (x.lub n).snd, x.hcu⟩

/-- Get the real value determined by the sequence. (Irreducibly) given here as the limit of
  the lower bound sequence. -/
irreducible_def val (x : ComputableℝSeq) : ℝ := Real.mk x.lb

/--
@isnad1 id=equiv.0h1v.s5.4c92cebfe859 from=translated src=- shape=78748d38 vocab=fe1483c9
-/
theorem heq (x : ComputableℝSeq) : x.lb ≈ x.ub :=
  x.heq'

/--
@isnad1 id=eq.0h1v.s3.9a3a4d8ef2ad from=translated src=- shape=bc817a25 vocab=41ca4742
-/
theorem lb_eq_ub (x : ComputableℝSeq) : Real.mk x.lb = Real.mk x.ub :=
  Real.mk_eq.2 x.heq'

/--
@isnad1 id=eq.0h1v.s3.9fa2bdb2905d from=translated src=- shape=69b989be vocab=066c7d5f
-/
theorem val_eq_mk_lb (x : ComputableℝSeq) : x.val = Real.mk x.lb :=
  val_def x

/--
@isnad1 id=eq.0h1v.s3.145b36069a17 from=translated src=- shape=69b989be vocab=0696a9d0
-/
theorem val_eq_mk_ub (x : ComputableℝSeq) : x.val = Real.mk x.ub :=
  x.val_eq_mk_lb.trans x.lb_eq_ub

/--
@isnad1 id=le.0h2v.s5.3320ba184761 from=translated src=- shape=e3e664b3 vocab=ff74ddf8
-/
theorem hlb (x : ComputableℝSeq) : ∀n, x.lb n ≤ x.val :=
  fun n ↦ val_eq_mk_lb _ ▸ (x.hlub n).1

/--
@isnad1 id=le.0h2v.s5.0728f597329e from=translated src=- shape=e3e664b3 vocab=7f02841a
-/
theorem hub (x : ComputableℝSeq) : ∀n, x.ub n ≥ x.val :=
  fun n ↦ val_eq_mk_lb _ ▸ (x.hlub n).2

/--
@isnad1 id=mem.0h2v.s3.d7d8417b502e from=translated src=- shape=0f6e5d1a vocab=85070fea
-/
theorem val_mem_interval (x : ComputableℝSeq) : ∀n, x.val ∈ x.lub n :=
  fun n ↦ ⟨x.hlb n, x.hub n⟩

private theorem val_uniq' {x : ℝ} {lb ub : CauSeq ℚ abs} (hlb : ∀ n, lb n ≤ x)
    (hub : ∀ n, ub n ≥ x) (heq : lb ≈ ub) : Real.mk lb = x :=
  (Real.of_near lb x (fun εℝ hεℝ ↦
      let ⟨ε, ⟨hε₁, hε₂⟩⟩ := exists_rat_btwn hεℝ
      let ⟨i,hi⟩ := heq ε (Rat.cast_pos.1 hε₁)
      ⟨i, fun j hj ↦ by
        replace hi := hi j hj
        have hl₁ := hlb j
        have hu₂ := hub j
        rify at hi hl₁ hu₂ hε₁
        rw [abs_ite_le] at hi ⊢
        split_ifs at hi ⊢
        <;> linarith⟩)).2

/-- If a real number x is bounded below and above by a sequence, it must be the value of that
sequence.
@isnad1 id=eq.2h2v.s6.fb6d9d4fcb32 from=translated src=- shape=35a85ee6 vocab=61075e16
-/
theorem val_uniq {x : ℝ} {s : ComputableℝSeq} (hlb : ∀ n, s.lb n ≤ x) (hub : ∀ n, s.ub n ≥ x) :
    s.val = x :=
  s.val_def ▸ val_uniq' hlb hub s.heq

/-- Make a computable sequence for x from a separate lower and upper bound CauSeq. -/
def mk (x : ℝ) (lub : ℕ → ℚInterval)
    (hcl : IsCauSeq abs (fun n ↦ (lub n).fst))
    (hcu : IsCauSeq abs (fun n ↦ (lub n).snd))
    (hlb : ∀ n, (lub n).fst ≤ x)
    (hub : ∀ n, (lub n).snd ≥ x)
    (heq : let lb : CauSeq ℚ abs := ⟨fun n ↦ (lub n).fst, hcl⟩
        let ub : CauSeq ℚ abs := ⟨fun n ↦ (lub n).snd, hcu⟩
        lb ≈ ub) : ComputableℝSeq where
  lub := lub
  hcl := hcl
  hcu := hcu
  heq' := heq
  hlub n := by
    rw [val_uniq' hlb hub heq]
    exact ⟨hlb n, hub n⟩

/--
@isnad1 id=eq.4h3v.s7.df0c8caf64a9 from=translated src=- shape=c939052e vocab=b2041a3f
-/
theorem mk_val_eq_val : (mk x v h₁ h₂ h₃ h₄ h₅).val = x :=
  val_uniq (fun n ↦ h₃ n) (fun n ↦ h₄ n)

/--
@isnad1 id=le.0h2v.s5.0aab4a226df3 from=translated src=- shape=45ad46e6 vocab=153bf57b
-/
theorem lb_le_ub (x : ComputableℝSeq) : ∀n, x.lb n ≤ x.ub n :=
  fun n ↦ Rat.cast_le.mp (le_trans (x.hlb n) (x.hub n))

/--
@isnad1 id=eq.2h2v.s6.c7b8c69b1e9f from=translated src=- shape=7e72ca48 vocab=3ffa2981
-/
@[ext]
theorem ext {x y : ComputableℝSeq} (h₁ : ∀ n, x.lb n = y.lb n) (h₂ : ∀ n, x.ub n = y.ub n) : x = y
  :=
  mk'.injEq _ _ _ _ _ _ _ _ _ _ ▸ (funext fun n ↦ NonemptyInterval.ext (Prod.ext (h₁ n) (h₂ n)))

/-- All rational numbers `q` have a computable sequence: the constant sequence `q`. -/
def ofRat (q : ℚ) : ComputableℝSeq :=
  mk q
    (fun _ ↦ NonemptyInterval.pure q)
    (IsCauSeq.const q) (IsCauSeq.const q)
    (fun _ ↦ rfl.le) (fun _ ↦ rfl.le)
    (Real.mk_eq.mp rfl)

instance natCast : NatCast ComputableℝSeq where natCast n := ofRat n

instance intCast : IntCast ComputableℝSeq where intCast z := ofRat z

instance ratCast : RatCast ComputableℝSeq where ratCast q := ofRat q
/-- Addition of computable real sequences. -/
def add (x : ComputableℝSeq) (y : ComputableℝSeq) : ComputableℝSeq :=
  mk (x.val + y.val)
  (fun n ↦ x.lub n + y.lub n)
  (IsCauSeq.add x.hcl y.hcl)
  (IsCauSeq.add x.hcu y.hcu)
  (by
    intro n
    rw [NonemptyInterval.fst_add]
    push_cast
    exact add_le_add (x.hlb n) (y.hlb n))
  (by
    intro n
    rw [NonemptyInterval.snd_add]
    push_cast
    exact add_le_add (x.hub n) (y.hub n))
  (have := CauSeq.add_equiv_add x.heq y.heq; this) --TODO why does 'inlining' the have not work
/-- Negation of a computable real sequence. -/
def neg (x : ComputableℝSeq) : ComputableℝSeq :=
  mk (-x.val)
  (fun n ↦ -x.lub n)
  (IsCauSeq.neg x.hcu)
  (IsCauSeq.neg x.hcl)
  (fun n ↦ by simpa [ub] using x.hub n)
  (fun n ↦ by simpa [lb] using x.hlb n)
  (have := CauSeq.neg_equiv_neg (Setoid.symm x.heq); this)
/-- Subtraction of computable real sequences. -/
def sub (x : ComputableℝSeq) (y : ComputableℝSeq) : ComputableℝSeq :=
  add x (neg y)

/-- "Bundled" multiplication to give lower and upper bounds. This bundling avoids the need to
  call lb and ub separately for each half (which, in a large product, leads to an exponential
  slowdown). This could be further optimized to use only two ℚ multiplications instead of four,
  when the sign is apparent. -/
def mul' (x : ComputableℝSeq) (y : ComputableℝSeq) : ℕ → ℚInterval :=
  fun n ↦ QInterval.mulPair (x.lub n) (y.lub n)

/-- More friendly expression for the lower bound for multiplication, as a CauSeq. -/
def mulLb (x : ComputableℝSeq) (y : ComputableℝSeq) : CauSeq ℚ abs :=
  ((x.lb * y.lb) ⊓ (x.ub * y.lb)) ⊓ ((x.lb * y.ub) ⊓ (x.ub * y.ub))

/-- More friendly expression for the lower bound for multiplication, as a CauSeq. -/
def mulUb (x : ComputableℝSeq) (y : ComputableℝSeq) : CauSeq ℚ abs :=
  ((x.lb * y.lb) ⊔ (x.ub * y.lb)) ⊔ ((x.lb * y.ub) ⊔ (x.ub * y.ub))

/-- The lower bounds from `mul'` are precisely the same sequence as `mulLb`.
@isnad1 id=eq.0h2v.s5.d606ae53bb6a from=translated src=- shape=b1671bb3 vocab=2106df03
-/
theorem fst_mul'_eq_mulLb : (fun i ↦ i.fst) ∘ mul' x y = (mulLb x y).1 := by
  ext n
  dsimp
  rw [mul', mulLb]
  congr

/-- The upper bounds from `mul'` are precisely the same sequence as `mulUb`.
@isnad1 id=eq.0h2v.s5.ecd6220d7156 from=translated src=- shape=b1671bb3 vocab=e90dd59f
-/
theorem snd_mul'_eq_mulUb : (fun i ↦ i.snd) ∘ mul' x y = (mulUb x y).1 := by
  ext n
  dsimp
  rw [mul', mulUb]
  congr

/-- The lower bounds from `mul'` form a Cauchy sequence.
@isnad1 id=iscauseq.0h2v.s5.d59268566f41 from=translated src=- shape=7188029c vocab=c9a00455
-/
theorem mul'_fst_iscau : IsCauSeq abs ((fun i ↦ i.fst) ∘ (mul' x y)) :=
  fst_mul'_eq_mulLb ▸ Subtype.property _

/-- The upper bounds from `mul'` form a Cauchy sequence.
@isnad1 id=iscauseq.0h2v.s5.ad09575053a1 from=translated src=- shape=7188029c vocab=79a10bdc
-/
theorem mul'_snd_iscau : IsCauSeq abs ((fun i ↦ i.snd) ∘ (mul' x y)) :=
  snd_mul'_eq_mulUb ▸ Subtype.property _

/--
@isnad1 id=equiv.0h2v.s5.b52fbb79f3fe from=translated src=- shape=995ce5a1 vocab=494f3e0c
-/
theorem lb_ub_mul_equiv (x : ComputableℝSeq) (y : ComputableℝSeq) :
    mulLb x y ≈ mulUb x y := by
  have hll : x.lb * y.lb ≈ x.lb * y.lb := Setoid.refl _
  have hul := CauSeq.mul_equiv_mul (Setoid.symm x.heq) (Setoid.refl y.lb)
  have hlu := CauSeq.mul_equiv_mul (Setoid.refl x.lb) (Setoid.symm y.heq)
  have huu := CauSeq.mul_equiv_mul (Setoid.symm x.heq) (Setoid.symm y.heq)
  have hl : mulLb x y ≈ x.lb * y.lb :=
    CauSeq.inf_equiv_of_equivs (CauSeq.inf_equiv_of_equivs hll hul)
      (CauSeq.inf_equiv_of_equivs hlu huu)
  have hu : mulUb x y ≈ x.lb * y.lb :=
    CauSeq.sup_equiv_of_equivs (CauSeq.sup_equiv_of_equivs hll hul)
      (CauSeq.sup_equiv_of_equivs hlu huu)
  exact Setoid.trans hl (Setoid.symm hu)

/--
@isnad1 id=le.0h3v.s5.b2340a6b32ab from=translated src=- shape=2de9eb08 vocab=7caf2f28
-/
theorem mulLb_is_lb (x : ComputableℝSeq) (y : ComputableℝSeq) (n : ℕ) :
    (mulLb x y).1 n ≤ x.val * y.val :=
  QInterval.mulPair_lb_is_lb _ (x.val_mem_interval n) _ (y.val_mem_interval n)

/--
@isnad1 id=le.0h3v.s5.167c8edea672 from=translated src=- shape=2de9eb08 vocab=1fab4532
-/
theorem mulUb_is_ub (x : ComputableℝSeq) (y : ComputableℝSeq) (n : ℕ) :
    (mulUb x y).1 n ≥ x.val * y.val :=
  QInterval.mulPair_ub_is_ub _ (x.val_mem_interval n) _ (y.val_mem_interval n)
/-- Multiplication of computable real sequences. -/
def mul (x : ComputableℝSeq) (y : ComputableℝSeq) : ComputableℝSeq where
  lub := mul' x y
  hcl := mul'_fst_iscau
  hcu := mul'_snd_iscau
  heq' := by
    have h₁ : mulLb x y = ⟨fun n ↦ (mul' x y n).fst, mul'_fst_iscau⟩ :=
      Subtype.ext fst_mul'_eq_mulLb.symm
    have h₂ : mulUb x y = ⟨fun n ↦ (mul' x y n).snd, mul'_snd_iscau⟩ :=
      Subtype.ext snd_mul'_eq_mulUb.symm
    exact h₂ ▸ h₁ ▸ lb_ub_mul_equiv x y
  hlub n :=
    let h₀ : Real.mk _ = x.val * y.val := by
      apply val_uniq' (mulLb_is_lb x y) (mulUb_is_ub x y)
      exact lb_ub_mul_equiv x y
    h₀ ▸ QInterval.mem_mulPair _ (x.val_mem_interval n) _ (y.val_mem_interval n)

instance instComputableZero : Zero ComputableℝSeq :=
  ⟨(0 : ℕ)⟩

instance instComputableOne : One ComputableℝSeq :=
  ⟨(1 : ℕ)⟩

instance instAdd : Add ComputableℝSeq :=
  ⟨add⟩

instance instNeg : Neg ComputableℝSeq :=
  ⟨neg⟩

instance instSub : Sub ComputableℝSeq :=
  ⟨sub⟩

instance instMul : Mul ComputableℝSeq :=
  ⟨mul⟩

instance instInh : Inhabited ComputableℝSeq :=
  ⟨0⟩

section simps

variable (x y : ComputableℝSeq)

/--
@isnad1 id=eq.0h1v.s5.7164356b9b36 from=translated src=- shape=738c9efe vocab=3ad7d4b8
-/
@[simp]
theorem natCast_lb : (Nat.cast n : ComputableℝSeq).lb = n := by
  rfl

/--
@isnad1 id=eq.0h1v.s5.4f8fcbe07c28 from=translated src=- shape=738c9efe vocab=b9a57b56
-/
@[simp]
theorem natCast_ub : (Nat.cast n : ComputableℝSeq).ub = n := by
  rfl

/--
@isnad1 id=eq.0h1v.s3.b5579b8b179e from=translated src=- shape=b37550ee vocab=3236527f
-/
@[simp]
theorem val_natCast : (Nat.cast n : ComputableℝSeq).val = n :=
  val_eq_mk_lb _ ▸ natCast_lb ▸ rfl

/--
@isnad1 id=eq.0h1v.s5.e08f0d2d349e from=translated src=- shape=738c9efe vocab=4023a826
-/
@[simp]
theorem intCast_lb : (Int.cast z : ComputableℝSeq).lb = z := by
  rfl

/--
@isnad1 id=eq.0h1v.s5.cf0e15cf3da2 from=translated src=- shape=738c9efe vocab=77e685a9
-/
@[simp]
theorem intCast_ub : (Int.cast z : ComputableℝSeq).ub = z := by
  rfl

/--
@isnad1 id=eq.0h1v.s3.d6dcbc07fa8a from=translated src=- shape=b37550ee vocab=ccee7ca3
-/
@[simp]
theorem val_intCast : (Int.cast z : ComputableℝSeq).val = z :=
  val_eq_mk_lb _ ▸ intCast_lb ▸ rfl

/--
@isnad1 id=eq.0h1v.s5.b40ac1416d46 from=translated src=- shape=fc9a1cf9 vocab=72d81ba7
-/
theorem ratCast_lb : (Rat.cast q : ComputableℝSeq).lb = CauSeq.const abs q := by
  rfl

/--
@isnad1 id=eq.0h1v.s5.d53e9436d7e5 from=translated src=- shape=fc9a1cf9 vocab=cac6bb07
-/
theorem ratCast_ub : (Rat.cast q : ComputableℝSeq).ub = CauSeq.const abs q := by
  rfl

/--
@isnad1 id=eq.0h1v.s3.c0fa8d0e5b41 from=translated src=- shape=b37550ee vocab=d4005ee0
-/
@[simp]
theorem val_ratCast : (Rat.cast q : ComputableℝSeq).val = q :=
  val_eq_mk_lb _ ▸ ratCast_lb ▸ rfl

/--
@isnad1 id=eq.0h0v.s6.50624292b888 from=translated src=- shape=34fd2b08 vocab=22fbd940
-/
@[simp]
theorem zero_lb : (0 : ComputableℝSeq).lb = 0 := by
  rfl

/--
@isnad1 id=eq.0h0v.s6.bc4e038a061d from=translated src=- shape=34fd2b08 vocab=0b3a2034
-/
@[simp]
theorem zero_ub : (0 : ComputableℝSeq).ub = 0 := by
  rfl

/--
@isnad1 id=eq.0h0v.s3.56d979f3bb13 from=translated src=- shape=1ac31801 vocab=c3550bd8
-/
@[simp]
theorem val_zero : (0 : ComputableℝSeq).val = 0 :=
  val_eq_mk_lb _ ▸ Real.mk_zero

/--
@isnad1 id=eq.0h0v.s6.e5da3f3ec99f from=translated src=- shape=34fd2b08 vocab=22fbd940
-/
@[simp]
theorem one_lb : (1 : ComputableℝSeq).lb = 1 := by
  rfl

/--
@isnad1 id=eq.0h0v.s6.29f4ac3383e2 from=translated src=- shape=34fd2b08 vocab=0b3a2034
-/
@[simp]
theorem one_ub : (1 : ComputableℝSeq).ub = 1 := by
  rfl

/--
@isnad1 id=eq.0h0v.s3.3eaf0a2ea7b5 from=translated src=- shape=1ac31801 vocab=c3550bd8
-/
@[simp]
theorem val_one : (1 : ComputableℝSeq).val = 1 :=
  val_eq_mk_lb _ ▸ Real.mk_one

/--
@isnad1 id=eq.0h2v.s6.18e3f90ffb09 from=translated src=- shape=b2f24dcd vocab=3d9b0194
-/
@[simp]
theorem lb_add : (x + y).lb = x.lb + y.lb :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.bd7e0beadc1c from=translated src=- shape=b2f24dcd vocab=945fd651
-/
@[simp]
theorem ub_add : (x + y).ub = x.ub + y.ub :=
  rfl

/--
@isnad1 id=eq.0h2v.s4.42c8641cb024 from=translated src=- shape=0438c7a3 vocab=bcfbfc95
-/
@[simp]
theorem val_add : (x + y).val = x.val + y.val :=
  (mk_val_eq_val : (add x y).val = x.val + y.val)

/--
@isnad1 id=eq.0h1v.s5.298560f0ec69 from=translated src=- shape=5b0db9a3 vocab=1691669f
-/
@[simp]
theorem lb_neg : (-x).lb = -x.ub :=
  rfl

/--
@isnad1 id=eq.0h1v.s5.4317398052c7 from=translated src=- shape=5b0db9a3 vocab=1691669f
-/
@[simp]
theorem ub_neg : (-x).ub = -x.lb := by
  rfl

/--
@isnad1 id=eq.0h1v.s3.a63021a50735 from=translated src=- shape=5a02da31 vocab=9f2da361
-/
@[simp]
theorem val_neg : (-x).val = -x.val :=
  (mk_val_eq_val : (neg x).val = -x.val)

/--
@isnad1 id=eq.0h2v.s6.774be4ee3506 from=translated src=- shape=4438fcfe vocab=1755447b
-/
@[simp]
theorem lb_sub : (x - y).lb = x.lb - y.ub := by
  change (x + -y).lb = x.lb - y.ub
  rw [lb_add, lb_neg, sub_eq_add_neg]

/--
@isnad1 id=eq.0h2v.s6.3dd69e6260bf from=translated src=- shape=4438fcfe vocab=1755447b
-/
@[simp]
theorem ub_sub : (x - y).ub = x.ub - y.lb := by
  change (x + -y).ub = x.ub - y.lb
  rw [ub_add, ub_neg, sub_eq_add_neg]

/--
@isnad1 id=eq.0h2v.s4.b118d684ef8f from=translated src=- shape=0438c7a3 vocab=007faeb4
-/
@[simp]
theorem val_sub : (x - y).val = x.val - y.val := by
  change (x + -y).val = x.val - y.val
  rw [val_add, val_neg, sub_eq_add_neg]

/--
@isnad1 id=eq.0h2v.s8.bf920078f1e7 from=translated src=- shape=28a38d61 vocab=9438485c
-/
theorem lb_mul : (x * y).lb = ((x.lb * y.lb) ⊓ (x.ub * y.lb)) ⊓ ((x.lb * y.ub) ⊓ (x.ub * y.ub)) :=
  by
  ext
  rw [← mulLb, ← fst_mul'_eq_mulLb]
  rfl

/--
@isnad1 id=eq.0h2v.s8.934e2b0db480 from=translated src=- shape=60b803ed vocab=a45d6ac9
-/
theorem ub_mul : (x * y).ub = ((x.lb * y.lb) ⊔ (x.ub * y.lb)) ⊔ ((x.lb * y.ub) ⊔ (x.ub * y.ub)) :=
  by
  ext
  rw [← mulUb, ← snd_mul'_eq_mulUb]
  rfl

/--
@isnad1 id=eq.0h2v.s4.99d926d5ede7 from=translated src=- shape=0438c7a3 vocab=2519e520
-/
@[simp]
theorem val_mul : (x * y).val = x.val * y.val := by
  suffices (mul x y).val = x.val * y.val by
    exact this
  rw [val_def]
  exact val_uniq' (mulLb_is_lb x y) (mulUb_is_ub x y) (lb_ub_mul_equiv x y)

end simps

section signs

private noncomputable instance sign_aux_sound (x : ℝ) :
    Inhabited { s : SignType // s = SignType.sign x } := ⟨SignType.sign x, rfl⟩

/-- The sign of `x`, defined classically as the sign of its real value, so this definition is
  `noncomputable` and carries no algorithmic content. (Searching the interval sequence for a
  sign witness terminates exactly when `x ≠ 0` or some interval is the point `0`, so a fuel-free
  executable version cannot be total.) This ends up providing the `DecidableEq` and
  `DecidableLT` instances on `Computableℝ`, which are likewise classical. -/
noncomputable def sign (x : ComputableℝSeq) : SignType :=
  SignType.sign x.val

/--
@isnad1 id=eq.0h1v.s5.9380bb6f1b96 from=translated src=- shape=fda29813 vocab=f46760a7
-/
theorem sign_sound (x : ComputableℝSeq) : x.sign = SignType.sign x.val :=
  rfl

/--
@isnad1 id=iff.0h1v.s4.7ea94faf207d from=translated src=- shape=eec6a9b8 vocab=6f49ca3f
-/
theorem sign_pos_iff (x : ComputableℝSeq) : x.sign = SignType.pos ↔ 0 < x.val := by
  rw [sign_sound, SignType.pos_eq_one, sign_eq_one_iff]

/--
@isnad1 id=iff.0h1v.s4.8a360fb5e8a4 from=translated src=- shape=13806f84 vocab=65bc43fc
-/
theorem sign_neg_iff (x : ComputableℝSeq) : x.sign = SignType.neg ↔ x.val < 0 := by
  rw [sign_sound, SignType.neg_eq_neg_one, sign_eq_neg_one_iff]

/--
@isnad1 id=iff.0h1v.s4.cae8ba033a64 from=translated src=- shape=201d5bbc vocab=e4df34ca
-/
theorem sign_zero_iff (x : ComputableℝSeq) : x.sign = SignType.zero ↔ x.val = 0 := by
  rw [sign_sound, SignType.zero_eq_zero, sign_eq_zero_iff]

/-- If x is nonzero, there is eventually a point in the Cauchy sequences where either the lower
or upper bound prove this. This theorem states that this point exists. -/
noncomputable def signWitnessTerm (x : ComputableℝSeq) (hnz : x.val ≠ 0) :
    { xq : ℕ × ℚ // (0:ℝ) < xq.2 ∧ xq.2 < abs x.val ∧ ∀ j ≥ xq.1, |(x.lb - x.ub) j| < xq.2} := by
    have hsx : abs x.val > 0 := by positivity
    have hq' : ∃(q:ℚ), (0:ℝ) < q ∧ q < abs x.val := exists_rat_btwn hsx
    obtain ⟨q, hq⟩ := Classical.indefiniteDescription _ hq'
    obtain ⟨hq₁, hq₂⟩ := hq
    obtain ⟨i, hi⟩ := Classical.indefiniteDescription _ (x.heq q (Rat.cast_pos.mp hq₁))
    use (i, q)

/--
@isnad1 id=le.3h2v.s8.90eb445a2e9d from=translated src=- shape=b68fffde vocab=baec065c
-/
theorem signWitnessTerm_prop (x : ComputableℝSeq) (n : ℕ) (hnz : x.val ≠ 0)
    (hub : ¬(x.ub).val n < 0) (hlb : ¬(x.lb).val n > 0) :
    n + Nat.succ 0 ≤ (x.signWitnessTerm hnz).val.1 := by
  push Not at hub hlb
  obtain ⟨⟨k, q⟩, ⟨h₁, h₂, h₃⟩⟩ := x.signWitnessTerm hnz
  by_contra hn
  replace h₃ := h₃ n (by linarith)
  simp_rw [CauSeq.sub_apply] at h₃
  rw [abs_ite_le] at h₂ h₃
  have := x.hlb n
  have := x.hub n
  split_ifs at h₂ h₃ with h₄ h₅
  all_goals
    rify at *; linarith (config := {splitNe := true})

/-- With the proof that x≠0, we can also eventually get a sign witness: a number n such that
    either 0 < x and 0 < lb n; or that x < 0 and ub n < 0. Marking it as irreducible because
    in theory all of the info needed is in the return Subtype. -/
irreducible_def signWitness (x : ComputableℝSeq) (hnz : x.val ≠ 0) :
    { n // (0 < x.val ∧ 0 < x.lb n) ∨ (x.val < 0 ∧ x.ub n < 0)} :=
  signWitness_aux 0 hnz where
  signWitness_aux (k : ℕ) (hnz : x.val ≠ 0) : { n // (0 < x.val ∧ 0 < x.lb n) ∨ (x.val < 0 ∧ x.ub
    n < 0)}:=
    if hub : x.ub k < 0 then
      ⟨k, Or.inr ⟨by rify at hub; linarith [x.hub k], hub⟩⟩
    else if hlb : x.lb k > 0 then
      ⟨k, Or.inl ⟨by rify at hlb; linarith [x.hlb k], hlb⟩⟩
    else
      signWitness_aux (k+1) hnz
    termination_by
      (x.signWitnessTerm hnz).val.fst - k
    decreasing_by
    · decreasing_with
      apply Nat.sub_add_lt_sub _ Nat.le.refl
      exact x.signWitnessTerm_prop k hnz hub hlb

/-- With the proof that x≠0, we get a total comparison function. -/
def isPos {x : ComputableℝSeq} (hnz : x.val ≠ 0) : Bool :=
  0 < x.lb (x.signWitness hnz)

/-- Proof that `isPos` correctly determines whether a nonzero computable number is positive.
@isnad1 id=iff.1h1v.s4.234404cb234b from=translated src=- shape=33195768 vocab=6b89aa73
-/
theorem isPos_iff (x : ComputableℝSeq) (hnz : x.val ≠ 0) : isPos hnz ↔ 0 < x.val := by
  have hsw := (x.signWitness hnz).property
  have hls := x.hlb (x.signWitness hnz)
  have hus := x.hub (x.signWitness hnz)
  constructor
  · intro h
    rw [isPos, decide_eq_true_eq] at h
    cases hsw
    · tauto
    · rify at *
      linarith
  · intro h
    have := not_lt.mpr (le_of_lt h)
    rw [isPos, decide_eq_true_eq]
    tauto

/--
@isnad1 id=lt.2h1v.s5.cc7f4074ad11 from=translated src=- shape=c492d061 vocab=6b89aa73
-/
theorem neg_of_not_pos {x : ComputableℝSeq} {hnz : x.val ≠ 0} (h : ¬isPos hnz) : x.val < 0 := by
  rw [isPos_iff] at h
  linarith (config := {splitNe := true})

/-- Given computable sequences for a nonzero x, drop the leading terms of both sequences
(lb and ub) until both are nonzero. This gives a new sequence that we can "safely" invert.
-/
def dropTilSigned (x : ComputableℝSeq) (hnz : x.val ≠ 0) : ComputableℝSeq :=
  let start := signWitness x hnz
  mk (x := x.val)
  (lub := fun n ↦ x.lub (start+n))
  (hcl := (x.lb.drop start).prop)
  (hcu := (x.ub.drop start).prop)
  (hlb := fun n ↦ x.hlb (start+n))
  (hub := fun n ↦ x.hub (start+n))
  (heq := Setoid.trans (
      Setoid.trans (x.lb.drop_equiv_self start) x.heq)
      (Setoid.symm (x.ub.drop_equiv_self start)))

/--
@isnad1 id=eq.1h1v.s4.6be19f8a0d50 from=translated src=- shape=6318ec3e vocab=f437884c
-/
@[simp]
theorem val_dropTilSigned {x : ComputableℝSeq} (h : x.val ≠ 0) : (x.dropTilSigned h).val = x.val :=
  by
  rw [val, val, Real.mk_eq]
  apply (lb x).drop_equiv_self

/--
@isnad1 id=ne.1h1v.s4.dc4741bfd9a9 from=translated src=- shape=3ed1d281 vocab=f437884c
-/
theorem dropTilSigned_nz {x : ComputableℝSeq} (h : x.val ≠ 0) : (x.dropTilSigned h).val ≠ 0 :=
  val_dropTilSigned h ▸ h

/--
@isnad1 id=or.1h1v.s6.78c01bba5906 from=translated src=- shape=6508f91e vocab=3d54530d
-/
theorem sign_dropTilSigned {x : ComputableℝSeq} (hnz : x.val ≠ 0) :
    (0 < x.val ∧ 0 < (x.dropTilSigned hnz).lb 0) ∨ (x.val < 0 ∧ (x.dropTilSigned hnz).ub 0 < 0) :=
      by
  have := (x.signWitness hnz).prop
  have := lt_trichotomy x.val 0
  tauto

/--
@isnad1 id=iff.1h1v.s6.0752a6e519c3 from=translated src=- shape=9bd07e5e vocab=7ec4402e
-/
theorem dropTilSigned_pos {x : ComputableℝSeq} (h : x.val ≠ 0) :
    x.val > 0 ↔ (x.dropTilSigned h).lb 0 > 0 :=
  ⟨fun h' ↦ (Or.resolve_right (sign_dropTilSigned h)
    (not_and.mpr fun a _ => ( not_lt_of_gt h') a)).2,
   fun h' ↦ calc val x = _ := (val_dropTilSigned h).symm
        _ ≥ _ := (x.dropTilSigned h).hlb 0
        _ > 0 := Rat.cast_pos.2 h'⟩

/--
@isnad1 id=iff.1h1v.s6.00ab7f0ff4da from=translated src=- shape=9bd07e5e vocab=3427f9a7
-/
theorem dropTilSigned_neg {x : ComputableℝSeq} (h : x.val ≠ 0) :
    x.val < 0 ↔ (x.dropTilSigned h).ub 0 < 0 :=
  ⟨fun h' ↦ (Or.resolve_left (sign_dropTilSigned h)
    (not_and.mpr fun a _ => ( not_lt_of_gt h') a)).2,
   fun h' ↦ calc val x = _ := (val_dropTilSigned h).symm
        _ ≤ _ := (x.dropTilSigned h).hub 0
        _ < 0 := Rat.cast_lt_zero.2 h'⟩

end signs

section safeInv

/--
@isnad1 id=not.1h1v.s4.45155ced29b9 from=translated src=- shape=81a9c16e vocab=9620eb28
-/
theorem neg_LimZero_lb_of_val {x : ComputableℝSeq} (hnz : x.val ≠ 0) : ¬x.lb.LimZero := by
  rw [← CauSeq.Completion.mk_eq_zero]
  rw [val_eq_mk_lb, ←Real.mk_zero, ne_eq, Real.ofCauchy.injEq] at hnz
  exact hnz

/--
@isnad1 id=not.1h1v.s4.6601e46e06cb from=translated src=- shape=81a9c16e vocab=c37e7831
-/
theorem neg_LimZero_ub_of_val {x : ComputableℝSeq} (hnz : x.val ≠ 0) : ¬x.ub.LimZero := by
  rw [← CauSeq.Completion.mk_eq_zero]
  rw [val_eq_mk_ub, ←Real.mk_zero, ne_eq, Real.ofCauchy.injEq] at hnz
  exact hnz

/--
@isnad1 id=pos.1h1v.s4.a2826b718dfc from=translated src=- shape=5e6a3299 vocab=34536073
-/
theorem pos_ub_of_val {x : ComputableℝSeq} (hp : x.val > 0) : x.ub.Pos :=
  Real.mk_pos.1 (val_eq_mk_ub _ ▸ hp)

/--
@isnad1 id=pos.1h1v.s5.b11fc6191471 from=translated src=- shape=3741e945 vocab=df5acd4c
-/
theorem pos_neg_ub_of_val {x : ComputableℝSeq} (hn : x.val < 0) : (-x.ub).Pos :=
  Real.mk_pos.1 (lb_neg _ ▸ val_eq_mk_lb _ ▸ val_neg _ ▸ Left.neg_pos_iff.mpr hn)

/--
@isnad1 id=pos.1h1v.s4.1d3dc2a2b05d from=translated src=- shape=5e6a3299 vocab=22b6539a
-/
theorem pos_lb_of_val {x : ComputableℝSeq} (hp : x.val > 0) : x.lb.Pos :=
  Real.mk_pos.1 (val_eq_mk_lb _ ▸ hp)

/--
@isnad1 id=pos.1h1v.s5.5fcd75557e9e from=translated src=- shape=3741e945 vocab=6fea3143
-/
theorem pos_neg_lb_of_val {x : ComputableℝSeq} (hn : x.val < 0) : (-x.lb).Pos :=
  Real.mk_pos.1 (ub_neg _ ▸ val_eq_mk_ub _ ▸ val_neg _ ▸ Left.neg_pos_iff.mpr hn)

/-- The sequence of lower bounds of 1/x. Only functions "correctly" to give lower bounds if we
   assume that hx is already `hx.dropTilSigned` (as proven in `lbInv_correct`) -- but those
   assumptions aren't need for proving that it's Cauchy. -/
def lbInv (x : ComputableℝSeq) (hnz : x.val ≠ 0) : CauSeq ℚ abs :=
  if hp : isPos hnz then --if x is positive, then reciprocals of ub's are always good lb's.
    x.ub.inv (neg_LimZero_ub_of_val hnz)
  else --x is negative, so positive values for ub don't give us any good lb's.
    let ub0 := x.ub 0 --save this first value, it acts as fallback if we get a bad ub
    ⟨fun n ↦
      let ub := x.ub n
      if ub ≥ 0 then
        ub0⁻¹ --sign is indeterminate, fall back to the starting values
      else
        ub⁻¹, fun _ hε ↦
          have hxv : x.val < 0 := by rw [isPos_iff] at hp; linarith (config:={splitNe:=true})
          let ⟨_, q0, Hq⟩ := pos_neg_ub_of_val hxv
          let ⟨_, K0, HK⟩ := CauSeq.abv_pos_of_not_limZero (neg_LimZero_ub_of_val hnz)
          let ⟨_, δ0, Hδ⟩ := rat_inv_continuous_lemma abs hε K0
          let ⟨i, H⟩ := exists_forall_ge_and (exists_forall_ge_and HK (x.ub.cauchy₃ δ0)) Hq
          let ⟨⟨iK, H'⟩, _⟩ := H _ le_rfl
          ⟨i, fun j hj ↦
            have h₁ := CauSeq.neg_apply x.ub _ ▸ H _ le_rfl
            have h₁ := CauSeq.neg_apply x.ub _ ▸ H _ hj
            by
              simp only [(by linarith : ¬x.ub i ≥ 0),(by linarith : ¬x.ub j ≥ 0), ite_false]
              exact Hδ (H _ hj).1.1 iK (H' _ hj)⟩⟩

/-- Analgoous to `lbInv` for providing upper bounds on 1/x. -/
def ubInv (x : ComputableℝSeq) (hnz : x.val ≠ 0) : CauSeq ℚ abs :=
  if hp : ¬isPos hnz then --if x is positive, then reciprocals of ub's are always good lb's.
    x.lb.inv (neg_LimZero_lb_of_val hnz)
  else --x is negative, so positive values for ub don't give us any good lb's.
    let lb0 := x.lb 0 --save this first value, it acts as fallback if we get a bad ub
    ⟨fun n ↦
      let lb := x.lb n
      if lb ≤ 0 then
        lb0⁻¹ --sign is indeterminate, fall back to the starting values
      else
        lb⁻¹, fun _ hε ↦
          have hxv : x.val > 0 := by
            rw [isPos_iff, not_not] at hp; linarith (config:={splitNe:=true})
          let ⟨_, q0, Hq⟩ := pos_lb_of_val hxv
          let ⟨_, K0, HK⟩ := CauSeq.abv_pos_of_not_limZero (neg_LimZero_lb_of_val hnz)
          let ⟨_, δ0, Hδ⟩ := rat_inv_continuous_lemma abs hε K0
          let ⟨i, H⟩ := exists_forall_ge_and (exists_forall_ge_and HK (x.lb.cauchy₃ δ0)) Hq
          let ⟨⟨iK, H'⟩, _⟩ := H _ le_rfl
          ⟨i, fun j hj ↦
            have h₁ := H _ le_rfl
            have h₁ := H _ hj
            by
              simp only [(by linarith : ¬x.lb i ≤ 0),(by linarith : ¬x.lb j ≤ 0), ite_false]
              exact Hδ (H j hj).1.1 iK (H' j hj)
              ⟩⟩

/-- When applied to a `dropTilSigned`, `lbInv` is a correct lower bound on x⁻¹.
@isnad1 id=le.1h2v.s5.6913920d14a4 from=translated src=- shape=205e3537 vocab=a3552ab8
-/
theorem lbInv_correct {x : ComputableℝSeq} (hnz : x.val ≠ 0) : ∀n,
    (x.dropTilSigned hnz).lbInv (dropTilSigned_nz hnz) n ≤ x.val⁻¹ := by
  intro n
  by_cases hp : isPos (dropTilSigned_nz hnz)
  · rw [show (x.dropTilSigned hnz).lbInv (dropTilSigned_nz hnz) =
      (x.dropTilSigned hnz).ub.inv (neg_LimZero_ub_of_val (dropTilSigned_nz hnz)) from
        dite_eq_left hp]
    simp only [CauSeq.inv_apply, Rat.cast_inv]
    rw [isPos_iff, val_dropTilSigned] at hp
    apply inv_anti₀ hp
    apply hub
  · have hv : val x < 0 := by
      rw [isPos_iff, val_dropTilSigned] at hp; linarith (config:={splitNe:=true})
    rw [show (x.dropTilSigned hnz).lbInv (dropTilSigned_nz hnz) n =
      if (x.dropTilSigned hnz).ub n ≥ 0 then ((x.dropTilSigned hnz).ub 0)⁻¹
      else ((x.dropTilSigned hnz).ub n)⁻¹ from
        congrFun (congrArg Subtype.val (dite_eq_right hp)) n]
    split_ifs with h
    <;> simp only [Rat.cast_inv]
    <;> apply (inv_le_inv_of_neg ?_ hv).2 (hub x _)
    · exact_mod_cast (dropTilSigned_neg hnz).1 hv
    · exact_mod_cast not_le.1 h

/-- When applied to a `dropTilSigned`, `ubInv` is a correct upper bound on x⁻¹.
@isnad1 id=le.1h2v.s5.5dd563ed9bac from=translated src=- shape=205e3537 vocab=ff48b88e
-/
theorem ubInv_correct {x : ComputableℝSeq} (hnz : x.val ≠ 0) : ∀n,
    (x.dropTilSigned hnz).ubInv (dropTilSigned_nz hnz) n ≥ x.val⁻¹ := by
  intro n
  by_cases hp : isPos (dropTilSigned_nz hnz)
  · have hv : val x > 0 := by
      rw [isPos_iff, val_dropTilSigned] at hp; linarith (config:={splitNe:=true})
    rw [show (x.dropTilSigned hnz).ubInv (dropTilSigned_nz hnz) n =
      if (x.dropTilSigned hnz).lb n ≤ 0 then ((x.dropTilSigned hnz).lb 0)⁻¹
      else ((x.dropTilSigned hnz).lb n)⁻¹ from
      congrFun (congrArg Subtype.val (dite_eq_right (not_not_intro hp))) n]
    split_ifs with h
    <;> simp only [Rat.cast_inv]
    <;> apply inv_anti₀ ?_ ((val_dropTilSigned hnz) ▸ hlb _ _)
    · exact_mod_cast (dropTilSigned_pos hnz).1 hv
    · exact_mod_cast not_le.1 h
  · rw [show (x.dropTilSigned hnz).ubInv (dropTilSigned_nz hnz) =
      (x.dropTilSigned hnz).lb.inv (neg_LimZero_lb_of_val (dropTilSigned_nz hnz)) from
        dite_eq_left hp]
    simp only [CauSeq.inv_apply, Rat.cast_inv]
    replace hp := val_dropTilSigned _ ▸ neg_of_not_pos hp
    rw [ge_iff_le, inv_le_inv_of_neg]
    · exact ((val_dropTilSigned hnz) ▸ hlb _ _)
    · exact hp
    · calc _ ≤ _ := ((val_dropTilSigned hnz) ▸ hlb _ _)
      _ < _ := hp

/-- `x.lbInv` converges to `(x.val)⁻¹`.
@isnad1 id=eq.1h1v.s4.cdd4ae65875e from=translated src=- shape=77504a84 vocab=a703e593
-/
theorem lbInv_converges {x : ComputableℝSeq} (hnz : x.val ≠ 0) :
    Real.mk (x.lbInv hnz) = x.val⁻¹ := by
  apply Real.ext_cauchy
  rw [Real.cauchy_inv, Real.cauchy, Real.cauchy, Real.mk, val_eq_mk_ub, Real.mk,
    CauSeq.Completion.inv_mk (neg_LimZero_ub_of_val hnz), CauSeq.Completion.mk_eq]
  by_cases h : isPos hnz
  · rw [show x.lbInv hnz = x.ub.inv (neg_LimZero_ub_of_val hnz) from dite_eq_left h, sub_self]
    exact CauSeq.zero_limZero
  · exact fun _ hε ↦
      have hxv : x.val < 0 := by
        rw [isPos_iff] at h
        linarith (config := {splitNe := true})
      let ⟨q, q0, ⟨i, H⟩⟩ := pos_neg_ub_of_val hxv
      ⟨i, fun j hj ↦
        have : ¬x.ub j ≥ 0 := by linarith [CauSeq.neg_apply x.ub _ ▸ H _ hj]
        by
          rw [CauSeq.sub_apply, show x.lbInv hnz j = if x.ub j ≥ 0 then (x.ub 0)⁻¹
            else (x.ub j)⁻¹ from congrFun (congrArg Subtype.val (dite_eq_right h)) j]
          simp [this, hε]⟩

/-- When applied to a `dropTilSigned`, `lbInv` is converges to x⁻¹.
@isnad1 id=eq.1h1v.s4.73cd5eee022e from=translated src=- shape=811b3768 vocab=04fd0597
-/
theorem lbInv_signed_converges {x : ComputableℝSeq} (hnz : x.val ≠ 0) :
    Real.mk ((x.dropTilSigned hnz).lbInv (dropTilSigned_nz hnz)) = x.val⁻¹ := by
  simp [lbInv_converges (dropTilSigned_nz hnz)]

/-- `x.ubInv` converges to `(x.val)⁻¹`.
@isnad1 id=eq.1h1v.s4.28fab36d15e8 from=translated src=- shape=77504a84 vocab=44fb4be3
-/
theorem ubInv_converges {x : ComputableℝSeq} (hnz : x.val ≠ 0) :
    Real.mk (x.ubInv hnz) = x.val⁻¹ := by
  apply Real.ext_cauchy
  rw [Real.cauchy_inv, Real.cauchy, Real.cauchy, Real.mk, val_eq_mk_lb, Real.mk,
    CauSeq.Completion.inv_mk (neg_LimZero_lb_of_val hnz), CauSeq.Completion.mk_eq]
  by_cases h : isPos hnz
  · exact fun _ hε ↦
      have hxv : x.val > 0 := by
        rw [isPos_iff] at h
        linarith (config := {splitNe := true})
      let ⟨q, q0, ⟨i, H⟩⟩ := pos_lb_of_val hxv
      ⟨i, fun j hj ↦
        have : ¬x.lb j ≤ 0 := by linarith [H _ hj]
        by
          rw [CauSeq.sub_apply, show x.ubInv hnz j = if x.lb j ≤ 0 then (x.lb 0)⁻¹
            else (x.lb j)⁻¹ from
              congrFun (congrArg Subtype.val (dite_eq_right (not_not_intro h))) j]
          simp [this, hε]⟩
  · rw [show x.ubInv hnz = x.lb.inv (neg_LimZero_lb_of_val hnz) from dite_eq_left h, sub_self]
    exact CauSeq.zero_limZero

/-- When applied to a `dropTilSigned`, `ubInv` is converges to x⁻¹.
TODO: version without hnz hypothesis.
@isnad1 id=eq.1h1v.s4.6e4fc81df2a0 from=translated src=- shape=811b3768 vocab=5b7eac47
-/
theorem ubInv_signed_converges {x : ComputableℝSeq} (hnz : x.val ≠ 0) :
    Real.mk ((x.dropTilSigned hnz).ubInv (dropTilSigned_nz hnz)) = x.val⁻¹ := by
  simp [ubInv_converges (dropTilSigned_nz hnz)]

/-- An inverse is defined only on reals that we can prove are nonzero. If we can prove they are
 nonzero, then we can prove that at some point we learn the sign, and so can start giving actual
 upper and lower bounds. There is a separate `inv` that uses `sign` to construct the proof of
 nonzeroness by searching along the sequence (but isn't guaranteed to terminate). -/
noncomputable def safeInv (x : ComputableℝSeq) (hnz : x.val ≠ 0) : ComputableℝSeq :=
  --TODO currently this passes the sequence to lbInv and ubInv separately, which means we evaluate
  --things twice (and this can lead to exponential slowdown for long series of inverses). This
  --should be bundled
  let signed := x.dropTilSigned hnz
  let hnz' := val_dropTilSigned hnz ▸ hnz
  mk (x := x.val⁻¹)
  (lub := fun n ↦ ⟨⟨(signed.lbInv hnz') n, (signed.ubInv hnz') n⟩,
    Rat.cast_le.mp ((lbInv_correct hnz n).trans (ubInv_correct hnz n))⟩)
  (hcl := (signed.lbInv hnz').2)
  (hcu := (signed.ubInv hnz').2)
  (hlb := lbInv_correct hnz)
  (hub := ubInv_correct hnz)
  (heq := Real.mk_eq.1 ((lbInv_signed_converges hnz).trans (ubInv_signed_converges hnz).symm))

/--
@isnad1 id=eq.1h1v.s4.421b24f202cd from=translated src=- shape=714021e5 vocab=7641908a
-/
@[simp]
theorem val_safeInv {x : ComputableℝSeq} (hnz : x.val ≠ 0) : (x.safeInv hnz).val = x.val⁻¹ := by
  rw [safeInv, mk_val_eq_val]

/--
@isnad1 id=ne.1h1v.s4.a90e13cb46fe from=translated src=- shape=3ed1d281 vocab=a2c8d8d6
-/
theorem val_safeInv_ne_zero {x : ComputableℝSeq} (hnz : x.val ≠ 0) : (x.safeInv hnz).val ≠ 0 := by
  rwa [val_safeInv, ne_eq, inv_eq_zero]

/-- Subtype of sequences with nonzero values. These admit a (terminating) inverse function. -/
def nzSeq := {x : ComputableℝSeq // x.val ≠ 0}
/-- The inverse on the subtype of sequences with nonzero value. -/
noncomputable def invNz : nzSeq → nzSeq :=
  fun x ↦ ⟨x.val.safeInv x.prop, val_safeInv_ne_zero _⟩

/--
@isnad1 id=eq.0h1v.s5.f63dfd8d426e from=translated src=- shape=b6cc2fb8 vocab=a8a5a810
-/
@[simp]
theorem val_invNz (x : nzSeq) : (invNz x).val.val = x.val.val⁻¹ :=
  val_safeInv _

noncomputable instance instNzInv : Inv nzSeq :=
  ⟨invNz⟩

end safeInv

section inv

/-- Inverse of a computable real. Will terminate if the argument is nonzero, or if it is zero and
  the upper and lower bounds become exactly zero at some point. See `ComputableℝSeq.sign`. If you
  want to only call this in a way guaranteed to terminate, use `ComputableℝSeq.safeInv`. -/
noncomputable def inv : ComputableℝSeq → ComputableℝSeq :=
  fun x ↦ match h : x.sign with
  | SignType.pos => x.safeInv (x.sign_pos_iff.1 h).ne'
  | SignType.neg => x.safeInv (x.sign_neg_iff.1 h).ne
  | SignType.zero => 0

noncomputable instance instInv : Inv ComputableℝSeq :=
  ⟨inv⟩

noncomputable instance instDiv : Div ComputableℝSeq :=
  ⟨fun x y ↦ x * y⁻¹⟩

/--
@isnad1 id=eq.0h1v.s3.1ca8e1805685 from=translated src=- shape=5e17aa0a vocab=a8c9fa9d
-/
theorem inv_def (x : ComputableℝSeq) : x⁻¹ = x.inv :=
  rfl

/-- The inverse is equal to the `safeInv`. This is an actual equality of sequences, not just
equivalence.
@isnad1 id=eq.1h1v.s4.4689045310cc from=translated src=- shape=88390f41 vocab=7641908a
-/
theorem inv_eq_safeInv {x : ComputableℝSeq} (hnz : x.val ≠ 0) : x⁻¹ = x.safeInv hnz := by
  rw [inv_def, inv]
  split
  next h => rfl
  next h => rfl
  next h =>
    absurd h
    rwa [sign_zero_iff]

/--
@isnad1 id=eq.0h1v.s3.96e3aa00cdf7 from=translated src=- shape=5a02da31 vocab=114389c3
-/
@[simp]
theorem val_inv (x : ComputableℝSeq) : x⁻¹.val = x.val⁻¹ := by
  by_cases h : x.val = 0
  · rw [h, inv_zero, inv_def, inv]
    split
    next h =>
      simp_all
    next h =>
      simp_all
    next h => exact val_zero
  · rwa [inv_eq_safeInv, val_safeInv]

/--
@isnad1 id=eq.0h2v.s4.43bf8939a1d8 from=translated src=- shape=0438c7a3 vocab=f3dba294
-/
@[simp]
theorem val_div (x y : ComputableℝSeq) : (x / y).val = x.val / y.val := by
  change (x * y⁻¹).val = x.val * y.val⁻¹
  simp

end inv

section semiring --proving that computable real *sequences* form a commutative semiring

/--
@isnad1 id=eq.0h2v.s4.8b7beb09f88d from=translated src=- shape=900bc7c0 vocab=b1518877
-/
theorem add_comm (x y : ComputableℝSeq) : x + y = y + x := by
  ext <;> simp only [ub_add, lb_add] <;> ring_nf

/--
@isnad1 id=eq.0h2v.s4.ce4bb44487dd from=translated src=- shape=900bc7c0 vocab=c4b088a9
-/
theorem mul_comm (x y : ComputableℝSeq) : x * y = y * x := by
  ext n
  <;> simp only [lb_mul, ub_mul]
  · repeat rw [_root_.mul_comm (lb x)]
    repeat rw [_root_.mul_comm (ub x)]
    dsimp
    rw [inf_assoc, inf_assoc]
    congr 1
    rw [← inf_assoc, ← inf_assoc]
    nth_rw 2 [inf_comm]
  · repeat rw [_root_.mul_comm (lb x)]
    repeat rw [_root_.mul_comm (ub x)]
    dsimp
    rw [sup_assoc, sup_assoc]
    congr 1
    rw [← sup_assoc, ← sup_assoc]
    nth_rw 2 [sup_comm]

/--
@isnad1 id=eq.0h2v.s4.f23f1f4e1b7b from=translated src=- shape=c517b5c2 vocab=320ddd00
-/
theorem neg_mul (x y : ComputableℝSeq) : -x * y = -(x * y) := by
  ext
  · rw [lb_neg, lb_mul, ub_mul]
    simp only [lb_neg, ub_neg, CauSeq.coe_inf, CauSeq.coe_mul, CauSeq.coe_neg,
      Pi.inf_apply, Pi.neg_apply, Pi.mul_apply, CauSeq.neg_apply, CauSeq.coe_sup, Pi.sup_apply,
        neg_sup]
    nth_rewrite 2 [inf_comm]
    nth_rewrite 3 [inf_comm]
    ring_nf
  · rw [ub_neg, lb_mul, ub_mul]
    simp only [lb_neg, ub_neg, CauSeq.coe_inf, CauSeq.coe_mul, CauSeq.coe_neg,
      Pi.inf_apply, Pi.neg_apply, Pi.mul_apply, CauSeq.neg_apply, CauSeq.coe_sup, Pi.sup_apply,
      neg_inf]
    nth_rewrite 2 [sup_comm]
    nth_rewrite 3 [sup_comm]
    ring_nf

/--
@isnad1 id=eq.0h2v.s4.bc4c639a9951 from=translated src=- shape=48fe9248 vocab=320ddd00
-/
theorem mul_neg (x y : ComputableℝSeq) : x * -y = -(x * y) := by
  rw [mul_comm, neg_mul, mul_comm]

/--
@isnad1 id=eq.1h2v.s4.74ed798a4399 from=translated src=- shape=4932d469 vocab=be1951ae
-/
theorem neg_eq_of_add (x y : ComputableℝSeq) (h : x + y = 0) : -x = y := by
  have hlb : ∀(x y : ComputableℝSeq), x + y = 0 → x.lb = -y.ub := by
    intro x y h
    ext n
    let ⟨h₁, h₂⟩ := ComputableℝSeq.ext_iff.mp h
    specialize h₁ n
    specialize h₂ n
    simp only [lb_add, ub_add, CauSeq.add_apply, zero_lb, zero_ub, CauSeq.zero_apply,
      CauSeq.neg_apply] at h₁ h₂ ⊢
    have h₃ := x.lb_le_ub n
    have h₄ := y.lb_le_ub n
    linarith (config := {splitNe := true})
  ext
  · rw [lb_neg, CauSeq.neg_apply, hlb y x (add_comm _ _ ▸ h), CauSeq.neg_apply]
  · rw [ub_neg, CauSeq.neg_apply, hlb x y h, CauSeq.neg_apply, neg_neg]

/-- Computable sequences have *most* of the properties of a field, including negation, subtraction,
  multiplication, division, IntCast all working as one would expect, with
  commutativity/associativity, involutive negation, and distributive properties ... except for a
  few crucial facts that a - a ≠ 0,
  a * a⁻¹ ≠ 1, and (a⁻¹)⁻¹ ≠ a. This typeclass collects all these facts together.

TODO could include mul_inv_rev, inv_eq_of_mul, intCast_ofNat, intCast_negSucc. -/
class CompSeqClass (G : Type u) extends
  AddCommMonoid G, CommMagma G, MulZeroOneClass G, Inv G, Div G,
  HasDistribNeg G, SubtractionCommMonoid G, NatCast G, IntCast G, RatCast G

noncomputable instance instSeqCompSeqClass : CompSeqClass ComputableℝSeq := by
  refine {
            natCast := fun n => n
            intCast := fun z => z
            ratCast := fun q => q
            zero := 0
            one := 1
            mul := (· * ·)
            add := (· + ·)
            neg := (- ·)
            sub := (· - ·)
            inv := (·⁻¹)
            div := (· / ·)
            nsmul := nsmulRec
            zsmul := zsmulRec
             --inline several of the "harder" proofs that can't be done automatically
            add_comm := add_comm
            mul_comm := mul_comm
            neg_mul := neg_mul
            mul_neg := mul_neg
            neg_eq_of_add := neg_eq_of_add
            add_assoc := ?_, zero_add := ?_, add_zero := ?_, nsmul_zero := ?_, nsmul_succ := ?_,
            one_mul := ?_, mul_one := ?_, zero_mul := ?_, mul_zero := ?_,
            sub_eq_add_neg := ?_, zsmul_zero' := ?_, zsmul_succ' := ?_, zsmul_neg' := ?_,
            neg_neg := ?_, neg_add_rev := ?_ }
  all_goals
    intros
    first
    | rfl
    | ext
      all_goals
        try simp only [CauSeq.add_apply,
           CauSeq.zero_apply, CauSeq.neg_apply, lb_add, ub_add, zero_ub, zero_lb, ub_neg,
           lb_neg, neg_add_rev, neg_neg, zero_add, add_zero]
        try ring_nf
        try rfl
        try {
          rename_i a n
          simp only [lb_mul, ub_mul, zero_lb, zero_ub, mul_zero, zero_mul, one_lb, one_ub, mul_one,
            one_mul,
            CauSeq.inf_idem, CauSeq.sup_idem, CauSeq.zero_apply, CauSeq.coe_inf, CauSeq.coe_sup,
            Pi.sup_apply, Pi.inf_apply, sup_eq_right, inf_eq_left, lb_le_ub a n]
       }

end semiring

/-- The equivalence relation on ComputableℝSeq's given by converging to the same real value. -/
instance equiv : Setoid (ComputableℝSeq) :=
  ⟨fun f g => f.val = g.val,
    ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩

/--
@isnad1 id=iff.0h2v.s4.730881c3a8c7 from=translated src=- shape=d8adba2e vocab=1568095b
-/
theorem equiv_iff {x y : ComputableℝSeq} : x ≈ y ↔ x.val = y.val :=
  ⟨id, id⟩

end ComputableℝSeq
