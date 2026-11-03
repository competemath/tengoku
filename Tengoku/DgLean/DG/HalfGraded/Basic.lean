import Tengoku.DgLean.DG.Bigraded.Basic
import Tengoku.DgLean.DG.Graded.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Half-graded dg rings

A *half-graded* dg ring (with parameter `k : ℤ`) is a ring `A` graded by `ℤ × ℤ/2` (an internal
degree and a parity), `A = ⨁ (j, ε), A^{j,ε}`, with a differential `d` of bidegree `(k, 1̄)`: `d` is
odd and raises the internal degree by `k`. The sign rule is that of the parity:
`d (a * b) = d a * b + (-1)^{|a|} • (a * d b)` where `|a| ∈ ℤ/2` is the parity of `a`. The main
case is `k = 2`.

Following `docs/CONVENTIONS.md`, half-graded objects are not a second core: they are treated by
regrading into bigraded dg objects (tier 7), which are then dg modules over the weight dg
category (`DG.WeightCategory`). The regrading is the pullback of the `ℤ × ℤ/2`-grading along the
group homomorphism

  `DG.halfDegree k : ℤ × ℤ →+ ℤ × ℤ/2`, `(n, w) ↦ (w + n k, n mod 2)`,

where `n` is a cohomological degree and `w` a weight:
`DG.HalfRegrade ℳ k = ⨁ (n, w), ℳ^{w + n k, n}`.
The differential of bidegree `(k, 1̄)` becomes a differential of bidegree `(1, 0)`, since
`halfDegree k (n + 1, w) = halfDegree k (n, w) + (k, 1̄)`, and the parity of an element placed in
cohomological degree `n` is `n mod 2`, so the Koszul signs of the parity become those of the
cohomological degree. This combines the two regradings of item 1.4 of the roadmap: the
periodization of a `ℤ/2`-grading (`DG.Periodize`, the fibres of `halfDegree k` are the
translates of `(2, -2k) ℤ`) and the division of a grading by the degree of the differential
(`DG.RegradeByDivision`, here the division of the internal degree by the translation by
`(k, 1̄)`). Every element of `A^{j,ε}` appears once in each bidegree `(n, w)` with `n ≡ ε` and
`w + n k = j`; these copies are related by the central unit `u = 1 ∈ A^{0,0̄}` placed in bidegree
`(2, -2k)` (`DG.HalfGradedDGRing.periodUnit`).

## Main definitions

* `DG.coarseGrading β f`: for `f : ι → κ`, the grading of an external direct sum `⨁ i, β i` by
  the fibres of `f`, with its `DirectSum.Decomposition` and the formula for its components
  (`DG.coe_decompose_coarseGrading_apply`).
* `DG.halfDegree k`, `DG.HalfRegrade ℳ k := ⨁ p : ℤ × ℤ, ℳ (halfDegree k p)` for a
  `ℤ × ℤ/2`-graded object `ℳ`, with `DG.HalfRegrade.mk ℳ k p m hm` (an element `m ∈ ℳ^{w + n k, n}`
  placed in bidegree `p = (n, w)`), the cohomological grading `DG.HalfRegrade.cohGrading` and the
  weight grading `DG.HalfRegrade.weightGrading`, and the regraded differential
  `DG.HalfRegrade.dHom`.
* `DG.HalfGradedDGRing A k`: a half-graded dg ring structure on a ring `A`.
* `DG.HalfGradedDGRing.Regraded H`: the regraded ring `⨁ (n, w), A^{w + n k, n}`, with the
  instances `DGAddCommGroup`, `DGRing`, `InternalGrading` and `BigradedDGRing`; its weight dg
  category `DG.WeightCategory H.Regraded` is the dg category whose dg modules are the half-graded
  dg `A`-modules.
* `DG.HalfGradedDGRing.periodUnit H`: the central unit `u` of bidegree `(2, -2k)`, with inverse
  `DG.HalfGradedDGRing.periodUnitInv H` of bidegree `(-2, 2k)`; both are cocycles.
-/

open scoped DG

open DirectSum

namespace DG

/-! ### Coarsening the grading of an external direct sum -/

section Coarse

variable {ι κ : Type*} (β : ι → Type*) [∀ i, AddCommGroup (β i)] (f : ι → κ)

/-- The grading of an external direct sum `⨁ i, β i` by the fibres of a map `f : ι → κ`: the
component of `k : κ` consists of the elements supported on `f⁻¹ {k}`.-/
def coarseGrading (k : κ) : AddSubgroup (⨁ i, β i) where
  carrier := {x | ∀ i, f i ≠ k → x i = 0}
  add_mem' {x y} hx hy i hi := by rw [add_apply, hx i hi, hy i hi, add_zero]
  zero_mem' i _ := DirectSum.zero_apply (β := β) i
  neg_mem' {x} hx i hi := by
    change (-x) i = 0
    rw [DFinsupp.neg_apply, hx i hi, neg_zero]

variable {β f}

/--
@isnad1 id=iff.0h6v.s8.680059a558d7 from=translated src=- shape=64cc965e vocab=e30e54d0
-/
theorem mem_coarseGrading_iff {k : κ} {x : ⨁ i, β i} :
    x ∈ coarseGrading β f k ↔ ∀ i, f i ≠ k → x i = 0 :=
  Iff.rfl

variable [DecidableEq ι]

/--
@isnad1 id=mem.0h6v.s8.5a3ac44a7a20 from=translated src=- shape=299facd1 vocab=9335345c
-/
theorem of_mem_coarseGrading (i : ι) (b : β i) : DirectSum.of β i b ∈ coarseGrading β f (f i) :=
  fun j hj => of_eq_of_ne i j b fun h => hj (h ▸ rfl)

/--
@isnad1 id=mem.1h7v.s8.df72bb9f30b3 from=translated src=- shape=5a4c5112 vocab=9335345c
-/
theorem of_mem_coarseGrading' {i : ι} {k : κ} (h : f i = k) (b : β i) :
    DirectSum.of β i b ∈ coarseGrading β f k :=
  h ▸ of_mem_coarseGrading i b

variable (β f) [DecidableEq κ]

/-- The inclusion of `β i` into the component of `f i` of the coarse grading.-/
def toCoarseGrading (i : ι) : β i →+ coarseGrading β f (f i) where
  toFun b := ⟨DirectSum.of β i b, of_mem_coarseGrading i b⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- The decomposition of `⨁ i, β i` into the components of the coarse grading.-/
def coarseDecompose : (⨁ i, β i) →+ ⨁ k, coarseGrading β f k :=
  DirectSum.toAddMonoid fun i =>
    (DirectSum.of (fun k => coarseGrading β f k) (f i)).comp (toCoarseGrading β f i)

variable {β f}

/--
@isnad1 id=eq.0h7v.s13.487366baff4e from=translated src=- shape=70a9458a vocab=9ee897df
-/
theorem coe_coarseDecompose_apply (x : ⨁ i, β i) (k : κ) (i : ι) :
    ((coarseDecompose β f x k : ⨁ i, β i) i) = if f i = k then x i else 0 := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j b =>
    simp only [coarseDecompose, toAddMonoid_of, AddMonoidHom.comp_apply]
    by_cases hjk : f j = k
    · subst hjk
      rw [of_eq_same]
      change (DirectSum.of β j b) i = _
      by_cases hij : i = j
      · subst hij; simp
      · rw [of_eq_of_ne j i b hij]; simp
    · rw [of_eq_of_ne _ _ _ (Ne.symm hjk), ZeroMemClass.coe_zero, zero_apply]
      by_cases hij : i = j
      · subst hij; simp [hjk]
      · rw [of_eq_of_ne j i b hij]; simp
  | add x y hx hy =>
    rw [map_add, add_apply, AddSubgroup.coe_add, add_apply, hx, hy, add_apply]
    split_ifs <;> simp

/--
@isnad1 id=eq.0h4v.s11.f53a759822f6 from=translated src=- shape=03aea53c vocab=d92d7f3d
-/
theorem coeAddMonoidHom_comp_coarseDecompose :
    (DirectSum.coeAddMonoidHom (coarseGrading β f)).comp (coarseDecompose β f) =
      AddMonoidHom.id _ := by
  refine DirectSum.addHom_ext fun i b => ?_
  simp only [AddMonoidHom.comp_apply, coarseDecompose, toAddMonoid_of, coeAddMonoidHom_of,
    AddMonoidHom.id_apply]
  rfl

/--
@isnad1 id=eq.0h4v.s13.86b9d02767d1 from=translated src=- shape=4be22571 vocab=d92d7f3d
-/
theorem coarseDecompose_comp_coeAddMonoidHom :
    (coarseDecompose β f).comp (DirectSum.coeAddMonoidHom (coarseGrading β f)) =
      AddMonoidHom.id _ := by
  refine DirectSum.addHom_ext fun k y => ?_
  simp only [AddMonoidHom.comp_apply, coeAddMonoidHom_of, AddMonoidHom.id_apply]
  ext k' i
  rw [coe_coarseDecompose_apply]
  by_cases hk : k = k'
  · subst hk
    rw [of_eq_same]
    split_ifs with h
    · rfl
    · exact (y.2 i h).symm
  · rw [of_eq_of_ne _ _ _ (Ne.symm hk), ZeroMemClass.coe_zero, zero_apply]
    split_ifs with h
    · exact y.2 i (h ▸ Ne.symm hk)
    · rfl

variable (β f)

/-- The coarse grading is a decomposition of `⨁ i, β i`.-/
instance instDecompositionCoarseGrading : Decomposition (coarseGrading β f) :=
  Decomposition.ofAddHom _ (coarseDecompose β f) coeAddMonoidHom_comp_coarseDecompose
    coarseDecompose_comp_coeAddMonoidHom

variable {β f}

/-- The components of the coarse decomposition: the component of `k` of `x` is the restriction
of `x` to `f⁻¹ {k}`.
@isnad1 id=eq.0h7v.s12.19d2468df097 from=translated src=- shape=8f290865 vocab=c12d6511
-/
theorem coe_decompose_coarseGrading_apply (x : ⨁ i, β i) (k : κ) (i : ι) :
    ((decompose (coarseGrading β f) x k : ⨁ i, β i) i) = if f i = k then x i else 0 :=
  coe_coarseDecompose_apply x k i

/-- Induction on an element of a component of the coarse grading.
@isnad1 id=var.1h10v.s9.4f183086c662 from=translated src=- shape=c62a9267 vocab=84613f32
-/
theorem coarseGrading_induction {k : κ} {P : (⨁ i, β i) → Prop} (zero : P 0)
    (of : ∀ i (b : β i), f i = k → P (DirectSum.of β i b)) (add : ∀ x y, P x → P y → P (x + y))
    {x : ⨁ i, β i} (hx : x ∈ coarseGrading β f k) : P x := by
  classical
  rw [← DirectSum.sum_support_of x]
  induction x.support using Finset.induction_on with
  | empty => simpa using zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    refine add _ _ ?_ ih
    by_cases h : f i = k
    · exact of i _ h
    · rw [hx i h, map_zero]; exact zero

end Coarse

/-! ### The regrading of a `ℤ × ℤ/2`-graded object -/

/-- The group homomorphism `ℤ × ℤ →+ ℤ × ℤ/2`, `(n, w) ↦ (w + n k, n mod 2)`, sending a
cohomological degree `n` and a weight `w` to an internal degree and a parity.-/
def halfDegree (k : ℤ) : ℤ × ℤ →+ ℤ × ZMod 2 where
  toFun p := (p.2 + p.1 * k, (p.1 : ZMod 2))
  map_zero' := by simp
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Int.cast_add, Prod.mk_add_mk, Prod.mk.injEq, and_true]
    ring

/--
@isnad1 id=eq.0h2v.s8.44971ca2fec8 from=translated src=- shape=a47f5909 vocab=7453ad32
-/
@[simp]
theorem halfDegree_apply (k : ℤ) (p : ℤ × ℤ) :
    halfDegree k p = (p.2 + p.1 * k, (p.1 : ZMod 2)) :=
  rfl

/-- Raising the cohomological degree by `1` raises the half-degree by `(k, 1̄)`.
@isnad1 id=eq.0h2v.s9.3160b3bfde02 from=translated src=- shape=149bdd92 vocab=86cb8d90
-/
theorem halfDegree_add_one_zero (k : ℤ) (p : ℤ × ℤ) :
    halfDegree k (p + (1, 0)) = halfDegree k p + (k, 1) := by
  simp only [halfDegree_apply, Prod.fst_add, Prod.snd_add, add_zero, Int.cast_add, Int.cast_one,
    Prod.mk_add_mk, Prod.mk.injEq, and_true]
  ring

section HalfRegrade

variable {M σ : Type*} [AddCommGroup M] [SetLike σ M] [AddSubgroupClass σ M]

/-- The pullback `p ↦ ℳ (halfDegree k p)` of a `ℤ × ℤ/2`-grading to `ℤ × ℤ`.-/
def halfGrading (ℳ : ℤ × ZMod 2 → σ) (k : ℤ) (p : ℤ × ℤ) : σ := ℳ (halfDegree k p)

omit [AddCommGroup M] [AddSubgroupClass σ M] in
/--
@isnad1 id=iff.0h6v.s7.f877afdbf69a from=translated src=- shape=6168614e vocab=c1bc8321
-/
@[simp]
theorem mem_halfGrading {ℳ : ℤ × ZMod 2 → σ} {k : ℤ} {p : ℤ × ℤ} {m : M} :
    m ∈ halfGrading ℳ k p ↔ m ∈ ℳ (halfDegree k p) := Iff.rfl

/-- The bigraded object attached to a `ℤ × ℤ/2`-graded object `ℳ` and `k : ℤ`: the external
direct sum `⨁ (n, w), ℳ^{w + n k, n mod 2}`, bigraded by the cohomological degree `n` and the
weight `w`.-/
def HalfRegrade (ℳ : ℤ × ZMod 2 → σ) (k : ℤ) : Type _ := ⨁ p : ℤ × ℤ, ↥(halfGrading ℳ k p)

instance (ℳ : ℤ × ZMod 2 → σ) (k : ℤ) : AddCommGroup (HalfRegrade ℳ k) :=
  inferInstanceAs (AddCommGroup (⨁ p : ℤ × ℤ, ↥(halfGrading ℳ k p)))

namespace HalfRegrade

variable (ℳ : ℤ × ZMod 2 → σ) (k : ℤ)

/-- An element `m ∈ ℳ^{w + n k, n}`, placed in bidegree `p = (n, w)` of `HalfRegrade ℳ k`.-/
def mk (p : ℤ × ℤ) (m : M) (hm : m ∈ ℳ (halfDegree k p)) : HalfRegrade ℳ k :=
  DirectSum.of (fun p => ↥(halfGrading ℳ k p)) p ⟨m, hm⟩

/-- The cohomological grading of `HalfRegrade ℳ k`: the elements supported in cohomological
degree `n`.-/
def cohGrading (n : ℤ) : AddSubgroup (HalfRegrade ℳ k) :=
  coarseGrading (fun p => ↥(halfGrading ℳ k p)) Prod.fst n

/-- The weight grading of `HalfRegrade ℳ k`: the elements supported in weight `w`.-/
def weightGrading (w : ℤ) : AddSubgroup (HalfRegrade ℳ k) :=
  coarseGrading (fun p => ↥(halfGrading ℳ k p)) Prod.snd w

instance instDecompositionCohGrading : Decomposition (cohGrading ℳ k) :=
  inferInstanceAs (Decomposition (coarseGrading (fun p => ↥(halfGrading ℳ k p)) Prod.fst))

instance instDecompositionWeightGrading : Decomposition (weightGrading ℳ k) :=
  inferInstanceAs (Decomposition (coarseGrading (fun p => ↥(halfGrading ℳ k p)) Prod.snd))

variable {ℳ k}

/--
@isnad1 id=eq.4h8v.s8.674bd4c9a037 from=translated src=- shape=5e028484 vocab=e4727738
-/
theorem mk_congr {p p' : ℤ × ℤ} (h : p = p') {m m' : M} (h' : m = m')
    (hm : m ∈ ℳ (halfDegree k p)) (hm' : m' ∈ ℳ (halfDegree k p')) :
    mk ℳ k p m hm = mk ℳ k p' m' hm' := by
  subst h h'; rfl

/--
@isnad1 id=eq.0h5v.s7.977eced19670 from=translated src=- shape=873962e5 vocab=4ab02f03
-/
@[simp]
theorem mk_zero (p : ℤ × ℤ) : mk ℳ k p 0 (zero_mem _) = 0 :=
  (DirectSum.of (fun p => ↥(halfGrading ℳ k p)) p).map_zero

/--
@isnad1 id=eq.2h7v.s9.dcc158a74e9e from=translated src=- shape=3868dd3c vocab=e4f03751
-/
theorem mk_add (p : ℤ × ℤ) {m m' : M} (hm : m ∈ ℳ (halfDegree k p))
    (hm' : m' ∈ ℳ (halfDegree k p)) :
    mk ℳ k p (m + m') (add_mem hm hm') = mk ℳ k p m hm + mk ℳ k p m' hm' :=
  (DirectSum.of (fun p => ↥(halfGrading ℳ k p)) p).map_add ⟨m, hm⟩ ⟨m', hm'⟩

/--
@isnad1 id=eq.1h7v.s8.07da90584ff8 from=translated src=- shape=609fdea0 vocab=9550ad7c
-/
theorem mk_zsmul (p : ℤ × ℤ) (c : ℤ) {m : M} (hm : m ∈ ℳ (halfDegree k p)) :
    mk ℳ k p (c • m) (zsmul_mem hm c) = c • mk ℳ k p m hm :=
  (DirectSum.of (fun p => ↥(halfGrading ℳ k p)) p).map_zsmul c ⟨m, hm⟩

/--
@isnad1 id=eq.1h7v.s8.cfc4f2e77a0e from=translated src=- shape=61b4eaec vocab=9b5a85bd
-/
theorem mk_units_smul (p : ℤ × ℤ) (c : ℤˣ) {m : M} (hm : m ∈ ℳ (halfDegree k p)) :
    mk ℳ k p (c • m) (by rw [Units.smul_def]; exact zsmul_mem hm _) = c • mk ℳ k p m hm := by
  simp only [Units.smul_def]
  exact mk_zsmul p (c : ℤ) hm

/--
@isnad1 id=var.0h9v.s8.b2f66b415bb7 from=translated src=- shape=fef61d81 vocab=c72f0bcf
-/
@[elab_as_elim]
theorem induction_on {P : HalfRegrade ℳ k → Prop} (x : HalfRegrade ℳ k) (zero : P 0)
    (mk : ∀ (p : ℤ × ℤ) (m : M) (hm : m ∈ ℳ (halfDegree k p)), P (mk ℳ k p m hm))
    (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  induction x using DirectSum.induction_on with
  | zero => exact zero
  | of p m => exact mk p m.1 m.2
  | add x y hx hy => exact add x y hx hy

/--
@isnad1 id=mem.1h6v.s8.861ce9e53661 from=translated src=- shape=efd3c9de vocab=69a81341
-/
theorem mk_mem_cohGrading (p : ℤ × ℤ) {m : M} (hm : m ∈ ℳ (halfDegree k p)) :
    mk ℳ k p m hm ∈ cohGrading ℳ k p.1 :=
  of_mem_coarseGrading (f := Prod.fst) p _

/--
@isnad1 id=mem.1h6v.s8.d05020e7e2f7 from=translated src=- shape=efd3c9de vocab=9a62324f
-/
theorem mk_mem_weightGrading (p : ℤ × ℤ) {m : M} (hm : m ∈ ℳ (halfDegree k p)) :
    mk ℳ k p m hm ∈ weightGrading ℳ k p.2 :=
  of_mem_coarseGrading (f := Prod.snd) p _

/-- Induction on an element of cohomological degree `n`.
@isnad1 id=var.1h10v.s9.482b908e7985 from=translated src=- shape=83b717d6 vocab=72041273
-/
theorem cohGrading_induction {n : ℤ} {P : HalfRegrade ℳ k → Prop} (zero : P 0)
    (mk : ∀ (w : ℤ) (m : M) (hm : m ∈ ℳ (halfDegree k (n, w))), P (mk ℳ k (n, w) m hm))
    (add : ∀ x y, P x → P y → P (x + y)) {x : HalfRegrade ℳ k} (hx : x ∈ cohGrading ℳ k n) :
    P x :=
  coarseGrading_induction (f := Prod.fst) zero
    (fun (p : ℤ × ℤ) b hp => by rcases p with ⟨n', w⟩; subst hp; exact mk w b.1 b.2) add hx

/-- Induction on an element of weight `w`.
@isnad1 id=var.1h10v.s9.f8c76d5598f8 from=translated src=- shape=03878a6f vocab=ca370083
-/
theorem weightGrading_induction {w : ℤ} {P : HalfRegrade ℳ k → Prop} (zero : P 0)
    (mk : ∀ (n : ℤ) (m : M) (hm : m ∈ ℳ (halfDegree k (n, w))), P (mk ℳ k (n, w) m hm))
    (add : ∀ x y, P x → P y → P (x + y)) {x : HalfRegrade ℳ k} (hx : x ∈ weightGrading ℳ k w) :
    P x :=
  coarseGrading_induction (f := Prod.snd) zero
    (fun (p : ℤ × ℤ) b hp => by rcases p with ⟨n, w'⟩; subst hp; exact mk n b.1 b.2) add hx

/-- The two gradings of `HalfRegrade ℳ k` commute: the weight components of an element of
cohomological degree `n` have cohomological degree `n`.
@isnad1 id=mem.1h7v.s11.82e3fb1da18d from=translated src=- shape=804d92a0 vocab=568d26e9
-/
theorem decompose_weightGrading_mem_cohGrading {n : ℤ} {x : HalfRegrade ℳ k}
    (hx : x ∈ cohGrading ℳ k n) (w : ℤ) :
    (decompose (weightGrading ℳ k) x w : HalfRegrade ℳ k) ∈ cohGrading ℳ k n := by
  intro p hp
  have h := coe_decompose_coarseGrading_apply (β := fun p => ↥(halfGrading ℳ k p))
    (f := Prod.snd) x w p
  refine h.trans ?_
  split_ifs
  · exact hx p hp
  · rfl

/-- The weight grading is homogeneous for the cohomological grading.
@isnad1 id=ishomoge.0h5v.s7.c9aa8147a83d from=translated src=- shape=aa614d87 vocab=337f31c4
-/
theorem isHomogeneous_cohGrading (n : ℤ) :
    SetLike.IsHomogeneous (weightGrading ℳ k) (cohGrading ℳ k n) :=
  fun w _ hx => decompose_weightGrading_mem_cohGrading hx w

section Differential

variable (ℳ k) (d : M →+ M)
  (hd : ∀ {j : ℤ} {ε : ZMod 2} {m : M}, m ∈ ℳ (j, ε) → d m ∈ ℳ (j + k, ε + 1))

omit [AddSubgroupClass σ M] in
include hd in
/--
@isnad1 id=mem.2h7v.s9.60002c134620 from=translated src=- shape=881351dc vocab=9c23214b
-/
theorem d_mem_halfDegree_add {p : ℤ × ℤ} {m : M} (hm : m ∈ ℳ (halfDegree k p)) :
    d m ∈ ℳ (halfDegree k (p + (1, 0))) := by
  rw [halfDegree_add_one_zero]
  exact hd hm

/-- The differential of `HalfRegrade ℳ k` induced by a map `d` of bidegree `(k, 1̄)`: `m` placed
in bidegree `(n, w)` goes to `d m` placed in bidegree `(n + 1, w)`.-/
def dHom : HalfRegrade ℳ k →+ HalfRegrade ℳ k :=
  DirectSum.toAddMonoid fun p =>
    { toFun := fun m => mk ℳ k (p + (1, 0)) (d m) (d_mem_halfDegree_add ℳ k d hd m.2)
      map_zero' := by simp only [ZeroMemClass.coe_zero, map_zero]; exact mk_zero _
      map_add' := fun m m' => by
        simp only [AddMemClass.coe_add, map_add]
        exact mk_add _ _ _ }

variable {d hd}

/--
@isnad1 id=eq.2h7v.s9.8a3921f55bed from=translated src=- shape=3df8ca9b vocab=544b7085
-/
@[simp]
theorem dHom_mk (p : ℤ × ℤ) (m : M) (hm : m ∈ ℳ (halfDegree k p)) :
    dHom ℳ k d hd (mk ℳ k p m hm) =
      mk ℳ k (p + (1, 0)) (d m) (d_mem_halfDegree_add ℳ k d hd hm) :=
  DirectSum.toAddMonoid_of (β := fun p => ↥(halfGrading ℳ k p)) _ p ⟨m, hm⟩

/--
@isnad1 id=mem.2h7v.s9.a7169bf59dc6 from=translated src=- shape=b9c830d4 vocab=adf5c887
-/
theorem dHom_mem_cohGrading {n : ℤ} {x : HalfRegrade ℳ k} (hx : x ∈ cohGrading ℳ k n) :
    dHom ℳ k d hd x ∈ cohGrading ℳ k (n + 1) := by
  refine cohGrading_induction (P := fun x => dHom ℳ k d hd x ∈ cohGrading ℳ k (n + 1)) ?_
    (fun w m hm => ?_) (fun x y hx hy => ?_) hx
  · rw [map_zero]; exact zero_mem _
  · rw [dHom_mk]; exact mk_mem_cohGrading (ℳ := ℳ) (k := k) ((n, w) + (1, 0)) _
  · rw [map_add]; exact add_mem hx hy

/--
@isnad1 id=mem.2h7v.s9.dbe6fa8f7aa9 from=translated src=- shape=3dce1be2 vocab=75fb28dc
-/
theorem dHom_mem_weightGrading {w : ℤ} {x : HalfRegrade ℳ k} (hx : x ∈ weightGrading ℳ k w) :
    dHom ℳ k d hd x ∈ weightGrading ℳ k w := by
  refine weightGrading_induction (P := fun x => dHom ℳ k d hd x ∈ weightGrading ℳ k w) ?_
    (fun n m hm => ?_) (fun x y hx hy => ?_) hx
  · rw [map_zero]; exact zero_mem _
  · rw [dHom_mk]
    have := mk_mem_weightGrading (ℳ := ℳ) (k := k) ((n, w) + (1, 0))
      (d_mem_halfDegree_add ℳ k d hd hm)
    simpa using this
  · rw [map_add]; exact add_mem hx hy

/--
@isnad1 id=eq.2h6v.s10.e9b81d684cbb from=translated src=- shape=6cc93f7e vocab=fc1024d7
-/
theorem dHom_dHom (hdd : ∀ m, d (d m) = 0) (x : HalfRegrade ℳ k) :
    dHom ℳ k d hd (dHom ℳ k d hd x) = 0 := by
  induction x using induction_on with
  | zero => simp
  | mk p m hm => simp only [dHom_mk]; exact (mk_congr rfl (hdd m) _ _).trans (mk_zero _)
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

end Differential

end HalfRegrade

end HalfRegrade

/-! ### Half-graded dg rings -/

/-- A half-graded dg ring structure with parameter `k : ℤ` on a ring `A`: a `ℤ × ℤ/2`-grading
`A = ⨁ (j, ε), A^{j,ε}` (internal degree `j`, parity `ε`) which is a ring grading, and a
differential `d` of bidegree `(k, 1̄)` with `d ∘ d = 0`, satisfying the Leibniz rule with the sign
of the parity, `d (a * b) = d a * b + (-1)^ε • (a * d b)` for `a ∈ A^{j,ε}`; the sign is written
`koszulSign n` for an integer `n` with `n mod 2 = ε`.-/
structure HalfGradedDGRing (A : Type*) [Ring A] (k : ℤ) where
  /-- The homogeneous components `A^{j,ε}`.-/
  hgrading : ℤ × ZMod 2 → AddSubgroup A
  /-- The grading is an internal direct sum decomposition.-/
  [decomposition : DirectSum.Decomposition hgrading]
  /-- The grading is a ring grading.-/
  [gradedMonoid : SetLike.GradedMonoid hgrading]
  /-- The differential, of bidegree `(k, 1̄)`.-/
  hd : A →+ A
  hd_mem : ∀ {j : ℤ} {ε : ZMod 2} {a : A}, a ∈ hgrading (j, ε) → hd a ∈ hgrading (j + k, ε + 1)
  hd_hd : ∀ a : A, hd (hd a) = 0
  hd_mul : ∀ {j n : ℤ} {a : A}, a ∈ hgrading (j, (n : ZMod 2)) → ∀ b : A,
    hd (a * b) = hd a * b + koszulSign n • (a * hd b)

attribute [instance] HalfGradedDGRing.decomposition HalfGradedDGRing.gradedMonoid

namespace HalfGradedDGRing

variable {A : Type*} [Ring A] {k : ℤ} (H : HalfGradedDGRing A k)

/--
@isnad1 id=gradedmo.0h3v.s5.38ad8a0937ca from=translated src=- shape=a715339b vocab=011e1067
-/
instance gradedMonoid_halfGrading : SetLike.GradedMonoid (halfGrading H.hgrading k) where
  one_mem := by
    rw [mem_halfGrading, map_zero]
    exact SetLike.GradedOne.one_mem
  mul_mem p q a b ha hb := by
    rw [mem_halfGrading, map_add]
    exact SetLike.GradedMul.mul_mem ha hb

/-- The regraded ring `⨁ (n, w), A^{w + n k, n mod 2}` of a half-graded dg ring, bigraded by the
cohomological degree `n` and the weight `w`, with the differential of bidegree `(1, 0)` induced by
`d`.-/
def Regraded : Type _ := HalfRegrade H.hgrading k

instance : Ring H.Regraded :=
  inferInstanceAs (Ring (⨁ p : ℤ × ℤ, ↥(halfGrading H.hgrading k p)))

/-- An element `a ∈ A^{w + n k, n}` placed in bidegree `p = (n, w)` of the regraded ring.-/
def place (p : ℤ × ℤ) (a : A) (ha : a ∈ H.hgrading (halfDegree k p)) : H.Regraded :=
  HalfRegrade.mk H.hgrading k p a ha

variable {H}

/--
@isnad1 id=eq.4h7v.s8.df077f705ea6 from=translated src=- shape=991abd87 vocab=88495c1c
-/
theorem place_congr {p p' : ℤ × ℤ} (h : p = p') {a a' : A} (h' : a = a')
    (ha : a ∈ H.hgrading (halfDegree k p)) (ha' : a' ∈ H.hgrading (halfDegree k p')) :
    H.place p a ha = H.place p' a' ha' :=
  HalfRegrade.mk_congr h h' ha ha'

/--
@isnad1 id=eq.0h4v.s6.8d2549b4e6b8 from=translated src=- shape=4b3d2859 vocab=31ed8f60
-/
@[simp]
theorem place_zero (p : ℤ × ℤ) : H.place p 0 (zero_mem _) = 0 :=
  HalfRegrade.mk_zero p

/--
@isnad1 id=eq.2h6v.s9.7f37959430ae from=translated src=- shape=d5ea97cc vocab=17da7543
-/
theorem place_add (p : ℤ × ℤ) {a a' : A} (ha : a ∈ H.hgrading (halfDegree k p))
    (ha' : a' ∈ H.hgrading (halfDegree k p)) :
    H.place p (a + a') (add_mem ha ha') = H.place p a ha + H.place p a' ha' :=
  HalfRegrade.mk_add p ha ha'

/--
@isnad1 id=eq.4h8v.s10.20433db666e4 from=translated src=- shape=f3ebd17d vocab=c71e014f
-/
theorem place_add_of_eq {p₁ p₂ p : ℤ × ℤ} (h₁ : p₁ = p) (h₂ : p₂ = p) {a a' : A}
    (ha : a ∈ H.hgrading (halfDegree k p₁)) (ha' : a' ∈ H.hgrading (halfDegree k p₂)) :
    H.place p₁ a ha + H.place p₂ a' ha' =
      H.place p (a + a') (by subst h₁ h₂; exact add_mem ha ha') := by
  subst h₁ h₂
  exact (place_add _ ha ha').symm

/--
@isnad1 id=eq.1h6v.s8.0827b2fb8f21 from=translated src=- shape=6be1192d vocab=b1bd1226
-/
theorem place_units_smul (p : ℤ × ℤ) (c : ℤˣ) {a : A} (ha : a ∈ H.hgrading (halfDegree k p)) :
    H.place p (c • a) (by rw [Units.smul_def]; exact zsmul_mem ha _) = c • H.place p a ha :=
  HalfRegrade.mk_units_smul p c ha

/--
@isnad1 id=eq.2h7v.s9.0367cee6c548 from=translated src=- shape=eaeb18e0 vocab=0934904d
-/
theorem place_mul_place {p q : ℤ × ℤ} {a b : A} (ha : a ∈ H.hgrading (halfDegree k p))
    (hb : b ∈ H.hgrading (halfDegree k q)) :
    H.place p a ha * H.place q b hb =
      H.place (p + q) (a * b) (show a * b ∈ H.hgrading (halfDegree k (p + q)) from
        SetLike.GradedMul.mul_mem (A := halfGrading H.hgrading k) ha hb) :=
  DirectSum.of_mul_of _ _

/--
@isnad1 id=eq.0h3v.s6.e78df2537ebd from=translated src=- shape=8f99f733 vocab=ea2efef4
-/
theorem one_eq_place : (1 : H.Regraded) =
    H.place 0 1 (SetLike.GradedOne.one_mem (A := halfGrading H.hgrading k)) :=
  rfl

/--
@isnad1 id=var.0h8v.s8.33d4c93b79e8 from=translated src=- shape=9df1ff54 vocab=42177beb
-/
@[elab_as_elim]
theorem induction_on {P : H.Regraded → Prop} (x : H.Regraded) (zero : P 0)
    (mk : ∀ (p : ℤ × ℤ) (a : A) (ha : a ∈ H.hgrading (halfDegree k p)), P (H.place p a ha))
    (add : ∀ x y, P x → P y → P (x + y)) : P x :=
  HalfRegrade.induction_on x zero mk add

variable (H)

/-- The regraded ring is a dg abelian group, graded by the cohomological degree, with the
differential induced by `d`.-/
instance instDGAddCommGroup : DGAddCommGroup H.Regraded where
  grading := HalfRegrade.cohGrading H.hgrading k
  decomposition := HalfRegrade.instDecompositionCohGrading H.hgrading k
  d := HalfRegrade.dHom H.hgrading k H.hd H.hd_mem
  d_mem' := HalfRegrade.dHom_mem_cohGrading _ _
  d_d' := HalfRegrade.dHom_dHom _ _ H.hd_hd

/-- The weight grading of the regraded ring.-/
instance instInternalGrading : InternalGrading H.Regraded where
  wgrading := HalfRegrade.weightGrading H.hgrading k
  wdecomposition := HalfRegrade.instDecompositionWeightGrading H.hgrading k
  isHomogeneous_grading' := HalfRegrade.isHomogeneous_cohGrading
  d_mem_wgrading' := HalfRegrade.dHom_mem_weightGrading _ _

variable {H}

/--
@isnad1 id=mem.1h5v.s8.a7e7467bcceb from=translated src=- shape=0fdb72b0 vocab=94c25c51
-/
theorem place_mem_grading (p : ℤ × ℤ) {a : A} (ha : a ∈ H.hgrading (halfDegree k p)) :
    H.place p a ha ∈ grading (M := H.Regraded) p.1 :=
  HalfRegrade.mk_mem_cohGrading p ha

/--
@isnad1 id=mem.1h5v.s8.b4072e94d24c from=translated src=- shape=3a97e8ee vocab=e45c8b57
-/
theorem place_mem_wgrading (p : ℤ × ℤ) {a : A} (ha : a ∈ H.hgrading (halfDegree k p)) :
    H.place p a ha ∈ wgrading (M := H.Regraded) p.2 :=
  HalfRegrade.mk_mem_weightGrading p ha

/--
@isnad1 id=eq.1h5v.s9.749773b9a409 from=translated src=- shape=89473532 vocab=a0d26dc2
-/
@[simp]
theorem d_place (p : ℤ × ℤ) (a : A) (ha : a ∈ H.hgrading (halfDegree k p)) :
    d (H.place p a ha) =
      H.place (p + (1, 0)) (H.hd a)
        (HalfRegrade.d_mem_halfDegree_add H.hgrading k H.hd H.hd_mem ha) :=
  HalfRegrade.dHom_mk H.hgrading k p a ha

/-- Induction on an element of cohomological degree `n`.
@isnad1 id=var.1h9v.s8.cf227fcc6d52 from=translated src=- shape=4ca64aff vocab=6dce18d9
-/
theorem grading_induction {n : ℤ} {P : H.Regraded → Prop} (zero : P 0)
    (mk : ∀ (w : ℤ) (a : A) (ha : a ∈ H.hgrading (halfDegree k (n, w))), P (H.place (n, w) a ha))
    (add : ∀ x y, P x → P y → P (x + y)) {x : H.Regraded} (hx : x ∈ grading n) : P x :=
  HalfRegrade.cohGrading_induction zero mk add hx

/-- Induction on an element of weight `w`.
@isnad1 id=var.1h9v.s8.d0c136166928 from=translated src=- shape=9e47d778 vocab=07d4a4c5
-/
theorem wgrading_induction {w : ℤ} {P : H.Regraded → Prop} (zero : P 0)
    (mk : ∀ (n : ℤ) (a : A) (ha : a ∈ H.hgrading (halfDegree k (n, w))), P (H.place (n, w) a ha))
    (add : ∀ x y, P x → P y → P (x + y)) {x : H.Regraded} (hx : x ∈ wgrading w) : P x :=
  HalfRegrade.weightGrading_induction zero mk add hx

variable (H)

/-- The weight grading of the regraded ring is a ring grading.
@isnad1 id=bigraded.0h3v.s5.a8ccdabb97ef from=translated src=- shape=54d0cce0 vocab=efd0cdce
-/
instance instBigradedDGRing : BigradedDGRing H.Regraded where
  one_mem := by
    rw [one_eq_place]
    exact place_mem_wgrading (H := H) 0 _
  mul_mem i j x y hx hy := by
    refine wgrading_induction (P := fun x => x * y ∈ wgrading (i + j)) (by simp)
      (fun n a ha => ?_) (fun x x' h h' => by rw [add_mul]; exact add_mem h h') hx
    refine wgrading_induction (P := fun y => H.place (n, i) a ha * y ∈ wgrading (i + j)) (by simp)
      (fun n' b hb => ?_) (fun y y' h h' => by rw [mul_add]; exact add_mem h h') hy
    rw [place_mul_place]
    exact place_mem_wgrading (H := H) ((n, i) + (n', j)) _

/-- The regraded ring is a dg ring: the Leibniz rule for the cohomological degree is the Leibniz
rule of `A` for the parity.
@isnad1 id=dgring.0h3v.s4.de9ba11db435 from=translated src=- shape=54d0cce0 vocab=c2f6fbf4
-/
instance instDGRing : DGRing H.Regraded where
  one_mem := by
    rw [one_eq_place]
    exact place_mem_grading (H := H) 0 _
  mul_mem i j x y hx hy := by
    refine grading_induction (P := fun x => x * y ∈ grading (i + j)) (by simp)
      (fun w a ha => ?_) (fun x x' h h' => by rw [add_mul]; exact add_mem h h') hx
    refine grading_induction
      (P := fun y => H.place (i, w) a ha * y ∈ grading (i + j)) (by simp)
      (fun w' b hb => ?_) (fun y y' h h' => by rw [mul_add]; exact add_mem h h') hy
    rw [place_mul_place]
    exact place_mem_grading (H := H) ((i, w) + (j, w')) _
  d_mul' {n x} hx y := by
    refine grading_induction
      (P := fun x => d (x * y) =
        d x * y + koszulSign n • (x * d y)) (by simp)
      (fun w a ha => ?_) (fun x x' h h' => by
        rw [add_mul, d_add, h, h', d_add, add_mul, add_mul, smul_add]; abel) hx
    induction y using induction_on with
    | zero => simp
    | mk q b hb =>
      rw [place_mul_place, d_place, d_place, d_place, place_mul_place, place_mul_place,
        ← place_units_smul, place_add_of_eq (p := (n, w) + q + (1, 0)) (by abel) (by abel)]
      exact place_congr rfl (H.hd_mul ha b) _ _
    | add y y' hy hy' => rw [mul_add, d_add, hy, hy', d_add, mul_add, mul_add, smul_add]; abel

/-! ### The periodicity unit -/

section PeriodUnit

variable {H}

/--
@isnad1 id=eq.0h3v.s6.491558766855 from=translated src=- shape=e4d31fc2 vocab=3833b7ae
-/
theorem hd_one : H.hd 1 = 0 := by
  have h := H.hd_mul (j := 0) (n := 0) (SetLike.GradedOne.one_mem (A := H.hgrading)) 1
  rw [mul_one, one_mul, koszulSign_zero, one_smul, mul_one] at h
  exact left_eq_add.mp h

/--
@isnad1 id=mem.1h4v.s9.6063a1adc4aa from=translated src=- shape=054985b1 vocab=863bcd9e
-/
theorem one_mem_of_halfDegree_eq_zero {p : ℤ × ℤ} (hp : halfDegree k p = 0) :
    (1 : A) ∈ H.hgrading (halfDegree k p) := by
  rw [hp]; exact SetLike.GradedOne.one_mem

/--
@isnad1 id=eq.0h1v.s8.6ba554661f93 from=translated src=- shape=1d5eecaa vocab=9ccb8888
-/
theorem halfDegree_two : halfDegree k (2, -2 * k) = 0 := by
  simp only [halfDegree_apply, Int.cast_ofNat, Prod.mk_eq_zero]
  exact ⟨by ring, rfl⟩

/--
@isnad1 id=eq.0h1v.s8.a8a9d8896b09 from=translated src=- shape=4d37d42c vocab=9ccb8888
-/
theorem halfDegree_neg_two : halfDegree k (-2, 2 * k) = 0 := by
  simp only [halfDegree_apply, Int.cast_neg, Int.cast_ofNat, Prod.mk_eq_zero]
  exact ⟨by ring, rfl⟩

variable (H)

/-- The periodicity unit `u` of the regraded ring: `1 ∈ A^{0,0̄}` placed in bidegree `(2, -2k)`
(cohomological degree `2`, weight `-2k`). It is central, a cocycle, and invertible with inverse
`DG.HalfGradedDGRing.periodUnitInv`. Multiplication by `u` identifies the copies
`(n, w)` and `(n + 2, w - 2k)` of `A^{w + n k, n}`.-/
def periodUnit : H.Regraded :=
  H.place (2, -2 * k) 1 (one_mem_of_halfDegree_eq_zero halfDegree_two)

/-- The inverse `u⁻¹` of the periodicity unit: `1 ∈ A^{0,0̄}` placed in bidegree `(-2, 2k)`.-/
def periodUnitInv : H.Regraded :=
  H.place (-2, 2 * k) 1 (one_mem_of_halfDegree_eq_zero halfDegree_neg_two)

variable {H}

/--
@isnad1 id=eq.1h5v.s8.843a21440b21 from=translated src=- shape=404704aa vocab=8784ed47
-/
theorem place_mul_periodUnit (p : ℤ × ℤ) {a : A} (ha : a ∈ H.hgrading (halfDegree k p)) :
    H.place p a ha * H.periodUnit =
      H.place (p + (2, -2 * k)) a (by rw [map_add, halfDegree_two, add_zero]; exact ha) := by
  rw [periodUnit, place_mul_place]
  exact place_congr rfl (mul_one a) _ _

/--
@isnad1 id=eq.1h5v.s8.e28e488182c6 from=translated src=- shape=c2e4fde3 vocab=554712fd
-/
theorem place_mul_periodUnitInv (p : ℤ × ℤ) {a : A} (ha : a ∈ H.hgrading (halfDegree k p)) :
    H.place p a ha * H.periodUnitInv =
      H.place (p + (-2, 2 * k)) a (by rw [map_add, halfDegree_neg_two, add_zero]; exact ha) := by
  rw [periodUnitInv, place_mul_place]
  exact place_congr rfl (mul_one a) _ _

/--
@isnad1 id=eq.1h5v.s8.b7dafaecc806 from=translated src=- shape=f58b7a66 vocab=554712fd
-/
theorem periodUnitInv_mul_place (p : ℤ × ℤ) {a : A} (ha : a ∈ H.hgrading (halfDegree k p)) :
    H.periodUnitInv * H.place p a ha =
      H.place (p + (-2, 2 * k)) a (by rw [map_add, halfDegree_neg_two, add_zero]; exact ha) := by
  rw [periodUnitInv, place_mul_place]
  exact place_congr (add_comm _ _) (one_mul a) _ _

variable (H)

/--
@isnad1 id=eq.0h3v.s6.6d3f1af6efba from=translated src=- shape=3f4ac762 vocab=09cc810f
-/
theorem periodUnit_mul_periodUnitInv : H.periodUnit * H.periodUnitInv = 1 := by
  rw [periodUnit, place_mul_periodUnitInv, one_eq_place]
  exact place_congr (by ext <;> simp) rfl _ _

/--
@isnad1 id=eq.0h3v.s6.d6c0d5f5f9e8 from=translated src=- shape=3f4ac762 vocab=09cc810f
-/
theorem periodUnitInv_mul_periodUnit : H.periodUnitInv * H.periodUnit = 1 := by
  rw [periodUnitInv, place_mul_periodUnit, one_eq_place]
  exact place_congr (by ext <;> simp) rfl _ _

/-- The inverse of the periodicity unit is central.
@isnad1 id=eq.0h4v.s6.dd60f91091e1 from=translated src=- shape=45d2d7f2 vocab=42628c00
-/
theorem periodUnitInv_mul_comm (x : H.Regraded) : H.periodUnitInv * x = x * H.periodUnitInv := by
  induction x using induction_on with
  | zero => simp
  | mk p a ha => rw [periodUnitInv_mul_place, place_mul_periodUnitInv]
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]

/--
@isnad1 id=mem.0h3v.s6.defcf8ee3ec6 from=translated src=- shape=f72a4b9b vocab=75a604ca
-/
theorem periodUnit_mem_grading : H.periodUnit ∈ grading (M := H.Regraded) 2 :=
  place_mem_grading (H := H) (2, -2 * k) _

/--
@isnad1 id=mem.0h3v.s7.4a3f4a0334f6 from=translated src=- shape=80895c9a vocab=9c382a30
-/
theorem periodUnit_mem_wgrading :
    H.periodUnit ∈ wgrading (M := H.Regraded) (-2 * k) :=
  place_mem_wgrading (H := H) (2, -2 * k) _

/--
@isnad1 id=mem.0h3v.s7.7712f8953ca6 from=translated src=- shape=4e2e77fe vocab=9296b858
-/
theorem periodUnitInv_mem_grading :
    H.periodUnitInv ∈ grading (M := H.Regraded) (-2) :=
  place_mem_grading (H := H) (-2, 2 * k) _

/--
@isnad1 id=mem.0h3v.s7.ae992e7eee54 from=translated src=- shape=9c917ed9 vocab=6cd72a7e
-/
theorem periodUnitInv_mem_wgrading :
    H.periodUnitInv ∈ wgrading (M := H.Regraded) (2 * k) :=
  place_mem_wgrading (H := H) (-2, 2 * k) _

/--
@isnad1 id=eq.0h3v.s8.ac7f86f163c4 from=translated src=- shape=13071d6c vocab=bd90d066
-/
@[simp]
theorem d_periodUnit : d H.periodUnit = 0 := by
  rw [periodUnit, d_place]
  exact (place_congr rfl hd_one _ _).trans (place_zero _)

/--
@isnad1 id=eq.0h3v.s8.47df44469a4a from=translated src=- shape=13071d6c vocab=c7823a26
-/
@[simp]
theorem d_periodUnitInv : d H.periodUnitInv = 0 := by
  rw [periodUnitInv, d_place]
  exact (place_congr rfl hd_one _ _).trans (place_zero _)

end PeriodUnit

end HalfGradedDGRing

end DG
