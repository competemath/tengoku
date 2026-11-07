/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Sadofschi Costa, Quang Dao
-/
module

public import Tengoku.Seed.Data.Finsupp.Fin
public import Tengoku.Seed.Algebra.BigOperators.Finsupp.Fin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Tuple operations on maps `Fin n →₀ M`

We interpret maps `Fin n →₀ M` as `n`-tuples of elements of `M`, and define the following
operations:
* `Finsupp.tail` : the tail of a map `Fin (n + 1) →₀ M`, i.e., its last `n` entries;
* `Finsupp.init` : the initial of a map `Fin n →₀ M`, i.e., its first `n - 1` entries;
* `Finsupp.removeNth` : removing an element at a given entry of a map `Fin (n + 1) →₀ M`;
* `Finsupp.cons` : adding an element at the beginning of an `n`-tuple, to get an `n + 1`-tuple;
* `Finsupp.snoc` : adding an element at the end of an `n`-tuple, to get an `n + 1`-tuple;
* `Finsupp.insertNth` : adding an element at a given entry of an `n`-tuple, to get an `n + 1`-tuple.

In this context, we prove some usual properties of these operations, analogous to those of
`Data.Fin.Tuple.Basic`.
-/

@[expose] public section

open Function

noncomputable section

namespace Finsupp

variable {n : ℕ} {M : Type*} [Zero M]

-- /-- `tail` for maps `Fin (n + 1) →₀ M`. See `Fin.tail` for more details. -/
-- def tail (s : Fin (n + 1) →₀ M) : Fin n →₀ M :=
--   Finsupp.equivFunOnFinite.symm (Fin.tail s)

/-- `init` for maps `Fin n →₀ M`. See `Fin.init` for more details.-/
def init (s : Fin (n + 1) →₀ M) : Fin n →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.init s)

/-- `removeNth` for maps `Fin n →₀ M`. See `Fin.removeNth` for more details.-/
def removeNth (p : Fin (n + 1)) (s : Fin (n + 1) →₀ M) : Fin n →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.removeNth p s : Fin n → M)

-- /-- `cons` for maps `Fin n →₀ M`. See `Fin.cons` for more details. -/
-- def cons (y : M) (s : Fin n →₀ M) : Fin (n + 1) →₀ M :=
--   Finsupp.equivFunOnFinite.symm (Fin.cons y s : Fin (n + 1) → M)

/-- `snoc` for maps `Fin n →₀ M`. See `Fin.snoc` for more details.-/
def snoc (s : Fin n →₀ M) (y : M) : Fin (n + 1) →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.snoc s y : Fin (n + 1) → M)

/-- `insertNth` for maps `Fin n →₀ M`. See `Fin.insertNth` for more details.-/
def insertNth (p : Fin (n + 1)) (y : M) (s : Fin n →₀ M) : Fin (n + 1) →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.insertNth p y s : Fin (n + 1) → M)

section Remove

variable (p : Fin (n + 1)) (s : Fin (n + 1) →₀ M) (y : M) (i : Fin n)

/--
@isnad1 id=eq.0h5v.s7.6b01d247328e from=translated src=- shape=7b90c9b8 vocab=7df31446
-/
@[simp]
theorem removeNth_apply : removeNth p s i = s (p.succAbove i) := rfl

/--
@isnad1 id=eq.0h3v.s6.fd85dab89f01 from=translated src=- shape=d1bd8e21 vocab=6f9cfef9
-/
@[simp]
theorem removeNth_zero : removeNth 0 s = tail s := rfl

/--
@isnad1 id=eq.0h3v.s5.b2f41a1ce44b from=translated src=- shape=f089f5f8 vocab=e9edd1d8
-/
@[simp]
theorem removeNth_last : removeNth (Fin.last n) s = init s := by simp [removeNth, init]

/-- Updating the `i`-th entry does not affect removing the `i`-th entry.
@isnad1 id=eq.0h5v.s6.36b335a6ac14 from=translated src=- shape=3d9e47a8 vocab=b29dfa65
-/
@[simp]
theorem removeNth_update : removeNth p (update s p y) = removeNth p s := by simp [removeNth]

-- @[simp]
-- theorem tail_apply : tail s i = s i.succ := rfl

-- @[simp]
-- theorem tail_update_zero : tail (update s 0 y) = tail s := by simp [tail]

-- @[simp]
-- theorem tail_update_succ : tail (update s i.succ y) = update (tail s) i y := by ext; simp [tail]

/--
@isnad1 id=eq.0h4v.s6.ef0700e73e48 from=translated src=- shape=53e9e8c7 vocab=67da2c7f
-/
@[simp]
theorem init_apply : init s i = s i.castSucc := rfl

/--
@isnad1 id=eq.0h4v.s5.6aaf2b6aff06 from=translated src=- shape=f2a86e13 vocab=cefcd77c
-/
@[simp]
theorem init_update_last : init (update s (Fin.last n) y) = init s := by simp [init]

/--
@isnad1 id=eq.0h5v.s6.337a5c51e6dd from=translated src=- shape=cc385a1a vocab=280481cd
-/
@[simp]
theorem init_update_castSucc : init (update s i.castSucc y) = update (init s) i y := by
  ext; simp [init]

/--
@isnad1 id=eq.0h3v.s6.41e34483b528 from=translated src=- shape=36dc1bc6 vocab=61c90c0a
-/
theorem tail_init_eq_init_tail (s : Fin (n + 2) →₀ M) : tail (init s) = init (tail s) := by
  simp only [tail, init, coe_equivFunOnFinite_symm, Fin.tail_init_eq_init_tail]

end Remove

section Add

variable (p : Fin (n + 1)) (y : M) (t : Fin (n + 1) →₀ M) (s : Fin n →₀ M) (i : Fin n)

-- @[simp]
-- theorem cons_zero : cons y s 0 = y := rfl

-- @[simp]
-- theorem cons_succ : cons y s i.succ = s i := rfl

/--
@isnad1 id=eq.0h4v.s6.e5bffea15bb7 from=translated src=- shape=e70740eb vocab=49401d3f
-/
@[simp]
theorem snoc_last : snoc s y (Fin.last n) = y := by simp [snoc]

/--
@isnad1 id=eq.0h5v.s6.1e93713bce14 from=translated src=- shape=07cb990a vocab=cf806ccb
-/
@[simp]
theorem snoc_castSucc : snoc s y i.castSucc = s i := by simp [snoc]

/--
@isnad1 id=eq.0h4v.s6.dfc76a3cf5ae from=translated src=- shape=e165f800 vocab=3e9a0052
-/
@[simp]
theorem insertNth_zero : insertNth 0 y s = cons y s := by simp [insertNth, cons]

/--
@isnad1 id=eq.0h4v.s5.f4f0e209e05a from=translated src=- shape=651bc05f vocab=f7aec340
-/
@[simp]
theorem insertNth_last : insertNth (Fin.last n) y s = snoc s y := by simp [insertNth, snoc]

/--
@isnad1 id=eq.0h5v.s6.58501834e30d from=translated src=- shape=f0b6c99a vocab=ec789b12
-/
@[simp]
theorem insertNth_apply_same : insertNth p y s p = y := by simp [insertNth]

/--
@isnad1 id=eq.0h6v.s7.22a8183a77bb from=translated src=- shape=2ccd7dc2 vocab=a2467fb7
-/
@[simp]
theorem insertNth_apply_succAbove : insertNth p y s (p.succAbove i) = s i := by simp [insertNth]

-- @[simp]
-- theorem tail_cons : tail (cons y s) = s :=
--   ext fun k => by simp only [tail_apply, cons_succ]

-- @[simp]
-- theorem cons_tail : cons (t 0) (tail t) = t := by
--   ext a
--   by_cases c_a : a = 0
--   · rw [c_a, cons_zero]
--   · rw [← Fin.succ_pred a c_a, cons_succ, ← tail_apply]

/--
@isnad1 id=eq.0h4v.s5.35492f11a579 from=translated src=- shape=125d889e vocab=1dc42630
-/
@[simp]
theorem init_snoc : init (snoc s y) = s := by
  simp only [init, snoc, coe_equivFunOnFinite_symm, Fin.init_snoc, equivFunOnFinite_symm_coe]

/--
@isnad1 id=eq.0h3v.s6.e86cddbff1ab from=translated src=- shape=e6891325 vocab=bb14b7e6
-/
@[simp]
theorem snoc_init_self : snoc (init t) (t (Fin.last n)) = t := by
  have : (⇑(equivFunOnFinite.symm (Fin.init (⇑t))) : Fin n → M) = Fin.init ⇑t := rfl
  simp only [snoc, init, this, Fin.snoc_init_self, equivFunOnFinite_symm_coe]

/--
@isnad1 id=eq.0h5v.s6.2916d11d8948 from=translated src=- shape=6a7b5cac vocab=65cb8499
-/
@[simp]
theorem insertNth_removeNth : insertNth p y (removeNth p t) = update t p y := by
  simp [insertNth, removeNth, coe_equivFunOnFinite_symm, Fin.insertNth_removeNth, update]
  have : Function.update (⇑t) p y = ⇑(update t p y) := by simp only [coe_update]
  rw [this, equivFunOnFinite_symm_coe, update]

/--
@isnad1 id=eq.0h4v.s7.2db9dc8d15c7 from=translated src=- shape=caa2d1d1 vocab=620159e6
-/
theorem insertNth_self_removeNth : insertNth p (t p) (removeNth p t) = t := by
  simp [insertNth, removeNth]

-- @[simp]
-- theorem cons_zero_zero : cons 0 (0 : Fin n →₀ M) = 0 := by
--   ext a
--   by_cases c : a = 0
--   · simp only [c, cons_zero, coe_zero, Pi.zero_apply]
--   · rw [← Fin.succ_pred a c, cons_succ]
--     simp only [coe_zero, Pi.zero_apply, Fin.succ_pred]

/--
@isnad1 id=eq.0h2v.s6.d5cb592a722b from=translated src=- shape=92d6351f vocab=c4992080
-/
@[simp]
theorem snoc_zero_zero : snoc (0 : Fin n →₀ M) 0 = 0 := by
  ext a
  simp only [snoc, coe_zero, coe_equivFunOnFinite_symm, Fin.snoc, Fin.castSucc_castLT,
    Pi.zero_apply, cast_eq, dite_eq_ite, ite_self]

/--
@isnad1 id=eq.0h3v.s6.a3bcf93d00b4 from=translated src=- shape=e69b65af vocab=d7d13a08
-/
@[simp]
theorem insertNth_zero_zero : insertNth p 0 (0 : Fin n →₀ M) = 0 := by
  ext a
  simp only [insertNth, coe_zero, coe_equivFunOnFinite_symm, Fin.insertNth,
    Fin.succAboveCases, eq_rec_constant, Pi.zero_apply, dite_eq_ite, ite_self]

variable {y} {s}

-- theorem cons_ne_zero_of_left (h : y ≠ 0) : cons y s ≠ 0 := by
--   contrapose! h with c
--   rw [← cons_zero y s, c, Finsupp.coe_zero, Pi.zero_apply]

-- theorem cons_ne_zero_of_right (h : s ≠ 0) : cons y s ≠ 0 := by
--   contrapose! h with c
--   ext a
--   simp only [← cons_succ y s a, c, coe_zero, Pi.zero_apply]

-- theorem cons_ne_zero_iff : cons y s ≠ 0 ↔ y ≠ 0 ∨ s ≠ 0 := by
--   refine ⟨fun h => ?_, fun h => h.casesOn cons_ne_zero_of_left cons_ne_zero_of_right⟩
--   refine imp_iff_not_or.1 fun h' c => h ?_
--   rw [h', c, Finsupp.cons_zero_zero]

/--
@isnad1 id=ne.1h4v.s6.2e3c5cc981c8 from=translated src=- shape=3a11aaa3 vocab=c4992080
-/
theorem snoc_ne_zero_of_left (h : s ≠ 0) : snoc s y ≠ 0 := by
  contrapose! h with c
  ext a
  simp only [← snoc_castSucc y s a, c, coe_zero, Pi.zero_apply]

/--
@isnad1 id=ne.1h4v.s6.100563ddd15a from=translated src=- shape=9e39a541 vocab=c4992080
-/
theorem snoc_ne_zero_of_right (h : y ≠ 0) : snoc s y ≠ 0 := by
  contrapose! h with c
  rw [← snoc_last y s, c, Finsupp.coe_zero, Pi.zero_apply]

/--
@isnad1 id=iff.0h4v.s7.37c45bfb1535 from=translated src=- shape=9707bb8d vocab=c4992080
-/
theorem snoc_ne_zero_iff : snoc s y ≠ 0 ↔ s ≠ 0 ∨ y ≠ 0 := by
  refine ⟨fun h => ?_, fun h => h.casesOn snoc_ne_zero_of_left snoc_ne_zero_of_right⟩
  refine imp_iff_not_or.1 fun h' c => h ?_
  rw [h', c, Finsupp.snoc_zero_zero]

/--
@isnad1 id=ne.1h5v.s6.2daca4d961e8 from=translated src=- shape=a4cfb2ee vocab=d7d13a08
-/
theorem insertNth_ne_zero_of_left (h : y ≠ 0) : insertNth p y s ≠ 0 := by
  contrapose! h with c
  rw [← insertNth_apply_same p y s, c, Finsupp.coe_zero, Pi.zero_apply]

/--
@isnad1 id=ne.1h5v.s7.2ff11dac25b2 from=translated src=- shape=495c589d vocab=d7d13a08
-/
theorem insertNth_ne_zero_of_right (h : s ≠ 0) : insertNth p y s ≠ 0 := by
  contrapose! h with c
  ext a
  simp only [← insertNth_apply_succAbove p y s a, c, coe_zero, Pi.zero_apply]

/--
@isnad1 id=iff.0h5v.s7.8c4d8cbef861 from=translated src=- shape=9bc3eb7a vocab=d7d13a08
-/
theorem insertNth_ne_zero_iff : insertNth p y s ≠ 0 ↔ y ≠ 0 ∨ s ≠ 0 := by
  refine ⟨fun h => ?_,
    fun h => h.casesOn (insertNth_ne_zero_of_left p) (insertNth_ne_zero_of_right p)⟩
  refine imp_iff_not_or.1 fun h' c => h ?_
  rw [h', c, Finsupp.insertNth_zero_zero]

-- theorem cons_support : (s.cons y).support ⊆ insert 0 (s.support.map (Fin.succEmb n)) := by
--   intro i hi
--   suffices i = 0 ∨ ∃ a, ¬s a = 0 ∧ a.succ = i by simpa
--   apply (Fin.eq_zero_or_eq_succ i).imp id (Exists.imp _)
--   rintro i rfl
--   simpa [Finsupp.mem_support_iff] using hi

-- theorem cons_right_injective : Injective (Finsupp.cons y : (Fin n →₀ M) → Fin (n + 1) →₀ M) :=
--   equivFunOnFinite.symm.injective.comp ((Fin.cons_right_injective _).comp DFunLike.coe_injective)

/--
@isnad1 id=le.0h4v.s7.4be008bd2506 from=translated src=- shape=fb88023a vocab=10b20785
-/
theorem snoc_support :
    (s.snoc y).support ⊆ insert (Fin.last n) (s.support.map Fin.castSuccEmb) := by
  intro i hi
  suffices i = Fin.last n ∨ ∃ a, ¬s a = 0 ∧ a.castSucc = i by simpa
  apply (Fin.eq_castSucc_or_eq_last i).symm.imp id (Exists.imp _)
  rintro i rfl
  simpa [Finsupp.mem_support_iff] using hi

/--
@isnad1 id=injectiv.0h3v.s5.0576893ac8b4 from=translated src=- shape=cb79bfaf vocab=19eac790
-/
theorem snoc_left_injective : Injective (Finsupp.snoc · y : (Fin n →₀ M) → Fin (n + 1) →₀ M) :=
  equivFunOnFinite.symm.injective.comp
    ((Fin.snoc_left_injective (α := fun _ => M) y).comp DFunLike.coe_injective)

/--
@isnad1 id=le.0h5v.s7.dfe3c070a168 from=translated src=- shape=f7ac6680 vocab=645c941a
-/
theorem insertNth_support :
    (insertNth p y s).support ⊆ insert p (s.support.map (Fin.succAboveEmb p)) := by
  intro i hi
  suffices i = p ∨ ∃ a, ¬s a = 0 ∧ p.succAbove a = i by simpa
  apply (Fin.eq_self_or_eq_succAbove p i).imp id (Exists.imp _)
  rintro j rfl
  simpa [Finsupp.mem_support_iff] using hi

/--
@isnad1 id=injectiv.0h4v.s5.1ae627b2892d from=translated src=- shape=21b9d360 vocab=51b950d4
-/
theorem insertNth_right_injective :
    Injective (Finsupp.insertNth p y : (Fin n →₀ M) → Fin (n + 1) →₀ M) :=
  equivFunOnFinite.symm.injective.comp
    ((Fin.insertNth_right_injective _).comp DFunLike.coe_injective)

end Add

section BigOperators

variable {M N : Type*}

/--
@isnad1 id=eq.0h5v.s7.ebfe928d1f7a from=translated src=- shape=d882db2b vocab=aa68ca39
-/
lemma sum_insertNth [AddCommMonoid M] {n : ℕ} (σ : Fin n →₀ M) (i : M) (p : Fin (n + 1)) :
    (insertNth p i σ).sum (fun _ e ↦ e) = i + σ.sum (fun _ e ↦ e) := by
  rw [sum_fintype _ _ (fun _ => rfl), sum_fintype _ _ (fun _ => rfl)]
  apply Fin.sum_insertNth

/--
@isnad1 id=eq.1h7v.s7.d945b46b40d8 from=translated src=- shape=dc684111 vocab=71d08891
-/
lemma sum_insertNth' [AddCommMonoid M] [AddCommMonoid N] {n : ℕ} (σ : Fin n →₀ M) (i : M)
    (p : Fin (n + 1)) (f : Fin (n+1) → M → N) (h : ∀ x, f x 0 = 0) :
    sum (insertNth p i σ) f = f p i + sum σ (Fin.removeNth p f) := by
  rw [sum_fintype _ _ (fun _ => by apply h), sum_fintype _ _ (fun _ => by apply h)]
  simp_rw [Fin.sum_univ_succAbove _ p, insertNth_apply_same, insertNth_apply_succAbove]
  congr

end BigOperators

end Finsupp
