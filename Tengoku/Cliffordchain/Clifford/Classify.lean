import Tengoku.Cliffordchain.Clifford.Counter6

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exactly which levels of the Clifford chain predicate hold

`cliffordChain_iff : CliffordChain n ↔ n ≤ 5`.

* `n ≤ 3`: direct (three points always lie on a generalized circle);
  `n = 4, 5`: `cliffordChain_four`, `cliffordChain_five`.
* `n ≥ 6`: the counterexample `Counter6.cx` propagates upwards. A level-`(m + 1)` object
  (`m + 1 ≥ 7`) needs a level-`m` object of the subfamily omitting the last circle
  (`not_chain_of_extends`), and any family in general position extends by one circle in general
  position (`GenPosN.exists_snoc`): the new centre is taken on the parabola `t + t² i`, which meets
  each bad line / circle in finitely many points.
-/

namespace Clifford

open Complex ComplexConjugate Polynomial EuclideanGeometry

/-! ### Low levels -/

theorem cliffordChain_zero : CliffordChain 0 := fun _ _ => ⟨{0}, rfl⟩
theorem cliffordChain_one : CliffordChain 1 := fun _ _ => ⟨_, rfl⟩
theorem cliffordChain_two : CliffordChain 2 := fun _ _ => ⟨_, rfl⟩

/-- Three points of `ℂ` lie on a generalized circle.-/
theorem cospherical_or_collinear (a b c : ℂ) :
    Cospherical ({a, b, c} : Set ℂ) ∨ Collinear ℝ ({a, b, c} : Set ℂ) := by
  by_cases h : Collinear ℝ ({a, b, c} : Set ℂ)
  · exact Or.inr h
  · left
    have hi : AffineIndependent ℝ ![a, b, c] := by
      rw [affineIndependent_iff_not_collinear_set]; exact h
    let t : Affine.Triangle ℝ ℂ := ⟨![a, b, c], hi⟩
    refine ⟨t.circumcenter, t.circumradius, fun p hp => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · rw [dist_comm]; exact t.dist_circumcenter_eq_circumradius' 0
    · rw [dist_comm]; exact t.dist_circumcenter_eq_circumradius' 1
    · rw [dist_comm]; exact t.dist_circumcenter_eq_circumradius' 2

theorem cliffordChain_three : CliffordChain 3 := by
  intro c _
  obtain ⟨X, hX, hs⟩ := exists_gcircle
    (cospherical_or_collinear (second (c 1) (c 2)) (second (c 0) (c 2)) (second (c 0) (c 1)))
  refine ⟨X, hX, fun i => ?_⟩
  fin_cases i
  · exact ⟨second (c 1) (c 2), rfl, hs (Set.mem_insert _ _)⟩
  · exact ⟨second (c 0) (c 2), rfl, hs (Set.mem_insert_of_mem _ (Set.mem_insert _ _))⟩
  · exact ⟨second (c 0) (c 1), rfl,
      hs (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))⟩

/-! ### Propagation of the counterexample -/

/-- A family whose first six centres are `Counter6.cx` has no Clifford object of level `≥ 6`.-/
theorem not_chain_of_extends : ∀ (m : ℕ) (c : Fin (m + 6) → ℂ),
    (∀ k : Fin 6, c (Fin.castLE (by omega) k) = Counter6.cx k) → ∀ X, ¬ Chain (m + 6) c X
  | 0, c, hc, X => by
    have : c = Counter6.cx := funext fun k => hc k
    subst this; exact Counter6.not_chain6
  | m + 1, c, hc, X => by
    intro h
    have hc' : ∀ k : Fin 6, (c ∘ (Fin.last (m + 6)).succAbove) (Fin.castLE (by omega) k) =
        Counter6.cx k := fun k => by
      rw [Fin.succAbove_last, Function.comp_apply, ← hc k]; rfl
    have h' : Chain (m + 4 + 3) c X := h
    rw [Chain] at h'
    split_ifs at h'
    · obtain ⟨p, hp, -⟩ := h'.2 (Fin.last _)
      exact not_chain_of_extends m _ hc' _ hp
    · obtain ⟨p, -, h'⟩ := h'
      obtain ⟨Y, hY, -⟩ := h' (Fin.last _)
      exact not_chain_of_extends m _ hc' _ hY

/-! ### Extending a family in general position -/

/-- The parabola `t + t² i`.-/
noncomputable def par (t : ℝ) : ℂ := t + I * (t : ℂ) ^ 2

theorem conj_par (t : ℝ) : conj (par t) = t - I * (t : ℂ) ^ 2 := by
  simp [par, map_add, map_mul, conj_ofReal, conj_I]; ring

/-- `par` as a polynomial, and its conjugate.-/
noncomputable def pZ : ℂ[X] := X + C I * X ^ 2
noncomputable def pZb : ℂ[X] := X - C I * X ^ 2

theorem eval_pZ (t : ℝ) : (pZ.eval (t : ℂ)) = par t := by simp [pZ, par]
theorem eval_pZb (t : ℝ) : (pZb.eval (t : ℂ)) = conj (par t) := by
  rw [conj_par]; simp [pZb]

theorem finite_roots {p : ℂ[X]} (hp : p ≠ 0) : {t : ℝ | p.eval (t : ℂ) = 0}.Finite :=
  (Polynomial.finite_setOfPred_isRoot hp).preimage (Complex.ofReal_injective.injOn)

noncomputable def pA (a : ℂ) : ℂ[X] := C (conj a) * pZ - C a * pZb

theorem eval_pA (a : ℂ) (t : ℝ) : (pA a).eval (t : ℂ) = conj a * par t - a * conj (par t) := by
  simp only [pA, eval_sub, eval_mul, eval_C, eval_pZ, eval_pZb]

theorem pA_ne_zero {a : ℂ} (ha : a ≠ 0) : pA a ≠ 0 := by
  intro h
  have h1 := eval_pA a 1; have h2 := eval_pA a (-1)
  rw [h, eval_zero] at h1 h2
  apply ha
  have e1 := congrArg Complex.re h1; have e2 := congrArg Complex.im h1
  have e3 := congrArg Complex.re h2; have e4 := congrArg Complex.im h2
  simp [par] at e1 e2 e3 e4
  apply Complex.ext <;> simp <;> nlinarith

noncomputable def pT (a b : ℂ) : ℂ[X] := triP (C a) (C b) pZ (C (conj a)) (C (conj b)) pZb

theorem eval_pT (a b : ℂ) (t : ℝ) :
    (pT a b).eval (t : ℂ) = triP a b (par t) (conj a) (conj b) (conj (par t)) := by
  rw [conj_par]; simp [pT, pZ, pZb, par, triP, det3]

theorem pT_ne_zero {a b : ℂ} (h : Transversal a b) : pT a b ≠ 0 := by
  intro h0
  have h1 := eval_pT a b 0
  rw [h0, eval_zero] at h1
  apply h
  simp [par, triP, det3] at h1
  linear_combination h1

noncomputable def pC (a b : ℂ) : ℂ[X] := cycP (C a) (C b) pZ (C (conj a)) (C (conj b)) pZb

theorem eval_pC (a b : ℂ) (t : ℝ) :
    (pC a b).eval (t : ℂ) = cycP a b (par t) (conj a) (conj b) (conj (par t)) := by
  rw [conj_par]; simp [pC, pZ, pZb, par, cycP, det3]

theorem pC_ne_zero {a b : ℂ} (h : Transversal a b) : pC a b ≠ 0 := by
  intro h0
  have e : ∀ t : ℝ, cycP a b (t + I * (t : ℂ) ^ 2) (conj a) (conj b) (t - I * (t : ℂ) ^ 2) = 0 :=
    fun t => by rw [← conj_par]; exact (eval_pC a b t).symm.trans (by rw [h0, eval_zero])
  have e0 := e 0; have e1 := e 1; have e2 := e (-1); have e3 := e 2; have e4 := e (-2)
  simp only [cycP, det3] at e0 e1 e2 e3 e4
  push_cast at e0 e1 e2 e3 e4
  apply h
  linear_combination (-1 / 4 : ℂ) * e1 + (-1 / 12 : ℂ) * e2 + (1 / 12 : ℂ) * e3 +
    (conj a * b - a * conj b) * I_sq

theorem finite_bad {n : ℕ} (c : Fin n → ℂ) (hc : ∀ i, c i ≠ 0)
    (h : ∀ i j, i ≠ j → Transversal (c i) (c j)) :
    {t : ℝ | (∃ i, ¬ Transversal (c i) (par t)) ∨
      ∃ i j, i < j ∧ ¬ GenTriple (c i) (c j) (par t)}.Finite := by
  have hA : ∀ i, {t : ℝ | ¬ Transversal (c i) (par t)}.Finite := fun i => by
    refine (finite_roots (pA_ne_zero (hc i))).subset fun t ht => ?_
    simp only [Set.mem_ofPred_eq, Transversal, not_not] at ht ⊢
    rw [eval_pA, ht, sub_self]
  have hT : ∀ i j, i < j → {t : ℝ | ¬ GenTriple (c i) (c j) (par t)}.Finite := fun i j hij => by
    refine ((finite_roots (pT_ne_zero (h i j hij.ne))).union
      (finite_roots (pC_ne_zero (h i j hij.ne)))).subset fun t ht => ?_
    simp only [Set.mem_ofPred_eq, GenTriple, not_and_or, not_not] at ht
    rcases ht with ht | ht
    · left; simp only [Set.mem_ofPred_eq]; rw [eval_pT]; exact ht
    · right; simp only [Set.mem_ofPred_eq]; rw [eval_pC]; exact ht
  have e : {t : ℝ | (∃ i, ¬ Transversal (c i) (par t)) ∨
      ∃ i j, i < j ∧ ¬ GenTriple (c i) (c j) (par t)} =
      (⋃ i, {t : ℝ | ¬ Transversal (c i) (par t)}) ∪
        ⋃ i, ⋃ j, ⋃ (_ : i < j), {t : ℝ | ¬ GenTriple (c i) (c j) (par t)} := by
    ext t; simp
  rw [e]
  exact (Set.finite_iUnion hA).union
    (Set.finite_iUnion fun i => Set.finite_iUnion fun j => Set.finite_iUnion fun hij => hT i j hij)

/-- A family of at least two circles in general position extends by one circle in general
position.-/
theorem GenPosN.exists_snoc {n : ℕ} (hn : 2 ≤ n) {c : Fin n → ℂ} (h : GenPosN c) :
    ∃ x, GenPosN (Fin.snoc c x : Fin (n + 1) → ℂ) := by
  have hc : ∀ i, c i ≠ 0 := fun i => by
    obtain ⟨j, hj⟩ : ∃ j, j ≠ i := by
      by_cases hi : (i : ℕ) = 0
      · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at hi; simp at hi⟩
      · exact ⟨⟨0, by omega⟩, fun e => by rw [← e] at hi; simp at hi⟩
    exact (h.1 i j hj.symm).left_ne_zero
  obtain ⟨t, ht⟩ := (finite_bad c hc h.1).exists_notMem
  simp only [Set.mem_ofPred_eq, not_or, not_exists, not_and, not_not] at ht
  obtain ⟨h1, h2⟩ := ht
  refine ⟨par t, fun i j hij => ?_, fun i j k hij hjk => ?_⟩
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd rfl hij
      | cast j => simp only [Fin.snoc_last, Fin.snoc_castSucc]; exact cd_symm (h1 j)
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp only [Fin.snoc_last, Fin.snoc_castSucc]; exact h1 i
      | cast j =>
        simp only [Fin.snoc_castSucc]
        exact h.1 i j fun e => hij (by rw [e])
  · induction k using Fin.lastCases with
    | last =>
      have hi : i ≠ Fin.last n := (hij.trans hjk).ne
      have hj : j ≠ Fin.last n := hjk.ne
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hi
      obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hj
      simp only [Fin.snoc_last, Fin.snoc_castSucc]
      exact h2 i j (Fin.castSucc_lt_castSucc_iff.1 hij)
    | cast k =>
      have hj : j ≠ Fin.last n := (hjk.trans (Fin.castSucc_lt_last k)).ne
      have hi : i ≠ Fin.last n := (hij.trans (hjk.trans (Fin.castSucc_lt_last k))).ne
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hi
      obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hj
      simp only [Fin.snoc_castSucc]
      exact h.2 i j k (Fin.castSucc_lt_castSucc_iff.1 hij) (Fin.castSucc_lt_castSucc_iff.1 hjk)

/-- Families in general position of every size `m + 6` starting with `Counter6.cx`.-/
theorem exists_extension : ∀ m : ℕ, ∃ c : Fin (m + 6) → ℂ, GenPosN c ∧
    ∀ k : Fin 6, c (Fin.castLE (by omega) k) = Counter6.cx k
  | 0 => ⟨Counter6.cx, Counter6.cx_genPosN, fun _ => rfl⟩
  | m + 1 => by
    obtain ⟨c, hc, he⟩ := exists_extension m
    obtain ⟨x, hx⟩ := hc.exists_snoc (by omega)
    refine ⟨Fin.snoc c x, hx, fun k => ?_⟩
    have : (Fin.castLE (by omega) k : Fin (m + 1 + 6)) =
        (Fin.castLE (by omega) k : Fin (m + 6)).castSucc := Fin.ext rfl
    rw [this, Fin.snoc_castSucc, he k]

/-- `CliffordChain n` fails for every `n ≥ 6`.-/
theorem not_cliffordChain_of_six_le {n : ℕ} (hn : 6 ≤ n) : ¬ CliffordChain n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  intro H
  obtain ⟨c, hc, he⟩ := exists_extension m
  obtain ⟨X, hX⟩ := H c hc
  exact not_chain_of_extends m c he X hX

/-- **Classification**: the Clifford chain predicate `CliffordChain n` holds exactly for `n ≤ 5`.-/
theorem cliffordChain_iff (n : ℕ) : CliffordChain n ↔ n ≤ 5 := by
  constructor
  · intro H; by_contra hn; exact not_cliffordChain_of_six_le (by omega) H
  · intro hn
    interval_cases n
    · exact cliffordChain_zero
    · exact cliffordChain_one
    · exact cliffordChain_two
    · exact cliffordChain_three
    · exact cliffordChain_four
    · exact cliffordChain_five

end Clifford
