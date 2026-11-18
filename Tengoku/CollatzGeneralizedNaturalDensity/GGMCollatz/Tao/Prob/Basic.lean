import Tengoku.CollatzGeneralizedNaturalDensity.GGMCollatz.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# PMF computations: total variation, expectation, i.i.d. vectors (counterpart of node S1 of tao-collatz)

Derived from `TaoCollatz/Prob/Basic.lean` of gotrevor/tao-collatz (Apache-2.0), commit 15efca2;
generalized to the GGM family (p, q, r). The content of this file consists of general PMF lemmas that do not
depend on `p`, `q`, `r`, so the body is unchanged from the original file (namespace `PMF`); we added at the end
the agreement with `GGMCollatz.Family.expect` and `GGMCollatz.Family.dTV`
(the definitions in `GGMCollatz/Basic.lean`).

All probabilities are handled via `PMF` and `tsum` (no measure theory; tao-collatz's design choice D1):
the expectation is `∑' a, (p a).toReal * f a`, the total variation is `∑' a, |(p a).toReal - (q a).toReal|`.
-/

open scoped ENNReal

namespace PMF

variable {α : Type*}

/-- Change of variables for `∑' b, (p.bind f) b * g b` (ℝ≥0∞: no summability side
conditions; Fubini and scalar-pull are unconditional).
@isnad1 id=eq.0h5v.s7.84443714da6e from=translated src=- shape=d214099f vocab=4a23ec25
-/
theorem tsum_bind_mul {β : Type*} (p : PMF α) (f : α → PMF β) (g : β → ℝ≥0∞) :
    ∑' b, (p.bind f) b * g b = ∑' a, p a * ∑' b, f a b * g b := by
  simp only [PMF.bind_apply]
  calc ∑' b, (∑' a, p a * f a b) * g b
      = ∑' b, ∑' a, p a * f a b * g b :=
        tsum_congr fun b => ENNReal.tsum_mul_right.symm
    _ = ∑' a, ∑' b, p a * f a b * g b := ENNReal.tsum_comm
    _ = ∑' a, p a * ∑' b, f a b * g b := tsum_congr fun a => by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun b => mul_assoc _ _ _

/-- Pushforward change of variables: `∑' b, (p.map φ) b * g b = ∑' a, p a * g (φ a)`.
@isnad1 id=eq.0h5v.s6.1bf623991a18 from=translated src=- shape=93b462a0 vocab=c0ebcc5b
-/
theorem tsum_map_mul {β : Type*} (p : PMF α) (φ : α → β) (g : β → ℝ≥0∞) :
    ∑' b, (p.map φ) b * g b = ∑' a, p a * g (φ a) := by
  rw [PMF.map, tsum_bind_mul]
  refine tsum_congr fun a => ?_
  congr 1
  rw [tsum_eq_single (φ a) (fun b hb => by simp [PMF.pure_apply, hb])]
  simp [PMF.pure_apply]

/-- Total variation distance (D1 form): `∑' a, |p a − q a|` over reals.-/
noncomputable def dTV (p q : PMF α) : ℝ := ∑' a, |(p a).toReal - (q a).toReal|

/-- Expectation of a real observable `f` under `p` (D1 form).-/
noncomputable def expect (p : PMF α) (f : α → ℝ) : ℝ := ∑' a, (p a).toReal * f a

/-- Expectation of a complex observable `f` under `p` (for character sums).-/
noncomputable def cexpect (p : PMF α) (f : α → ℂ) : ℂ := ∑' a, ((p a).toReal : ℂ) * f a

/-- The `n`-fold iid product of `p`, as a `PMF (Fin n → α)`.-/
noncomputable def iid (p : PMF α) : (n : ℕ) → PMF (Fin n → α)
  | 0 => PMF.pure (fun i => i.elim0)
  | n + 1 => p.bind fun a => (iid p n).map (Fin.cons a)

/-- Peel one coordinate off an `iid` vector tsum: the head is a fresh `p`-draw, the
tail restarts as `iid n` under `Fin.cons`.
@isnad1 id=eq.0h4v.s8.05b488a8a29a from=translated src=- shape=a56bd48d vocab=a5733c08
-/
theorem tsum_iid_succ_mul (p : PMF α) (n : ℕ) (h : (Fin (n + 1) → α) → ℝ≥0∞) :
    ∑' v : Fin (n + 1) → α, (p.iid (n + 1)) v * h v
      = ∑' a, p a * ∑' w : Fin n → α, (p.iid n) w * h (Fin.cons a w) := by
  rw [show p.iid (n + 1) = p.bind fun a => (p.iid n).map (Fin.cons a) from rfl,
    tsum_bind_mul]
  exact tsum_congr fun a => by rw [tsum_map_mul]

/-- The `iid 0` tsum collapses: the empty vector has full mass.
@isnad1 id=eq.0h3v.s6.2d4b07f5fa1d from=translated src=- shape=5d8069dc vocab=bdc4421e
-/
theorem tsum_iid_zero_mul (p : PMF α) (h : (Fin 0 → α) → ℝ≥0∞) :
    ∑' v : Fin 0 → α, (p.iid 0) v * h v = h (fun i => i.elim0) := by
  rw [tsum_eq_single (fun i => i.elim0)
    (fun v hv => absurd (funext fun i => i.elim0) hv)]
  rw [show p.iid 0 = PMF.pure (fun i => i.elim0) from rfl]
  simp [PMF.pure_apply]

/-- `toReal` bridge for a PMF-weighted `ofReal` tsum (no side conditions beyond
pointwise nonnegativity: every term is finite).
@isnad1 id=eq.1h3v.s6.874cb9e7a60c from=translated src=- shape=b4e2f3a0 vocab=e79f9cdf
-/
theorem toReal_tsum_mul_ofReal (p : PMF α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑' x, p x * ENNReal.ofReal (f x)).toReal = ∑' x, (p x).toReal * f x := by
  rw [ENNReal.tsum_toReal_eq
    (fun x => ENNReal.mul_ne_top (p.apply_ne_top x) ENNReal.ofReal_ne_top)]
  exact tsum_congr fun x => by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf x)]

/-- PMF-weighted `ofReal` sums of `≤ 1` observables are `≤ 1`.
@isnad1 id=le.1h3v.s6.ed58232d687e from=translated src=- shape=8569afdc vocab=f5b8e758
-/
theorem tsum_mul_ofReal_le_one (p : PMF α) (f : α → ℝ) (hf : ∀ x, f x ≤ 1) :
    ∑' x, p x * ENNReal.ofReal (f x) ≤ 1 := by
  calc ∑' x, p x * ENNReal.ofReal (f x)
      ≤ ∑' x, p x * 1 :=
        ENNReal.tsum_le_tsum fun x =>
          mul_le_mul_right (ENNReal.ofReal_le_one.mpr (hf x)) _
    _ = 1 := by rw [tsum_congr fun x => mul_one (p x), p.tsum_coe]

/-- The empty iid vector carries full mass: expectations collapse.
@isnad1 id=eq.0h3v.s5.0ead7559463d from=translated src=- shape=46514219 vocab=11257f86
-/
theorem expect_iid_zero (p : PMF α) (h : (Fin 0 → α) → ℝ) :
    (p.iid 0).expect h = h (fun i => i.elim0) := by
  show ∑' v : Fin 0 → α, ((p.iid 0) v).toReal * h v = _
  rw [tsum_eq_single (fun i : Fin 0 => i.elim0)
    (fun v hv => absurd (funext fun i => i.elim0) hv)]
  rw [show p.iid 0 = PMF.pure (fun i => i.elim0) from rfl]
  simp [PMF.pure_apply]

/-- Peel one coordinate off an iid expectation of a `[0,1]`-valued observable.
@isnad1 id=eq.2h4v.s7.f0f2e12232da from=translated src=- shape=69841c1a vocab=e338a32a
-/
theorem expect_iid_succ (p : PMF α) (n : ℕ) (h : (Fin (n + 1) → α) → ℝ)
    (h0 : ∀ v, 0 ≤ h v) (h1 : ∀ v, h v ≤ 1) :
    (p.iid (n + 1)).expect h
      = ∑' a : α, (p a).toReal * (p.iid n).expect fun w => h (Fin.cons a w) := by
  show ∑' v : Fin (n + 1) → α, ((p.iid (n + 1)) v).toReal * h v = _
  rw [← toReal_tsum_mul_ofReal (p.iid (n + 1)) h h0,
    tsum_iid_succ_mul p n (fun v => ENNReal.ofReal (h v)),
    ENNReal.tsum_toReal_eq (fun a => ENNReal.mul_ne_top (p.apply_ne_top a)
      (ne_top_of_le_ne_top (by simp)
        (tsum_mul_ofReal_le_one (p.iid n) _ (fun w => h1 _))))]
  refine tsum_congr fun a => ?_
  rw [ENNReal.toReal_mul, toReal_tsum_mul_ofReal (p.iid n) _ (fun w => h0 _)]
  rfl

/-- Pushforward can only merge mass: `p a ≤ (p.map f) (f a)`. With `f = mod-N
reduction` this is the free truncation step of the finite circle method.
@isnad1 id=le.0h5v.s5.6f31a644c5d0 from=translated src=- shape=ad05c459 vocab=aee74a9b
-/
theorem apply_le_map_apply {β : Type*} (p : PMF α) (f : α → β) (a : α) :
    p a ≤ (p.map f) (f a) := by
  classical
  rw [PMF.map_apply]
  calc p a = if f a = f a then p a else 0 := by rw [ite_eq_left rfl]
    _ ≤ ∑' a', if f a = f a' then p a' else 0 := ENNReal.le_tsum a

/-- Every coordinate of a vector in the support of `p.iid n` lies in `p.support`.
@isnad1 id=mem.1h5v.s5.ac4c9d58b4e5 from=translated src=- shape=e1015c97 vocab=c6a68de3
-/
theorem iid_support_coord (p : PMF α) :
    ∀ (n : ℕ) (v : Fin n → α), v ∈ (p.iid n).support → ∀ i, v i ∈ p.support := by
  intro n
  induction n with
  | zero => intro v _ i; exact i.elim0
  | succ n IH =>
    intro v hv i
    rw [show p.iid (n + 1) = p.bind fun a => (p.iid n).map (Fin.cons a) from rfl,
      PMF.mem_support_bind_iff] at hv
    obtain ⟨a, ha, hv⟩ := hv
    rw [PMF.mem_support_map_iff] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using ha
    · simpa using IH w hw j

/-- Total variation is symmetric.
@isnad1 id=eq.0h3v.s4.844dc42b5a49 from=translated src=- shape=3cad1d62 vocab=51cef362
-/
theorem dTV_comm (p q : PMF α) : dTV p q = dTV q p := by
  unfold dTV
  exact tsum_congr fun _ => abs_sub_comm _ _

/-- Total variation is nonnegative.
@isnad1 id=le.0h3v.s4.561a7e4ab1ef from=translated src=- shape=71919d61 vocab=e2e12ba5
-/
theorem dTV_nonneg (p q : PMF α) : 0 ≤ dTV p q :=
  tsum_nonneg fun _ => abs_nonneg _

/-- Paper (1.10), indicator/expectation form: the difference of event probabilities
under `p` and `q` is controlled by their total variation.
@isnad1 id=le.0h4v.s6.28747535d5b8 from=translated src=- shape=06dadadc vocab=5707a0ba
-/
theorem abs_expect_indicator_sub_le_dTV (p q : PMF α) (E : Set α) :
    |p.expect (Set.indicator E 1) - q.expect (Set.indicator E 1)| ≤ p.dTV q := by
  have hp : Summable fun a => (p a).toReal :=
    ENNReal.summable_toReal (by rw [p.tsum_coe]; exact ENNReal.one_ne_top)
  have hq : Summable fun a => (q a).toReal :=
    ENNReal.summable_toReal (by rw [q.tsum_coe]; exact ENNReal.one_ne_top)
  have hnn : ∀ (r : PMF α) (a : α), 0 ≤ (r a).toReal * Set.indicator E 1 a := fun r a =>
    mul_nonneg ENNReal.toReal_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) a)
  have hle : ∀ (r : PMF α) (a : α), (r a).toReal * Set.indicator E 1 a ≤ (r a).toReal := by
    intro r a
    by_cases h : a ∈ E
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h, ENNReal.toReal_nonneg]
  have hpE : Summable fun a => (p a).toReal * Set.indicator E 1 a :=
    Summable.of_nonneg_of_le (hnn p) (hle p) hp
  have hqE : Summable fun a => (q a).toReal * Set.indicator E 1 a :=
    Summable.of_nonneg_of_le (hnn q) (hle q) hq
  have hkey : ∀ a,
      |(p a).toReal * Set.indicator E 1 a - (q a).toReal * Set.indicator E 1 a|
        ≤ |(p a).toReal - (q a).toReal| := by
    intro a
    rw [← sub_mul, abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    by_cases h : a ∈ E
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  unfold expect dTV
  rw [← hpE.tsum_sub hqE]
  calc |∑' a, ((p a).toReal * Set.indicator E 1 a - (q a).toReal * Set.indicator E 1 a)|
      ≤ ∑' a, |(p a).toReal * Set.indicator E 1 a - (q a).toReal * Set.indicator E 1 a| := by
        have h := norm_tsum_le_tsum_norm
          (f := fun a => (p a).toReal * Set.indicator E 1 a
            - (q a).toReal * Set.indicator E 1 a)
          (by simpa only [Real.norm_eq_abs] using (hpE.sub hqE).abs)
        simpa only [Real.norm_eq_abs] using h
    _ ≤ ∑' a, |(p a).toReal - (q a).toReal| :=
        ((hpE.sub hqE).abs).tsum_le_tsum hkey ((hp.sub hq).abs)

/-- The pointwise mass of an iid vector factorizes as the product of coordinate masses.
@isnad1 id=eq.0h4v.s6.9f2d3b932058 from=translated src=- shape=4ff8ce95 vocab=b0c0127b
-/
theorem iid_apply_eq_prod (p : PMF α) (n : Nat) (v : Fin n → α) :
    p.iid n v = ∏ i, p (v i) := by
  classical
  induction n with
  | zero =>
      have hv : v = fun i : Fin 0 => i.elim0 := by
        funext i
        exact i.elim0
      subst v
      rw [show p.iid 0 = PMF.pure (fun i : Fin 0 => i.elim0) from rfl]
      simp [PMF.pure_apply]
  | succ n ih =>
      rw [show p.iid (n + 1) = p.bind fun a => (p.iid n).map (Fin.cons a) from rfl,
        PMF.bind_apply]
      rw [tsum_eq_single (v 0)]
      · rw [PMF.map_apply]
        rw [tsum_eq_single (Fin.tail v)]
        · rw [ite_eq_left (Fin.cons_self_tail v).symm, ih, Fin.prod_univ_succ]
          congr 1
        · intro w hw
          rw [ite_eq_right]
          intro heq
          apply hw
          funext j
          exact (congrFun heq j.succ).symm
      · intro a ha
        rw [PMF.map_apply]
        rw [mul_eq_zero]
        right
        apply ENNReal.tsum_eq_zero.mpr
        intro w
        rw [ite_eq_right]
        intro heq
        apply ha
        exact (congrFun heq 0).symm

/-- Real-summability of any `‖·‖ ≤ 1` observable weighted by an iid mass (comparison with the
total mass `∑ = 1`). Backbone for the block-independence factorization.
@isnad1 id=summable.1h4v.s6.cee32fa391ad from=translated src=- shape=5b30da98 vocab=6c267103
-/
theorem summable_iid_norm_le_one (p : PMF α) (k : ℕ) (h : (Fin k → α) → ℂ) (hh : ∀ v, ‖h v‖ ≤ 1) :
    Summable (fun v => ‖((p.iid k) v).toReal * h v‖) := by
  have hbase : Summable (fun v : Fin k → α => ((p.iid k) v).toReal) :=
    ENNReal.summable_toReal (by rw [(p.iid k).tsum_coe]; exact ENNReal.one_ne_top)
  refine Summable.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_) hbase
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  calc ((p.iid k) v).toReal * ‖h v‖ ≤ ((p.iid k) v).toReal * 1 :=
        mul_le_mul_of_nonneg_left (hh v) ENNReal.toReal_nonneg
    _ = ((p.iid k) v).toReal := mul_one _

/-- **iid block-independence** (D1 product form): the complex expectation of a product of a
head-observable `f` (first `j` coords) and a tail-observable `g` (last `q` coords) over `iid (j+q)`
factors as the product of the two block expectations. Bounded observables (`‖·‖ ≤ 1`, as for
character/indicator products) supply the summability. This is the reusable engine behind §6's
conditional character-sum factorization: with `g` carrying a `1_{pre(tail)=l}` indicator, the head
and tail blocks separate.
@isnad1 id=eq.2h6v.s7.d7985e5aa060 from=translated src=- shape=340cd9eb vocab=f23ea342
-/
theorem cexpect_iid_append (p : PMF α) (j q : ℕ)
    (f : (Fin j → α) → ℂ) (g : (Fin q → α) → ℂ)
    (hf : ∀ v, ‖f v‖ ≤ 1) (hg : ∀ v, ‖g v‖ ≤ 1) :
    (p.iid (j + q)).cexpect
        (fun v => f (fun i => v (Fin.castAdd q i)) * g (fun i => v (Fin.natAdd j i)))
      = (p.iid j).cexpect f * (p.iid q).cexpect g := by
  rw [cexpect, cexpect, cexpect,
    tsum_mul_tsum_of_summable_norm (summable_iid_norm_le_one p j f hf)
      (summable_iid_norm_le_one p q g hg),
    ← Equiv.tsum_eq (Fin.appendEquiv j q)
      (fun v => ((p.iid (j + q)) v).toReal * (f (fun i => v (Fin.castAdd q i))
        * g (fun i => v (Fin.natAdd j i))))]
  refine tsum_congr (fun z => ?_)
  obtain ⟨vh, vt⟩ := z
  have happ : (Fin.appendEquiv j q) (vh, vt) = Fin.append vh vt := rfl
  rw [happ]
  have hhead : (fun i => Fin.append vh vt (Fin.castAdd q i)) = vh := by
    funext i; exact Fin.append_left vh vt i
  have htail : (fun i => Fin.append vh vt (Fin.natAdd j i)) = vt := by
    funext i; exact Fin.append_right vh vt i
  have hmass : (p.iid (j + q)) (Fin.append vh vt) = (p.iid j) vh * (p.iid q) vt := by
    rw [iid_apply_eq_prod, Fin.prod_univ_add, iid_apply_eq_prod p j vh, iid_apply_eq_prod p q vt]
    congr 1
    · exact Finset.prod_congr rfl (fun i _ => by rw [Fin.append_left])
    · exact Finset.prod_congr rfl (fun i _ => by rw [Fin.append_right])
  rw [hhead, htail, hmass, ENNReal.toReal_mul]
  push_cast
  ring

end PMF

namespace GGMCollatz

namespace Family

/-- `Family.expect` (`GGMCollatz/Basic.lean`) has the same definition as `PMF.expect`.
@isnad1 id=eq.0h3v.s4.842f1fff0c61 from=translated src=- shape=9d7b64aa vocab=203963e4
-/
theorem expect_eq_pmf_expect {α : Type*} (μ : PMF α) (f : α → ℝ) :
    expect μ f = μ.expect f := rfl

/-- `Family.dTV` (`GGMCollatz/Basic.lean`) has the same definition as `PMF.dTV`.
@isnad1 id=eq.0h3v.s4.830d660837af from=translated src=- shape=edc67bda vocab=94ab5d82
-/
theorem dTV_eq_pmf_dTV {α : Type*} (μ ν : PMF α) : dTV μ ν = μ.dTV ν := rfl

/-- Total variation is symmetric (the `Family.dTV` form).
@isnad1 id=eq.0h3v.s4.d36fefd618d2 from=translated src=- shape=3cad1d62 vocab=828f8880
-/
theorem dTV_comm {α : Type*} (μ ν : PMF α) : dTV μ ν = dTV ν μ := PMF.dTV_comm μ ν

/-- Total variation is nonnegative (the `Family.dTV` form).
@isnad1 id=le.0h3v.s4.17d6a6954342 from=translated src=- shape=71919d61 vocab=63a40e8c
-/
theorem dTV_nonneg {α : Type*} (μ ν : PMF α) : 0 ≤ dTV μ ν := PMF.dTV_nonneg μ ν

/-- The difference of the probabilities of an event is bounded by the total variation (the `Family.expect`, `Family.dTV` form; (1.10) of tao-collatz).
@isnad1 id=le.0h4v.s6.f7c756ca6921 from=translated src=- shape=06dadadc vocab=f4966b1d
-/
theorem abs_expect_indicator_sub_le_dTV {α : Type*} (μ ν : PMF α) (E : Set α) :
    |expect μ (Set.indicator E 1) - expect ν (Set.indicator E 1)| ≤ dTV μ ν :=
  PMF.abs_expect_indicator_sub_le_dTV μ ν E

end Family

end GGMCollatz
