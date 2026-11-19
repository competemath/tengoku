import Tengoku.Seed.Analysis.SpecialFunctions.Integrals.Basic
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.SymmetricPoly

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory intervalIntegral
open scoped BigOperators

namespace OddCycleBound.DenseRegion

/--
@isnad1 id=eq.0h2v.s7.cae2269afe07 from=translated src=- shape=65161285 vocab=8daa55f5
-/
lemma beta_nat : ∀ (i k : ℕ),
    (∫ t in (0:ℝ)..1, t ^ i * (1 - t) ^ k)
      = (Nat.factorial i * Nat.factorial k : ℝ) / (Nat.factorial (i + k + 1))
  | i, 0 => by
      simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, Nat.add_zero]
      rw [integral_pow, one_pow, zero_pow (by omega : i + 1 ≠ 0), sub_zero]
      have hfac : (Nat.factorial (i + 1) : ℝ) = (i + 1 : ℝ) * (Nat.factorial i : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hne : (Nat.factorial i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
      have hi1 : (i + 1 : ℝ) ≠ 0 := by positivity
      rw [hfac]
      field_simp
  | i, (k + 1) => by
      have hi1 : (i + 1 : ℝ) ≠ 0 := by positivity

      have hu : ∀ x ∈ Set.uIcc (0:ℝ) 1,
          HasDerivAt (fun t => (1 - t) ^ (k + 1)) (-((k + 1 : ℝ) * (1 - x) ^ k)) x := by
        intro x _
        have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := (hasDerivAt_id x).const_sub 1
        have h2 := h1.pow (k + 1)
        simp only [Nat.add_sub_cancel] at h2
        have heq : (↑(k + 1) : ℝ) * (1 - x) ^ k * (-1) = -((k + 1 : ℝ) * (1 - x) ^ k) := by
          push_cast; ring
        rwa [heq] at h2
      have hv : ∀ x ∈ Set.uIcc (0:ℝ) 1,
          HasDerivAt (fun t => t ^ (i + 1) / (i + 1 : ℝ)) (x ^ i) x := by
        intro x _
        have h2 := (hasDerivAt_pow (i + 1) x).div_const (i + 1 : ℝ)
        simp only [Nat.add_sub_cancel] at h2
        have heq : (↑(i + 1) : ℝ) * x ^ i / (i + 1 : ℝ) = x ^ i := by
          push_cast; field_simp
        rwa [heq] at h2
      have hu' : IntervalIntegrable (fun x => -((k + 1 : ℝ) * (1 - x) ^ k)) volume 0 1 :=
        Continuous.intervalIntegrable (by fun_prop) _ _
      have hv' : IntervalIntegrable (fun x : ℝ => x ^ i) volume 0 1 :=
        Continuous.intervalIntegrable (by fun_prop) _ _
      have IBP := integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
      simp only [sub_self, one_pow, sub_zero] at IBP
      have hLHS : (∫ t in (0:ℝ)..1, t ^ i * (1 - t) ^ (k + 1))
          = ∫ t in (0:ℝ)..1, (1 - t) ^ (k + 1) * t ^ i := by
        apply integral_congr; intro x _; ring
      have hRHS : (∫ x in (0:ℝ)..1, -((k + 1 : ℝ) * (1 - x) ^ k) * (x ^ (i + 1) / (i + 1)))
          = -(((k + 1 : ℝ) / (i + 1)) * ∫ t in (0:ℝ)..1, t ^ (i + 1) * (1 - t) ^ k) := by
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
        apply integral_congr; intro x _; ring
      rw [hLHS, IBP, hRHS, beta_nat (i + 1) k]
      rw [show (i + 1) + k + 1 = i + (k + 1) + 1 from by omega]
      have e1 : (Nat.factorial (i + 1) : ℝ) = (i + 1 : ℝ) * (Nat.factorial i : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have e2 : (Nat.factorial (k + 1) : ℝ) = (k + 1 : ℝ) * (Nat.factorial k : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      rw [e1, e2]
      field_simp
      ring

noncomputable def dirExp : List ℝ → (ℝ → ℝ) → ℝ
  | [], _ => 0
  | [a], f => f a
  | (a :: b :: L), f =>
      ∫ t in (0:ℝ)..1,
        ((b :: L).length : ℝ) * (1 - t) ^ ((b :: L).length - 1)
          * dirExp (b :: L) (fun x => f (t * a + (1 - t) * x))

/--
@isnad1 id=le.3h4v.s6.bbdfb12bad6f from=translated src=- shape=ce85338a vocab=5ce56b72
-/
lemma dirExp_nonneg : ∀ (L : List ℝ) (f : ℝ → ℝ) (a b : ℝ), a ≤ b →
    (∀ x ∈ Set.Icc a b, 0 ≤ f x) → (∀ x ∈ L, x ∈ Set.Icc a b) → 0 ≤ dirExp L f
  | [], f, a, b, _, _, _ => by simp [dirExp]
  | [c], f, a, b, _, hf, hL => by
      rw [dirExp]; exact hf c (hL c (by simp))
  | (c :: d :: L), f, a, b, hab, hf, hL => by
      rw [dirExp]
      apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
      intro t ht
      have h0t : (0:ℝ) ≤ t := ht.1
      have ht1 : t ≤ 1 := ht.2
      have hc : c ∈ Set.Icc a b := hL c (by simp)
      apply mul_nonneg
      · exact mul_nonneg (by positivity) (pow_nonneg (by linarith) _)
      · refine dirExp_nonneg (d :: L) _ a b hab ?_
          (fun x hx => hL x (List.mem_cons_of_mem c hx))
        intro x hx
        exact hf _ ⟨by nlinarith [hc.1, hx.1], by nlinarith [hc.2, hx.2]⟩

/--
@isnad1 id=continuo.1h3v.s5.e9a7a1180f58 from=translated src=- shape=397c9cde vocab=c2a71886
-/
lemma dirExp_param_continuous : ∀ (L : List ℝ) {X : Type} [TopologicalSpace X] (F : X → ℝ → ℝ),
    Continuous (Function.uncurry F) → Continuous (fun w => dirExp L (fun x => F w x))
  | [], _, _, _, _ => by simp only [dirExp]; exact continuous_const
  | [c], X, _, F, hF => by
      simp only [dirExp]
      exact hF.comp (show Continuous (fun w : X => (w, c)) from by fun_prop)
  | (c :: d :: L), X, _, F, hF => by
      simp only [dirExp]
      have hG : Continuous (Function.uncurry
          (fun (p : X × ℝ) (x : ℝ) => F p.1 (p.2 * c + (1 - p.2) * x))) :=
        hF.comp (show Continuous (fun q : (X × ℝ) × ℝ =>
          (q.1.1, q.1.2 * c + (1 - q.1.2) * q.2)) from by fun_prop)
      have hrec := dirExp_param_continuous (d :: L)
        (fun (p : X × ℝ) (x : ℝ) => F p.1 (p.2 * c + (1 - p.2) * x)) hG
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ 0 1
      have hρ : Continuous (fun p : X × ℝ =>
          ((d :: L).length : ℝ) * (1 - p.2) ^ ((d :: L).length - 1)) := by fun_prop
      exact hρ.mul hrec

/--
@isnad1 id=eq.0h2v.s4.a5262ea001fb from=translated src=- shape=9975ce89 vocab=9cd15a92
-/
@[simp] lemma dirExp_singleton (c : ℝ) (f : ℝ → ℝ) : dirExp [c] f = f c := rfl

/--
@isnad1 id=eq.0h4v.s7.52ca043525bd from=translated src=- shape=8c514440 vocab=8cf1d15f
-/
lemma dirExp_cons_cons (c d : ℝ) (L : List ℝ) (f : ℝ → ℝ) :
    dirExp (c :: d :: L) f
      = ∫ t in (0:ℝ)..1, ((d :: L).length : ℝ) * (1 - t) ^ ((d :: L).length - 1)
          * dirExp (d :: L) (fun x => f (t * c + (1 - t) * x)) := rfl

/--
@isnad1 id=interval.1h3v.s7.238ce92f0833 from=translated src=- shape=982dbedc vocab=657e5ddb
-/
lemma dirExp_intervalIntegrable (T : List ℝ) (c : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    IntervalIntegrable
      (fun t => (T.length : ℝ) * (1 - t) ^ (T.length - 1) * dirExp T (fun x => f (t * c + (1 - t) * x)))
      volume 0 1 := by
  have hpc : Continuous (fun t => dirExp T (fun x => f (t * c + (1 - t) * x))) :=
    dirExp_param_continuous T (fun (t : ℝ) (x : ℝ) => f (t * c + (1 - t) * x)) (hf.comp (by fun_prop))
  exact Continuous.intervalIntegrable
    ((by fun_prop : Continuous (fun t : ℝ => (T.length : ℝ) * (1 - t) ^ (T.length - 1))).mul hpc) _ _

/--
@isnad1 id=eq.0h1v.s4.82b5b6d9f663 from=translated src=- shape=a9b381d3 vocab=592ae1eb
-/
lemma dirExp_zero : ∀ (L : List ℝ), dirExp L (fun _ => 0) = 0
  | [] => rfl
  | [_] => rfl
  | (c :: d :: L) => by
      rw [dirExp_cons_cons]
      simp only [dirExp_zero (d :: L), mul_zero, intervalIntegral.integral_zero]

/--
@isnad1 id=eq.0h3v.s5.74b4a951d817 from=translated src=- shape=e651d454 vocab=0fa9725f
-/
lemma dirExp_smul : ∀ (L : List ℝ) (a : ℝ) (f : ℝ → ℝ),
    dirExp L (fun x => a * f x) = a * dirExp L f
  | [], a, f => by simp [dirExp]
  | [c], a, f => by simp [dirExp]
  | (c :: d :: L), a, f => by
      rw [dirExp_cons_cons, dirExp_cons_cons, ← intervalIntegral.integral_const_mul]
      refine integral_congr fun t _ => ?_
      rw [dirExp_smul (d :: L) a (fun x => f (t * c + (1 - t) * x))]
      ring

/--
@isnad1 id=eq.2h3v.s6.12d684788823 from=translated src=- shape=332eafba vocab=18e38c01
-/
lemma dirExp_add : ∀ (L : List ℝ) (f g : ℝ → ℝ), Continuous f → Continuous g →
    dirExp L (fun x => f x + g x) = dirExp L f + dirExp L g
  | [], f, g, _, _ => by simp [dirExp]
  | [c], f, g, _, _ => by simp [dirExp]
  | (c :: d :: L), f, g, hf, hg => by
      rw [dirExp_cons_cons, dirExp_cons_cons, dirExp_cons_cons,
        ← intervalIntegral.integral_add
          (dirExp_intervalIntegrable (d :: L) c f hf) (dirExp_intervalIntegrable (d :: L) c g hg)]
      refine integral_congr fun t _ => ?_
      rw [dirExp_add (d :: L) (fun x => f (t * c + (1 - t) * x)) (fun x => g (t * c + (1 - t) * x))
        (by fun_prop) (by fun_prop)]
      ring

/--
@isnad1 id=eq.1h4v.s5.fc283c4e3f56 from=translated src=- shape=3cacfd46 vocab=53f8fde7
-/
lemma dirExp_finset_sum {ι : Type*} (L : List ℝ) (s : Finset ι) (F : ι → ℝ → ℝ)
    (hF : ∀ i, Continuous (F i)) :
    dirExp L (fun x => ∑ i ∈ s, F i x) = ∑ i ∈ s, dirExp L (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [Finset.sum_empty, dirExp_zero]
  | @insert a s ha ih =>
      have hcs : Continuous (fun x => ∑ i ∈ s, F i x) := continuous_finsetSum s fun i _ => hF i
      rw [show (fun x => ∑ i ∈ insert a s, F i x) = (fun x => F a x + ∑ i ∈ s, F i x) from by
            funext x; rw [Finset.sum_insert ha],
        dirExp_add L (F a) (fun x => ∑ i ∈ s, F i x) (hF a) hcs, ih, Finset.sum_insert ha]

/--
@isnad1 id=eq.1h2v.s6.4add794a270c from=translated src=- shape=dfbec6d2 vocab=612c3698
-/
lemma dirExp_pow : ∀ (L : List ℝ), L ≠ [] → ∀ (j : ℕ),
    dirExp L (fun x => x ^ j)
      = hsym L j / (Nat.choose (j + (L.length - 1)) (L.length - 1) : ℝ)
  | [], h, _ => absurd rfl h
  | [c], _, j => by
      simp [dirExp_singleton, hsym_singleton]
  | (c :: d :: L), _, j => by
      have hTne : (d :: L) ≠ [] := List.cons_ne_nil d L
      have hlen : (c :: d :: L).length - 1 = (d :: L).length := rfl
      rw [hlen, dirExp_cons_cons]

      have hinner : ∀ t : ℝ, dirExp (d :: L) (fun x => (t * c + (1 - t) * x) ^ j)
          = ∑ i ∈ Finset.range (j + 1),
              ((j.choose i : ℝ) * c ^ i
                * (hsym (d :: L) (j - i)
                    / (Nat.choose ((j - i) + ((d :: L).length - 1)) ((d :: L).length - 1) : ℝ)))
              * (t ^ i * (1 - t) ^ (j - i)) := by
        intro t
        rw [show (fun x : ℝ => (t * c + (1 - t) * x) ^ j)
              = (fun x => ∑ i ∈ Finset.range (j + 1),
                  ((j.choose i : ℝ) * (t * c) ^ i * (1 - t) ^ (j - i)) * x ^ (j - i)) from by
            funext x; rw [add_pow]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [mul_pow (1 - t) x (j - i)]; ring]
        rw [dirExp_finset_sum (d :: L) _ _ (fun i => by fun_prop)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [dirExp_smul (d :: L) _ (fun x => x ^ (j - i)), dirExp_pow (d :: L) hTne (j - i)]
        rw [mul_pow t c i]; ring

      have hterm : ∀ i ∈ Finset.range (j + 1),
          (∫ t in (0:ℝ)..1, ((d :: L).length : ℝ) * (1 - t) ^ ((d :: L).length - 1)
              * (((j.choose i : ℝ) * c ^ i
                  * (hsym (d :: L) (j - i)
                      / (Nat.choose ((j - i) + ((d :: L).length - 1)) ((d :: L).length - 1) : ℝ)))
                * (t ^ i * (1 - t) ^ (j - i))))
            = c ^ i * hsym (d :: L) (j - i)
                / (Nat.choose (j + (d :: L).length) (d :: L).length : ℝ) := by
        intro i hi
        rw [Finset.mem_range, Nat.lt_succ_iff] at hi
        set s := (d :: L).length with hs
        have hs1 : 1 ≤ s := by rw [hs]; simp
        rw [show (∫ t in (0:ℝ)..1, (s : ℝ) * (1 - t) ^ (s - 1)
                * (((j.choose i : ℝ) * c ^ i
                    * (hsym (d :: L) (j - i) / (Nat.choose ((j - i) + (s - 1)) (s - 1) : ℝ)))
                  * (t ^ i * (1 - t) ^ (j - i))))
              = ∫ t in (0:ℝ)..1, ((s : ℝ) * (j.choose i : ℝ) * c ^ i
                    * (hsym (d :: L) (j - i) / (Nat.choose ((j - i) + (s - 1)) (s - 1) : ℝ)))
                  * (t ^ i * (1 - t) ^ ((s - 1) + (j - i))) from
            integral_congr fun t _ => by rw [pow_add]; ring]
        rw [intervalIntegral.integral_const_mul, beta_nat i ((s - 1) + (j - i)),
          show i + ((s - 1) + (j - i)) + 1 = j + s from by omega,
          show (s - 1) + (j - i) = (j - i) + (s - 1) from by omega]
        have hA : (j.choose i : ℝ) * (Nat.factorial i : ℝ) * (Nat.factorial (j - i) : ℝ)
            = (Nat.factorial j : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
        have hB : (Nat.choose ((j - i) + (s - 1)) (s - 1) : ℝ) * (Nat.factorial (s - 1) : ℝ)
              * (Nat.factorial (j - i) : ℝ) = (Nat.factorial ((j - i) + (s - 1)) : ℝ) := by
          have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left (s - 1) (j - i))
          rw [Nat.add_sub_cancel] at h; exact_mod_cast h
        have hC : (Nat.choose (j + s) s : ℝ) * (Nat.factorial s : ℝ) * (Nat.factorial j : ℝ)
            = (Nat.factorial (j + s) : ℝ) := by
          have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left s j)
          rw [Nat.add_sub_cancel] at h; exact_mod_cast h
        have hsf : (s : ℝ) * (Nat.factorial (s - 1) : ℝ) = (Nat.factorial s : ℝ) := by
          exact_mod_cast Nat.mul_factorial_pred (by omega : s ≠ 0)
        have hCb : (Nat.choose ((j - i) + (s - 1)) (s - 1) : ℝ) ≠ 0 := by
          have := Nat.choose_pos (Nat.le_add_left (s - 1) (j - i)); positivity
        have hfjs : (Nat.factorial (j + s) : ℝ) ≠ 0 := by positivity
        have hCc : (Nat.choose (j + s) s : ℝ) ≠ 0 := by
          have := Nat.choose_pos (Nat.le_add_left s j); positivity
        have hMAIN : (s : ℝ) * (j.choose i : ℝ) * (Nat.factorial i : ℝ)
              * (Nat.factorial ((j - i) + (s - 1)) : ℝ) * (Nat.choose (j + s) s : ℝ)
            = (Nat.choose ((j - i) + (s - 1)) (s - 1) : ℝ) * (Nat.factorial (j + s) : ℝ) := by
          rw [← hB, ← hC, ← hsf, ← hA]; ring
        field_simp
        linear_combination (c ^ i * hsym (d :: L) (j - i)) * hMAIN

      rw [show (∫ t in (0:ℝ)..1, ((d :: L).length : ℝ) * (1 - t) ^ ((d :: L).length - 1)
                * dirExp (d :: L) (fun x => (t * c + (1 - t) * x) ^ j))
            = ∑ i ∈ Finset.range (j + 1),
                (∫ t in (0:ℝ)..1, ((d :: L).length : ℝ) * (1 - t) ^ ((d :: L).length - 1)
                  * (((j.choose i : ℝ) * c ^ i
                      * (hsym (d :: L) (j - i)
                          / (Nat.choose ((j - i) + ((d :: L).length - 1)) ((d :: L).length - 1) : ℝ)))
                    * (t ^ i * (1 - t) ^ (j - i)))) from by
        rw [← intervalIntegral.integral_finsetSum (fun i _ => by
              apply Continuous.intervalIntegrable; fun_prop)]
        refine integral_congr fun t _ => ?_
        rw [hinner t, Finset.mul_sum]]
      rw [Finset.sum_congr rfl hterm, hsym_cons, Finset.sum_div]

/--
@isnad1 id=eq.3h4v.s6.8f046802d4d6 from=translated src=- shape=72726bb6 vocab=830b00fb
-/
lemma multiKernel_eq_dirExp {m r : ℕ} (hr : r ≠ 0) (hn : 1 ≤ m - 2 * r) (q : ℝ) (L : List ℝ)
    (hLlen : L.length = r) :
    multiKernel m r q L = dirExp L (fun x => diagKernel m r q x) := by
  have hLne : L ≠ [] := by rintro rfl; simp at hLlen; exact hr hLlen.symm
  rw [multiKernel_expand hr hn,
    show (fun x => diagKernel m r q x)
        = (fun x => ∑ j ∈ Finset.range (m - 2 * r + 1),
            kerB m r q j * ((Nat.choose (j + (r - 1)) (r - 1) : ℝ) * x ^ j)) from by
      funext x; rw [diagKernel_expand hr hn],
    dirExp_finset_sum L _ _ (fun j => by fun_prop)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hCne : (Nat.choose (j + (r - 1)) (r - 1) : ℝ) ≠ 0 := by
    have := Nat.choose_pos (Nat.le_add_left (r - 1) j); positivity
  rw [show (fun x => kerB m r q j * ((Nat.choose (j + (r - 1)) (r - 1) : ℝ) * x ^ j))
        = (fun x => (kerB m r q j * (Nat.choose (j + (r - 1)) (r - 1) : ℝ)) * x ^ j) from by
      funext x; ring,
    dirExp_smul L _ (fun x => x ^ j), dirExp_pow L hLne j, hLlen]
  field_simp

/--
@isnad1 id=le.5h4v.s7.f3a37d652838 from=translated src=- shape=324cfaef vocab=2f10de1b
-/
theorem multiKernel_nonneg {m r : ℕ} (hr : r ≠ 0) (hn : 1 ≤ m - 2 * r) (q : ℝ) (L : List ℝ)
    (hLlen : L.length = r)
    (hdiag : ∀ ℓ ∈ Set.Icc (-(1:ℝ) / 2) (1 / 2), 0 ≤ diagKernel m r q ℓ)
    (hL : ∀ x ∈ L, x ∈ Set.Icc (-(1:ℝ) / 2) (1 / 2)) :
    0 ≤ multiKernel m r q L := by
  rw [multiKernel_eq_dirExp hr hn q L hLlen]
  exact dirExp_nonneg L _ (-(1:ℝ) / 2) (1 / 2) (by norm_num) hdiag hL

end OddCycleBound.DenseRegion
