/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov, Aristotle (Harmonic)
-/
module

public import Tengoku.Arklib.ArkLib.Data.Polynomial.Bivariate

public import Tengoku.Seed.Algebra.Polynomial.Basic
public import Tengoku.Seed.Tactic.Cases
public import Tengoku.Seed.Tactic.LinearCombinationPrime
public import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  Proof of Proposition 6.3 from [BS08].

  The statement is taken from [ACFY24]. Namely,
  ```latex
  \textbf{Fact 4.6 (BS08).} \textit{Given a polynomial } $\hat{q} \in \mathbb{F}[X]$:

  \begin{itemize}
      \item For every $\hat{f} \in \mathbb{F}[X]$ there exists a unique bivariate polynomial
      $\hat{Q} \in \mathbb{F}[X,Y]$ with
      \[
          \deg_X(\hat{Q}) = \left\lfloor \frac{\deg(\hat{f})}{\deg(\hat{q})} \right\rfloor
          \quad \text{and} \quad
          \deg_Y(\hat{Q}) < \deg(\hat{q})
      \]
      such that
      \[
          \hat{f}(Z) = \hat{Q}(\hat{q}(Z), Z).
      \]
      Moreover, $\hat{Q}$ can be computed efficiently given $\hat{f}$ and $\hat{q}$.
      Observe that if $\deg(\hat{f}) < t \cdot \deg(\hat{q})$ then
      $\deg_X(\hat{Q}) < t$.

      \item For every $\hat{Q} \in \mathbb{F}[X,Y]$ with
      $\deg_X(\hat{Q}) < t$ and $\deg_Y(\hat{Q}) < \deg(\hat{q})$,
      the polynomial
      \[
          \hat{f}(Z) := \hat{Q}(\hat{q}(Z), Z)
      \]
      has degree
      \[
          \deg(\hat{f}) < t \cdot \deg(\hat{q}).
      \]
  \end{itemize}
  ```

## References

* [Ben-Sasson, E., Madhu, S., *Short PCPs with Polylog Query Complexity*][BS08]
* [Arnon, G., Chiesa, A., Fenzi, G., Yogev, E.,
  *STIR: Reed–Solomon Proximity Testing with Fewer Queries*][ACFY24]

-/

@[expose] public section

namespace Polynomial.FoldingPolynomial

section

open Polynomial Polynomial.Bivariate

variable {ι F : Type*} [Field F]

/-- The definition of the folding polynomial `Q`
    from the proposition that takes `fuel` value
    as the upper bound of number of steps needed
    to produce the polynomial `Q`.-/
noncomputable def foldingPolynomialAux (q f : F[X]) (fuel : ℕ) : F[X][Y] :=
  -- The main idea behind the `fuel` argument
  -- is to assure the totality checker that
  -- the recursive function is indeed total
  -- by providing the upper bound on the number
  -- of iterations.
  --
  -- Later on, we eliminate it in the public API `foldingPolynomial`.
  if q.degree ≤ 0 then Polynomial.map C f else
  if f.degree < q.degree then Polynomial.map C f
  else
  match fuel with
  | .zero => Polynomial.map Polynomial.C f
  | .succ fuel => (Polynomial.map Polynomial.C (f % q))
    + Polynomial.C Polynomial.X * (foldingPolynomialAux q (f / q) fuel)

/-- The bivariate polynomial `Q` such that
    `f = Q(q(X), X)`, `Q.degreeX = f.natDegree / q.natDegree`,
    and `Q.natDegreeY < q.natDegree`, if `q` is not a constant polynomial.-/
noncomputable def foldingPolynomial (q f : F[X]) : F[X][Y] :=
  foldingPolynomialAux q f f.natDegree

lemma folding_polynomial_eq_map_of_f_degree_lt_q_degree {q f : F[X]}
    (h : f.degree < q.degree) :
    foldingPolynomial q f = Polynomial.map C f := by
  unfold foldingPolynomial foldingPolynomialAux
  simp [h]

@[simp]
lemma folding_polynomial_C_q {q : F} {f : F[X]} :
    foldingPolynomial (C q) f = Polynomial.map C f := by
  unfold foldingPolynomial foldingPolynomialAux
  simp only [ite_eq_left_iff, not_le, not_lt]
  intro h
  have contra : (0 : WithBot ℕ) < 0 :=
    lt_of_lt_of_le h (Polynomial.degree_C_le (a := q))
  simp at contra

@[simp]
lemma foldingPolynomial_C_f {f : F} {q : F[X]} :
    foldingPolynomial q (C f) = C (C f) := by
  unfold foldingPolynomial foldingPolynomialAux
  simp

@[simp]
lemma foldingPolynomial_zero {q : F[X]} :
    foldingPolynomial q 0 = 0 := by
  unfold foldingPolynomial foldingPolynomialAux
  simp

private lemma folding_polynomial_def_base_case {q f : F[X]}
  (h : f.degree < q.degree ∨ f.degree ≤ 0 ∨ q.degree ≤ 0) :
    foldingPolynomial q f = Polynomial.map C f := by
  rcases h with h | h | h
    <;> try (
      rw [Polynomial.degree_le_zero_iff] at h
      rw [h]
      simp [map_C, folding_polynomial_C_q])
  rw [folding_polynomial_eq_map_of_f_degree_lt_q_degree h]

private lemma natDegree_div_eq_sub_of_degree_le {q f : F[X]}
    (hq : q ≠ 0) (hdeg : q.degree ≤ f.degree) :
    (f / q).natDegree = f.natDegree - q.natDegree := by
  have hdiv : f / q ≠ 0 :=
    mt (Polynomial.div_eq_zero_iff hq).mp (not_lt_of_ge hdeg)
  have hadd := Polynomial.degree_add_div hq hdeg
  rw [Polynomial.degree_eq_natDegree hq,
    Polynomial.degree_eq_natDegree hdiv] at hadd
  have hf : f ≠ 0 := by
    intro hf
    subst f
    exact hq (Polynomial.degree_eq_bot.mp (bot_unique hdeg))
  rw [Polynomial.degree_eq_natDegree hf] at hadd
  norm_cast at hadd
  omega

private lemma folding_polynomial_aux_natDegree_fuel_is_enough {q f : F[X]} {fuel : ℕ}
  (h : f.natDegree ≤ fuel) :
  foldingPolynomialAux q f f.natDegree = foldingPolynomialAux q f fuel := by
  have h_foldingPolynomialAux :
    ∀ (deg₁ deg₂ : ℕ),
      deg₁ ≥ f.natDegree →
        deg₂ ≥ f.natDegree →
          foldingPolynomialAux q f deg₁ = foldingPolynomialAux q f deg₂ := by
      intro deg₁ deg₂ h₁ h₂
      induction deg₁ generalizing deg₂ f with
      | zero =>
        simp_all +decide only [ge_iff_le, nonpos_iff_eq_zero, natDegree_eq_zero_iff_degree_le_zero]
        rw [Polynomial.eq_C_of_degree_le_zero h₁]
        simp +decide only [foldingPolynomialAux, map_C, ite_self]
        rcases deg₂ with _ | deg₂
          <;> simp_all only
                [foldingPolynomialAux,
                 map_C,
                 left_eq_ite_iff,
                 not_le, not_lt, nonpos_iff_eq_zero,
                 foldingPolynomialAux, map_C, ite_self]
        exact fun h₃ h₄ ↦
          absurd h₄
            (not_le_of_gt (lt_of_le_of_lt (Polynomial.degree_C_le) h₃))
      | succ deg₁ ih =>
        rcases deg₂ with _ | deg₂
          <;> simp_all +decide only
                [ge_iff_le,
                 nonpos_iff_eq_zero,
                 foldingPolynomialAux,
                 ite_self,
                 ite_eq_left_iff,
                 not_le,
                 not_lt,
                 zero_le]
        · obtain ⟨c, hc⟩ : ∃ c : F, f = Polynomial.C c :=
            ⟨f.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero h₂⟩
          by_cases hc : c = 0 <;> simp_all +decide [Polynomial.degree_C]
          aesop
        · split_ifs <;> simp_all +decide only [
              not_le,
              not_lt,
              add_right_inj,
              mul_eq_mul_left_iff,
              C_eq_zero,
              X_ne_zero,
              or_false]
          have h_div_deg : (f / q).natDegree ≤ f.natDegree - q.natDegree := by
            rw [Polynomial.div_def]
            rw [Polynomial.natDegree_C_mul, Polynomial.natDegree_divByMonic]
            · rw [Polynomial.natDegree_mul'] <;> aesop
            · exact Polynomial.monic_mul_leadingCoeff_inv (by aesop)
            · aesop
          by_cases hq : q.natDegree = 0
          · rw [Polynomial.degree_eq_natDegree] at * <;> aesop
          · exact ih (by omega) _ (by omega) (by omega)
  exact h_foldingPolynomialAux _ _ le_rfl h

private lemma folding_polynomial_def_ind_case {q f : F[X]}
  (h₁ : f.degree ≥ q.degree)
  (h₂ : q.degree > 0) :
  foldingPolynomial q f = (Polynomial.map Polynomial.C (f % q)) +
    Polynomial.C Polynomial.X * foldingPolynomial q (f / q) := by
      have h_fold :
        ∀ {deg : ℕ},
          deg ≥ f.natDegree →
            foldingPolynomial q f =
              Polynomial.map Polynomial.C (f % q) +
                Polynomial.C Polynomial.X *
                  foldingPolynomial q (f / q) := by
        intros deg hdeg
        rw [foldingPolynomial]
        have h_fold :
          ∀ {deg : ℕ},
            deg ≥ f.natDegree →
              foldingPolynomialAux q f deg =
                Polynomial.map Polynomial.C (f % q) +
                  Polynomial.C Polynomial.X *
                    foldingPolynomialAux q (f / q) (deg - 1) := by
          intros deg hdeg
          induction deg generalizing f with
          | zero =>
            obtain ⟨c, hc⟩ : ∃ c : F, f = Polynomial.C c :=
              ⟨f.coeff 0, Polynomial.eq_C_of_natDegree_le_zero hdeg⟩
            simp_all +decide only [gt_iff_lt, ge_iff_le, natDegree_C, zero_le, zero_tsub]
            exact absurd h₁ (not_le_of_gt (lt_of_le_of_lt (Polynomial.degree_C_le) h₂))
          | succ deg ih =>
            rw [foldingPolynomialAux]
            rw [ite_eq_right h₂.not_ge, ite_eq_right (not_lt_of_ge h₁)]
            rfl
        convert h_fold hdeg using 1
        · exact folding_polynomial_aux_natDegree_fuel_is_enough hdeg
        · have h_fold_eq :
            foldingPolynomial q (f / q)
              = foldingPolynomialAux q (f / q) (deg - 1) := by
            have h_deg : (f / q).natDegree ≤ deg - 1 := by
              have h_deg : (f / q).natDegree ≤ f.natDegree - q.natDegree := by
                rw [natDegree_div_eq_sub_of_degree_le
                  (Polynomial.ne_zero_of_degree_gt h₂) h₁]
              exact le_trans h_deg (Nat.sub_le_sub_right hdeg _)
                |> le_trans
                <| Nat.sub_le_sub_left (Polynomial.natDegree_pos_iff_degree_pos.mpr h₂) _
            apply folding_polynomial_aux_natDegree_fuel_is_enough
            assumption
          rw [h_fold_eq]
      exact h_fold le_rfl

/-- If the folding polynomial is zero
  then so is the original polynomial.-/
lemma eq_zero_of_folding_polynomial_eq_zero {q f : F[X]}
    (h : foldingPolynomial q f = 0) : f = 0 := by
    induction n : f.natDegree using Nat.strong_induction_on generalizing f with
    | h n' ih =>
      by_cases h₁ :
      f.degree < q.degree
        ∨ f.degree ≤ 0
        ∨ q.degree ≤ 0 <;> simp_all only [ext_iff, coeff_zero, not_or, not_lt, not_le]
      · rw [folding_polynomial_def_base_case h₁] at h
        intro n
        specialize h n 0
        aesop
      · have h_rem_zero : f % q = 0 := by
          rw [folding_polynomial_def_ind_case h₁.1 h₁.2.2] at h
          ext n
          specialize h n 0
          simp_all +decide [Polynomial.coeff_map]
        have h_quot_zero : f / q = 0 := by
          have h_quot_zero : foldingPolynomial q (f / q) = 0 := by
            have h_quot_zero :
            foldingPolynomial q f
              = (Polynomial.map Polynomial.C (f % q))
                + Polynomial.C Polynomial.X
                    * foldingPolynomial q (f / q) := by
              rw [folding_polynomial_def_ind_case] <;> aesop
            simp_all +decide only [Polynomial.map_zero, zero_add, coeff_C_mul,
            EuclideanDomain.mod_eq_zero, ext_iff, coeff_add, coeff_map, add_zero, coeff_zero]
            intro n n_1
            specialize h n (n_1 + 1)
            simp_all +decide
          contrapose! ih
          refine
            ⟨Polynomial.natDegree (f / q),
            by {
              rw [natDegree_div_eq_sub_of_degree_le
                (Polynomial.ne_zero_of_degree_gt h₁.2.2) h₁.1]
              rw [← n]
              exact Nat.sub_lt
                (Polynomial.natDegree_pos_iff_degree_pos.mpr h₁.2.1)
                (Polynomial.natDegree_pos_iff_degree_pos.mpr h₁.2.2)
            },
            f / q,
            by simp_all +decide,
            rfl,
            Polynomial.natDegree (f / q), by simp [ih]⟩
        rw [EuclideanDomain.mod_eq_sub_mul_div] at h_rem_zero
        aesop

lemma folding_polynomial_ne_zero_of_ne_zero {q f : F[X]}
    (h : f ≠ 0) : foldingPolynomial q f ≠ 0 := fun contra ↦ by
  simp_all [eq_zero_of_folding_polynomial_eq_zero contra]

lemma substitution_property_of_folding_polynomial {q f : F[X]} :
    ((foldingPolynomial q f).map (Polynomial.compRingHom q)).eval X = f := by
  revert q f
  intro q f
  induction n : f.natDegree using Nat.strong_induction_on generalizing q f with
  | h n ih =>
    by_cases h_deg : f.degree < q.degree ∨ f.degree ≤ 0 ∨ q.degree ≤ 0
    · rw [folding_polynomial_def_base_case h_deg]
      simp +decide only [eval_map]
      simp +decide only [eval₂_map]
      simp +decide only
        [eval₂_eq_sum_range,
         RingHom.coe_comp,
         coe_compRingHom,
         Function.comp_apply,
         C_comp]
      conv_rhs => rw [Polynomial.as_sum_range_C_mul_X_pow f]
    · have h_fold_def :
        foldingPolynomial q f =
          (Polynomial.map Polynomial.C (f % q)) +
            Polynomial.C Polynomial.X * foldingPolynomial q (f / q) := by
        apply folding_polynomial_def_ind_case
        · exact le_of_not_gt fun h ↦ h_deg <| Or.inl h
        · exact lt_of_not_ge fun h ↦ h_deg <| Or.inr <| Or.inr h
      have h_fold_def :
        Polynomial.eval Polynomial.X
          (Polynomial.map q.compRingHom (foldingPolynomial q f)) =
            (f % q) +
              q * Polynomial.eval Polynomial.X
                (Polynomial.map q.compRingHom (foldingPolynomial q (f / q))) := by
        simp +decide only
          [h_fold_def,
           Polynomial.map_add,
           Polynomial.map_mul,
           map_C,
           coe_compRingHom,
           X_comp,
           eval_add,
           eval_map,
           eval_mul,
           eval_C,
           add_left_inj]
        simp +decide only [eval₂_map]
        simp +decide only
          [eval₂_eq_sum_range,
           RingHom.coe_comp,
           coe_compRingHom,
           Function.comp_apply,
           C_comp]
        conv_rhs => rw [Polynomial.as_sum_range_C_mul_X_pow (f % q)]
      have h_fold_def :
        Polynomial.eval Polynomial.X
          (Polynomial.map q.compRingHom
            (foldingPolynomial q (f / q))) = f / q := by
        convert ih (Polynomial.natDegree (f / q)) _ rfl using 1
        have hqpos : 0 < q.degree :=
          lt_of_not_ge fun h => h_deg (Or.inr (Or.inr h))
        have hfpos : 0 < f.degree :=
          lt_of_not_ge fun h => h_deg (Or.inr (Or.inl h))
        have hqle : q.degree ≤ f.degree :=
          le_of_not_gt fun h => h_deg (Or.inl h)
        rw [←n, natDegree_div_eq_sub_of_degree_le
          (Polynomial.ne_zero_of_degree_gt hqpos) hqle]
        exact Nat.sub_lt
          (Polynomial.natDegree_pos_iff_degree_pos.mpr hfpos)
          (Polynomial.natDegree_pos_iff_degree_pos.mpr hqpos)
      rw [
        ‹Polynomial.eval Polynomial.X
          (Polynomial.map q.compRingHom
            (foldingPolynomial q f)) =
              f % q +
                q * Polynomial.eval Polynomial.X
                  (Polynomial.map q.compRingHom
                    (foldingPolynomial q (f / q)))›,
        h_fold_def, EuclideanDomain.mod_eq_sub_mul_div]
      ring

/-- A means to evaluate the original polynomial in terms of
  the folding polynomial.-/
lemma eval_property_of_folding_polynomial {q f : F[X]} {x : F} :
    ((foldingPolynomial q f).map (Polynomial.evalRingHom (q.eval x))).eval x = f.eval x := by
  have h_subst : ((Polynomial.FoldingPolynomial.foldingPolynomial q f).map
    (Polynomial.compRingHom q)).eval X = f :=
      substitution_property_of_folding_polynomial
  generalize_proofs at *
  (replace h_subst := congr_arg (Polynomial.eval x) h_subst
   simp_all only [eval_map]
   convert h_subst using 1
   simp +decide [Polynomial.eval₂_eq_sum_range]
   ring_nf
   simp +decide [Polynomial.eval_finsetSum])

/-- A means to evaluate the original polynomial in terms of
  the folding polynomial when `q = X ^ k`.-/
lemma eval_property_of_folding_polynomial_x_k {f : F[X]} {k : ℕ} {x : F} :
    ((foldingPolynomial (X ^ k) f).map (Polynomial.evalRingHom (x ^ k))).eval x =
    f.eval x := by
  simpa only [Polynomial.eval_X_pow] using
    (eval_property_of_folding_polynomial (f := f) (q := X ^ k) (x := x))

private lemma satisfies_composition_property_implies_is_the_reminder
  {q f : F[X]}
  {Q : F[X][Y]}
  (h : (Q.map (Polynomial.compRingHom q)).eval X = f) :
  ∃ Q': F[X][Y],
    Polynomial.map C f = Q' * (C X - Polynomial.map C q) + Q := by
      obtain ⟨Q', hQ'⟩ :
        ∃ Q' : F[X][Y],
          Q - Polynomial.map (Polynomial.C) f =
            (Polynomial.C Polynomial.X - Polynomial.map Polynomial.C q) * Q' := by
        have h_div :
          (Polynomial.C Polynomial.X - Polynomial.map Polynomial.C q) ∣
            Q - Polynomial.map (Polynomial.C)
                    (Polynomial.eval Polynomial.X
                        (Polynomial.map
                            (Polynomial.compRingHom q) Q)) := by
          have h_div :
            ∀ p : F[X][Y],
              (Polynomial.C Polynomial.X - Polynomial.map Polynomial.C q) ∣
                  p - Polynomial.map Polynomial.C
                        (Polynomial.eval Polynomial.X
                          (Polynomial.map (Polynomial.compRingHom q) p)) := by
            intro p
            induction p using Polynomial.induction_on' with
            | add p q hp hq =>
              convert dvd_add hp hq using 1
              simp +decide [sub_add_sub_comm]
            | monomial n p =>
              induction n with
              | zero =>
                simp_all +decide only [←C_mul_X_pow_eq_monomial, Polynomial.map_mul, map_C,
                  coe_compRingHom, Polynomial.map_pow, map_X, eval_mul, eval_C, eval_pow, eval_X]
                induction ‹F[X]› using
                  Polynomial.induction_on' with
                | add p q hp hq =>
                  simp_all +decide only [pow_zero, mul_one, map_add, add_comp,
                    Polynomial.map_add]
                  convert dvd_add hp hq using 1
                  ring
                | monomial n p =>
                  simp_all only [pow_zero, mul_one,
                  ←C_mul_X_pow_eq_monomial, map_mul, map_pow,
                    pow_zero, mul_one, mul_comp, C_comp, pow_comp, X_comp, Polynomial.map_mul,
                    map_C, Polynomial.map_pow]
                  exact dvd_trans
                    (sub_dvd_pow_sub_pow _ _ _)
                    ⟨Polynomial.C (Polynomial.C ‹_›), by ring⟩
              | succ n ih =>
                simp_all +decide only [←C_mul_X_pow_eq_monomial, Polynomial.map_mul, map_C,
                  coe_compRingHom, Polynomial.map_pow, map_X, eval_mul, eval_C, eval_pow, eval_X,
                  pow_succ, ←mul_assoc]
                simpa only [sub_mul] using ih.mul_right _
          exact h_div Q
        aesop
      exact ⟨-Q', by linear_combination -hQ'⟩

/-- An alternative description of the folding polynomial
    as the reminder in bivariate polynomial division
    of the form `f = Q' * (X - q(Y)) + Q`.-/
lemma folding_polynomial_is_the_reminder {q f : F[X]} :
    ∃ Q': F[X][Y],
    Polynomial.map C f = Q' * (C X - Polynomial.map C q) + (foldingPolynomial q f) :=
    satisfies_composition_property_implies_is_the_reminder
      substitution_property_of_folding_polynomial

/-- Polynomial folding function that turns
    a polynomial of degree `≤n` into a polynomial
    of degree `≤n/k` for given `k`.
    The key ingridient of FRI-related family of protocols.-/
noncomputable def polyFold (f : F[X]) (k : ℕ) (r : F) : F[X] :=
  (foldingPolynomial (X ^ k) f).eval (C r)

@[simp high]
lemma polyFold_zero_eq_zero {k : ℕ} {r : F} :
    polyFold 0 k r = 0 := by simp [polyFold]

section PolyFoldRecurrence

variable {F : Type*} [Field F]

/-- Evaluating `Polynomial.map C f` at `C r` recovers `C (f.eval r)`.-/
private lemma eval_C_map_C (f : F[X]) (r : F) :
    (Polynomial.map Polynomial.C f).eval (Polynomial.C r) = Polynomial.C (f.eval r) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range,
      Polynomial.eval_eq_sum_range, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow]

/-- Base case of `polyFold`: when `k = 0` or `f` has degree below `k`,
    `polyFold f k r = C (f.eval r)`.-/
lemma polyFold_base {f : F[X]} {k : ℕ} {r : F} (h : k = 0 ∨ f.natDegree < k) :
    polyFold f k r = Polynomial.C (f.eval r) := by
  unfold polyFold
  have h_deg : f.degree < (X^k : F[X]).degree ∨ f.degree ≤ 0 ∨ (X^k : F[X]).degree ≤ 0 := by
    rcases h with rfl | hlt
    · right; right
      rw [pow_zero]; simp
    · left
      rw [Polynomial.degree_X_pow]
      by_cases hf : f = 0
      · rw [hf, Polynomial.degree_zero]; exact WithBot.bot_lt_coe k
      · rw [Polynomial.degree_eq_natDegree hf]; exact_mod_cast hlt
  rw [folding_polynomial_def_base_case h_deg]
  exact eval_C_map_C f r

/-- Recursive case of `polyFold`: when `0 < k ≤ f.natDegree`,
    `polyFold f k r = C ((f %ₘ X^k).eval r) + X * polyFold (f /ₘ X^k) k r`.-/
lemma polyFold_step {f : F[X]} {k : ℕ} {r : F} (hk : 0 < k) (hf : k ≤ f.natDegree) :
    polyFold f k r =
      Polynomial.C ((f %ₘ X^k).eval r) + X * polyFold (f /ₘ X^k) k r := by
  unfold polyFold
  have h_deg_q : 0 < (X^k : F[X]).degree := by
    rw [Polynomial.degree_X_pow]; exact_mod_cast hk
  have h_deg_f : (X^k : F[X]).degree ≤ f.degree := by
    rw [Polynomial.degree_X_pow]
    have hf0 : f ≠ 0 := by
      rintro rfl; simp at hf; omega
    rw [Polynomial.degree_eq_natDegree hf0]; exact_mod_cast hf
  rw [folding_polynomial_def_ind_case h_deg_f h_deg_q]
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, eval_C_map_C]
  rw [show f / X^k = f /ₘ X^k from
        (divByMonic_eq_div f (Polynomial.monic_X_pow k)).symm,
      show f % X^k = f %ₘ X^k from
        (modByMonic_eq_mod f (Polynomial.monic_X_pow k)).symm]

end PolyFoldRecurrence

end

end FoldingPolynomial
end Polynomial

namespace CompPoly.CPolynomial.FoldingPolynomial

variable {F : Type*} [Field F] [DecidableEq F]

end CompPoly.CPolynomial.FoldingPolynomial
