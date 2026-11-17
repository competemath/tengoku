import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.StringDiagramsLean.StringDiagrams.Examples.OddTemperleyLieb.Basic
import Tengoku.StringDiagramsLean.StringDiagrams.Examples.TemperleyLieb.Representation
import Tengoku.StringDiagramsLean.StringDiagrams.Examples.OddTemperleyLieb.Dyck

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The representation `G` of the odd Temperley–Lieb supercategory (Lemma A.1)

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, Lemma A.1.

Let `V` be the superspace with basis `v₁` (even) and `v₋₁` (odd). Lemma A.1 asserts that there
is a monoidal superfunctor `G : STL(δ) → SVec` with `G(n) = V^{⊗n}`, sending the cup to
`1 ↦ v₋₁ ⊗ v₁ - q v₁ ⊗ v₋₁` and the cap to the form with
`v₁ ⊗ v₁ ↦ 0`, `v₁ ⊗ v₋₁ ↦ 1`, `v₋₁ ⊗ v₁ ↦ -ε q⁻¹ = q⁻¹`, `v₋₁ ⊗ v₋₁ ↦ 0`,
where `δ = -(q + ε q⁻¹) = -(q - q⁻¹)`.

This file constructs `G` as an `R`-linear functor `rep q : STL(δ) ⥤ ModuleCat R` over any
commutative ring `R` with a unit `q` (the appendix works over a field of characteristic
different from `2` with `q` not a root of unity; neither assumption is needed here), and checks
its values on the generators (`rep_cup_single`, `rep_cap_single`).

## The model of `V^{⊗n}` and the Koszul signs

As for the Temperley–Lieb representation (`StringDiagrams.TemperleyLieb.Rep`), the object with
`n` strands goes to `Word n → R`, where `Word n` is the type of lists of length `n` over
`Fin 2`; the letter `0` stands for `v₁` (even) and the letter `1` for `v₋₁` (odd), and a
function `f` is the vector `Σ_w f(w) v_{w₁} ⊗ ⋯ ⊗ v_{wₙ}`. The parity of `v_w` is the number of
letters `1` in `w` modulo `2`.

A layer `1_l ⊗ g ⊗ 1_r` with `g` odd acts, by the sign rule for tensor products of linear maps
between superspaces, by `x ⊗ y ⊗ z ↦ (-1)^{|x|} x ⊗ g(y) ⊗ z`. In terms of coefficient
functions this is the Temperley–Lieb layer operator multiplied by the sign
`psign p w = (-1)^{(number of letters 1 among the first p letters of w)}` (`cupOp`, `capOp`).
These Koszul signs make generators at disjoint positions anticommute, as required by the super
interchange law (`cup_cup_op`, `cup_cap_op`, `cap_cup_op`, `cap_cap_op`).

The structure of `rep q` as a monoidal superfunctor into the monoidal supercategory of
superspaces is in `StringDiagrams.Examples.OddTemperleyLieb.MonoidalRep` (`Rep.repSMonoidal`).
-/

noncomputable section

namespace StringDiagrams.OddTemperleyLieb.Rep

open CategoryTheory
open TemperleyLieb.Rep (Word ins del ext res Agree length_ins length_del getD_ins_lt
  getD_ins_self getD_ins_succ getD_ins_ge getD_del_lt getD_del_ge del_ins del_succ_ins
  del_ins_succ set_getD_self ins_ins del_del del_ins_far del_ins_far' ext_apply_of_length
  ext_apply_word res_apply)

/-! ## Parities of prefixes -/

/-- The number of letters `1` (odd basis vectors) in a word.-/
def nOdd : List (Fin 2) → ℕ
  | [] => 0
  | a :: w => a.val + nOdd w

/--
@isnad1 id=eq.0h0v.s3.9e2b2f432430 from=translated src=- shape=120b6148 vocab=5de63d77
-/
@[simp] theorem nOdd_nil : nOdd [] = 0 := rfl

/--
@isnad1 id=eq.0h2v.s5.1224eae2cc2e from=translated src=- shape=9b929969 vocab=929af6f7
-/
@[simp] theorem nOdd_cons (a : Fin 2) (w : List (Fin 2)) : nOdd (a :: w) = a.val + nOdd w := rfl

variable {R : Type*} [CommRing R]

/-- The Koszul sign of a layer at position `p` acting on the basis vector `v_w`:
`(-1)^{|v_{w₁}| + ⋯ + |v_{w_p}|}`.-/
def psign (R : Type*) [CommRing R] (p : ℕ) (w : List (Fin 2)) : R := (-1) ^ nOdd (w.take p)

/--
@isnad1 id=eq.0h3v.s5.8b040a3d754b from=translated src=- shape=62c0a824 vocab=cb0211dd
-/
theorem psign_mul_self (p : ℕ) (w : List (Fin 2)) : psign R p w * psign R p w = 1 := by
  rw [psign, ← pow_add, ← two_mul, pow_mul]; simp

/--
@isnad1 id=eq.2h6v.s6.8be8f9d2a46c from=translated src=- shape=1f74a47a vocab=8d3cf017
-/
theorem psign_ins_le {p q : ℕ} (a b : Fin 2) {w : List (Fin 2)} (h : p ≤ q)
    (hq : q ≤ w.length) : psign R p (ins q a b w) = psign R p w := by
  unfold psign
  congr 2
  induction q generalizing p w with
  | zero => obtain rfl : p = 0 := by omega
            simp
  | succ q ih => cases p with
    | zero => simp
    | succ p => cases w with
      | nil => simp at hq
      | cons x w =>
        simp only [ins, List.take_succ_cons]
        rw [ih (by omega) (by simp at hq; omega)]

/--
@isnad1 id=eq.2h6v.s7.7fa4fe912d87 from=translated src=- shape=1404f0ea vocab=4fac77ed
-/
theorem psign_ins_ge {p q : ℕ} (a b : Fin 2) {w : List (Fin 2)} (h : q ≤ p)
    (hq : q ≤ w.length) :
    psign R (p + 2) (ins q a b w) = psign R p w * (-1) ^ (a.val + b.val) := by
  unfold psign
  rw [← pow_add]
  congr 1
  induction q generalizing p w with
  | zero => simp [ins]; omega
  | succ q ih => cases w with
    | nil => simp at hq
    | cons x w =>
      obtain ⟨p, rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      simp only [ins, show p + 1 + 2 = (p + 2) + 1 by omega, List.take_succ_cons, nOdd_cons]
      rw [ih (by omega) (by simp at hq; omega)]; omega

/--
@isnad1 id=eq.1h4v.s5.3647c48ad69f from=translated src=- shape=260e44a2 vocab=16e9e33e
-/
theorem psign_del_le {p q : ℕ} (w : List (Fin 2)) (h : p ≤ q) :
    psign R p (del q w) = psign R p w := by
  unfold psign
  congr 2
  induction q generalizing p w with
  | zero => obtain rfl : p = 0 := by omega
            simp
  | succ q ih => cases p with
    | zero => simp
    | succ p => cases w with
      | nil => simp [del]
      | cons x w => simp only [del, List.take_succ_cons]; rw [ih _ (by omega)]

/--
@isnad1 id=eq.2h4v.s7.4bf1ff4baf9f from=translated src=- shape=3086b222 vocab=343a7914
-/
theorem psign_del_ge {p q : ℕ} {w : List (Fin 2)} (h : p + 2 ≤ q) (hq : q ≤ w.length) :
    psign R q w =
      psign R (q - 2) (del p w) * (-1) ^ ((w.getD p 0).val + (w.getD (p + 1) 0).val) := by
  conv_lhs => rw [← ins_getD_del (p := p) (w := w) (by omega),
    show q = (q - 2) + 2 by omega]
  exact psign_ins_ge _ _ (by omega) (by have := length_del (p := p) (w := w) (by omega); omega)

/-! ## The layer operators -/

variable (R) (q : Rˣ)

/-- Coefficients of the cup vector `v₋₁ ⊗ v₁ - q v₁ ⊗ v₋₁` (letter `0` is `v₁`, letter `1`
is `v₋₁`): `u(1, 0) = 1`, `u(0, 1) = -q`, and `0` otherwise.-/
def cupCoeff : Fin 2 → Fin 2 → R := ![![0, -(q : R)], ![1, 0]]

/-- Coefficients of the cap form: `β(0, 1) = 1` (`v₁ ⊗ v₋₁ ↦ 1`), `β(1, 0) = q⁻¹`
(`v₋₁ ⊗ v₁ ↦ -ε q⁻¹` with `ε = -1`), and `0` otherwise.-/
def capCoeff : Fin 2 → Fin 2 → R := ![![0, 1], ![((q⁻¹ : Rˣ) : R), 0]]

/--
@isnad1 id=eq.0h2v.s6.0fe5dbbb23a2 from=translated src=- shape=6572ee7d vocab=856734f9
-/
@[simp] theorem cupCoeff_00 : cupCoeff R q 0 0 = 0 := rfl
/--
@isnad1 id=eq.0h2v.s6.e62217936d3b from=translated src=- shape=cd7984c3 vocab=64e1aa85
-/
@[simp] theorem cupCoeff_01 : cupCoeff R q 0 1 = -(q : R) := rfl
/--
@isnad1 id=eq.0h2v.s6.552b37edf1ee from=translated src=- shape=6572ee7d vocab=856734f9
-/
@[simp] theorem cupCoeff_10 : cupCoeff R q 1 0 = 1 := rfl
/--
@isnad1 id=eq.0h2v.s6.fea361dd347f from=translated src=- shape=6572ee7d vocab=856734f9
-/
@[simp] theorem cupCoeff_11 : cupCoeff R q 1 1 = 0 := rfl
/--
@isnad1 id=eq.0h2v.s6.376191facbc6 from=translated src=- shape=6572ee7d vocab=81686499
-/
@[simp] theorem capCoeff_00 : capCoeff R q 0 0 = 0 := rfl
/--
@isnad1 id=eq.0h2v.s6.3eb6e12ed7fb from=translated src=- shape=6572ee7d vocab=81686499
-/
@[simp] theorem capCoeff_01 : capCoeff R q 0 1 = 1 := rfl
/--
@isnad1 id=eq.0h2v.s6.8fb999fccf3f from=translated src=- shape=70f4c957 vocab=9d55e4e0
-/
@[simp] theorem capCoeff_10 : capCoeff R q 1 0 = ((q⁻¹ : Rˣ) : R) := rfl
/--
@isnad1 id=eq.0h2v.s6.3cba4f318eca from=translated src=- shape=6572ee7d vocab=81686499
-/
@[simp] theorem capCoeff_11 : capCoeff R q 1 1 = 0 := rfl

/-- The cup and cap coefficients are odd: they vanish unless exactly one letter is `1`.
@isnad1 id=eq.0h4v.s7.cbe3594fcc9c from=translated src=- shape=a9fe03a7 vocab=8f27b8e9
-/
theorem cupCoeff_sign (a b : Fin 2) : (-1 : R) ^ (a.val + b.val) * cupCoeff R q a b =
    -cupCoeff R q a b := by
  fin_cases a <;> fin_cases b <;> simp

/--
@isnad1 id=eq.0h4v.s7.8b05203b18c2 from=translated src=- shape=a9fe03a7 vocab=7e5945c5
-/
theorem capCoeff_sign (a b : Fin 2) : (-1 : R) ^ (a.val + b.val) * capCoeff R q a b =
    -capCoeff R q a b := by
  fin_cases a <;> fin_cases b <;> simp

/-- Functions on words of all lengths.-/
abbrev Fn : Type _ := List (Fin 2) → R

/-- The cup at position `p`, with its Koszul sign:
`(cup F)(w) = psign p w · u(w_p, w_{p+1}) · F(w without w_p, w_{p+1})`.-/
def cupOp (p : ℕ) : Fn R →ₗ[R] Fn R where
  toFun F w := psign R p w * (cupCoeff R q (w.getD p 0) (w.getD (p + 1) 0) * F (del p w))
  map_add' F G := by funext w; simp [mul_add]
  map_smul' r F := by funext w; simp [mul_left_comm]

/-- The cap at position `p`, with its Koszul sign:
`(cap F)(w) = psign p w · Σ_{a b} β(a, b) F(w with a, b inserted at p)`.-/
def capOp (p : ℕ) : Fn R →ₗ[R] Fn R where
  toFun F w := psign R p w * ∑ a : Fin 2, ∑ b : Fin 2, capCoeff R q a b * F (ins p a b w)
  map_add' F G := by funext w; simp [mul_add, Finset.sum_add_distrib]
  map_smul' r F := by
    funext w
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

/--
@isnad1 id=eq.0h5v.s8.871669a883fa from=translated src=- shape=41eaba05 vocab=fc217400
-/
@[simp] theorem cupOp_apply (p : ℕ) (F : Fn R) (w : List (Fin 2)) :
    cupOp R q p F w = psign R p w * (cupCoeff R q (w.getD p 0) (w.getD (p + 1) 0) * F (del p w)) :=
  rfl

/--
@isnad1 id=eq.0h5v.s8.0f872db9aa73 from=translated src=- shape=f4f09242 vocab=a6df0b29
-/
@[simp] theorem capOp_apply (p : ℕ) (F : Fn R) (w : List (Fin 2)) :
    capOp R q p F w = psign R p w * ∑ a : Fin 2, ∑ b : Fin 2, capCoeff R q a b * F (ins p a b w) :=
  rfl

/-- The operator of a layer: a cup or a cap at the position given by its left strands.-/
def op (L : Layer sig) : Fn R →ₗ[R] Fn R :=
  match (L.gen : Gen) with
  | .cup => cupOp R q L.left.length
  | .cap => capOp R q L.left.length

/--
@isnad1 id=eq.0h5v.s7.e690a90028c4 from=translated src=- shape=b320997f vocab=9e632064
-/
@[simp] theorem op_cup (s : Unit) (l r : List Unit) :
    op R q ⟨s, l, .cup, r⟩ = cupOp R q l.length := rfl

/--
@isnad1 id=eq.0h5v.s7.252863f005b3 from=translated src=- shape=b320997f vocab=3e884cb6
-/
@[simp] theorem op_cap (s : Unit) (l r : List Unit) :
    op R q ⟨s, l, .cap, r⟩ = capOp R q l.length := rfl

variable {R q}

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=agree.1h5v.s9.bad8c6296348 from=translated src=- shape=97eb0acd vocab=4d8c9e3e
-/
theorem op_agree (L : Layer sig) {F F' : Fn R} (h : Agree L.dom.word.length F F') :
    Agree L.cod.word.length (op R q L F) (op R q L F') := by
  obtain ⟨s, l, g, r⟩ := L
  intro w hw
  cases g with
  | cup =>
    simp only [Layer.cod_word, List.length_append, sig, List.length_cons, List.length_nil] at hw
    have := length_del (p := l.length) (w := w) (by omega)
    simp only [op, cupOp_apply]
    rw [h _ (by simp [sig]; omega)]
  | cap =>
    simp only [Layer.cod_word, List.length_append, sig, List.length_nil] at hw
    simp only [op, capOp_apply]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [h _ (by simp [sig]; omega)]

/-! ## The interpretation -/

variable (R q)

/-- The representation as an interpretation by local operators on `Fn R`: `n` strands go to
`Word n → R`, included by extension by zero and projected by restriction.-/
def loc : LocalInterpretation sig R (Fn R) (fun n => Word n → R) where
  κ a := a.word.length
  ext := ext R
  res := res R
  op := op R q
  res_comp_ext _ := LinearMap.ext fun f => funext fun w => ext_apply_word R f w
  res_op_ext_res L _ := LinearMap.ext fun _ => funext fun w =>
    op_agree L (fun _ hw => ext_apply_of_length R _ hw) w.1 w.2

/--
@isnad1 id=eq.0h3v.s7.c091c88ba39f from=translated src=- shape=be984950 vocab=1ea5fefa
-/
@[simp] theorem loc_κ (a : Obj sig) : (loc R q).κ a = a.word.length := rfl
/--
@isnad1 id=eq.0h3v.s8.53629d265244 from=translated src=- shape=3c1697c8 vocab=7a57d64f
-/
@[simp] theorem loc_ext (n : ℕ) : (loc R q).ext n = ext R n := rfl
/--
@isnad1 id=eq.0h3v.s8.9c74f0654ffc from=translated src=- shape=706b8ba4 vocab=13500b46
-/
@[simp] theorem loc_res (n : ℕ) : (loc R q).res n = res R n := rfl
/--
@isnad1 id=eq.0h3v.s8.1ddebbf3569d from=translated src=- shape=1714dccc vocab=698f39ed
-/
@[simp] theorem loc_op (L : Layer sig) : (loc R q).op L = op R q L := rfl

/-! ## The relations as identities of operators -/

variable {R q}

/-- The loop relation: `cap_p ∘ cup_p = q⁻¹ - q = -(q - q⁻¹)`.
@isnad1 id=eq.1h5v.s9.03a43aab9f57 from=translated src=- shape=a96d8ec6 vocab=2e5648e5
-/
theorem loop_op {p : ℕ} (F : Fn R) {w : List (Fin 2)} (hp : p ≤ w.length) :
    capOp R q p (cupOp R q p F) w = -((q : R) - ((q⁻¹ : Rˣ) : R)) * F w := by
  simp only [capOp_apply, cupOp_apply, getD_ins_self _ _ _ hp, getD_ins_succ _ _ _ hp,
    del_ins _ _ _ hp, psign_ins_le _ _ (le_refl p) hp, Fin.sum_univ_two]
  have := psign_mul_self (R := R) p w
  simp only [cupCoeff_00, cupCoeff_01, cupCoeff_10, cupCoeff_11, capCoeff_00, capCoeff_01,
    capCoeff_10, capCoeff_11]
  linear_combination (-(q : R) * F w + ((q⁻¹ : Rˣ) : R) * F w) * this

/-- The zigzag relation `cap_p ∘ cup_{p+1} = 1`.
@isnad1 id=eq.1h5v.s9.4b5bf95458e7 from=translated src=- shape=2c1fdb67 vocab=e5bc6d74
-/
theorem zigzagA_op {p : ℕ} (F : Fn R) {w : List (Fin 2)} (hp : p < w.length) :
    capOp R q p (cupOp R q (p + 1) F) w = F w := by
  have e : F w = F (w.set p (w.getD p 0)) := by rw [set_getD_self hp]
  have hs : ∀ a b : Fin 2, psign R (p + 1) (ins p a b w) = psign R p w * (-1) ^ a.val := by
    intro a b
    rw [psign, psign, ← pow_add]
    congr 1
    clear e
    induction p generalizing w with
    | zero => simp [ins]
    | succ p ih => cases w with
      | nil => simp at hp
      | cons x w =>
        simp only [ins, List.take_succ_cons, nOdd_cons]
        rw [ih (by simp at hp; omega)]; omega
  simp only [capOp_apply, cupOp_apply, getD_ins_succ _ _ _ hp.le, hs,
    show p + 1 + 1 = p + 2 from rfl, getD_ins_ge _ _ le_rfl hp.le, del_succ_ins _ _ hp, e]
  have h1 := psign_mul_self (R := R) p w
  have h2 := Units.inv_mul q
  generalize w.getD p 0 = c
  fin_cases c
  · simp [Fin.sum_univ_two]
    linear_combination (F (w.set p 0)) * h1
  · simp [Fin.sum_univ_two]
    linear_combination (psign R p w * psign R p w * F (w.set p 1)) * h2 +
      F (w.set p 1) * h1

/--
@isnad1 id=eq.1h3v.s7.3777ba8c5aa3 from=translated src=- shape=4db8285f vocab=940528bb
-/
theorem psign_succ {p : ℕ} {w : List (Fin 2)} (hp : p < w.length) :
    psign R (p + 1) w = psign R p w * (-1) ^ (w.getD p 0).val := by
  rw [psign, psign, ← pow_add]
  congr 1
  induction p generalizing w with
  | zero => cases w with
    | nil => simp at hp
    | cons x w => simp
  | succ p ih => cases w with
    | nil => simp at hp
    | cons x w =>
      simp only [List.take_succ_cons, nOdd_cons, List.getD_cons_succ]
      rw [ih (by simp at hp; omega)]; omega

/-- The zigzag relation `cap_{p+1} ∘ cup_p = ε = -1`.
@isnad1 id=eq.1h5v.s9.86c0ef6f6bc6 from=translated src=- shape=1b0ed3a1 vocab=c259dbbd
-/
theorem zigzagB_op {p : ℕ} (F : Fn R) {w : List (Fin 2)} (hp : p < w.length) :
    capOp R q (p + 1) (cupOp R q p F) w = -F w := by
  have e : F w = F (w.set p (w.getD p 0)) := by rw [set_getD_self hp]
  simp only [capOp_apply, cupOp_apply, getD_ins_lt _ _ (Nat.lt_succ_self p) hp,
    getD_ins_self _ _ _ hp, del_ins_succ _ _ hp, psign_ins_le _ _ (Nat.le_succ p) hp,
    psign_succ hp, e]
  have h1 := psign_mul_self (R := R) p w
  have h2 := Units.inv_mul q
  generalize w.getD p 0 = c
  fin_cases c
  · simp [Fin.sum_univ_two]
    linear_combination (psign R p w * psign R p w * F (w.set p 0)) * h2 +
      F (w.set p 0) * h1
  · simp [Fin.sum_univ_two]
    linear_combination (F (w.set p 1)) * h1

/-- Interchange of two cups, with the Koszul sign `-1`.
@isnad1 id=eq.1h6v.s10.f442f7fee21b from=translated src=- shape=1f87008b vocab=3d5f6619
-/
theorem cup_cup_op {p k : ℕ} (F : Fn R) {w : List (Fin 2)} (h : p + k + 4 ≤ w.length) :
    cupOp R q (p + 2 + k) (cupOp R q p F) w = -cupOp R q p (cupOp R q (p + k) F) w := by
  simp only [cupOp_apply]
  rw [getD_del_lt (show p < p + 2 + k by omega) (by omega),
    getD_del_lt (show p + 1 < p + 2 + k by omega) (by omega),
    getD_del_ge (show p ≤ p + k by omega), getD_del_ge (show p ≤ p + k + 1 by omega),
    show p + k + 2 = p + 2 + k by omega, show p + k + 1 + 2 = p + 2 + k + 1 by omega, del_del h,
    psign_del_le _ (show p ≤ p + 2 + k by omega),
    psign_del_ge (p := p) (q := p + 2 + k) (by omega) (by omega),
    show p + 2 + k - 2 = p + k by omega]
  have := cupCoeff_sign R q (w.getD p 0) (w.getD (p + 1) 0)
  linear_combination (psign R (p + k) (del p w) *
    cupCoeff R q (w.getD (p + 2 + k) 0) (w.getD (p + 2 + k + 1) 0) * psign R p w *
    F (del (p + k) (del p w))) * this

/-- Interchange of two caps, with the Koszul sign `-1`.
@isnad1 id=eq.1h6v.s10.60f73957f656 from=translated src=- shape=e59fd1c9 vocab=530045be
-/
theorem cap_cap_op {p k : ℕ} (F : Fn R) {w : List (Fin 2)} (h : p + k ≤ w.length) :
    capOp R q (p + k) (capOp R q p F) w = -capOp R q p (capOp R q (p + 2 + k) F) w := by
  simp only [capOp_apply, ins_ins _ _ _ _ h]
  simp only [psign_ins_le (w := w) _ _ (show p ≤ p + k by omega) h,
    show p + 2 + k = p + k + 2 by omega,
    psign_ins_ge (w := w) _ _ (show p ≤ p + k by omega) (show p ≤ w.length by omega)]
  simp [Fin.sum_univ_two]
  ring

/-- Interchange of a cup (on the left) and a cap (on the right), with the Koszul sign `-1`.
@isnad1 id=eq.1h6v.s10.e9cd7a3d0fbe from=translated src=- shape=098c7185 vocab=1c0cb2ac
-/
theorem cup_cap_op {p k : ℕ} (F : Fn R) {w : List (Fin 2)} (h : p + 2 + k ≤ w.length) :
    capOp R q (p + 2 + k) (cupOp R q p F) w = -cupOp R q p (capOp R q (p + k) F) w := by
  simp only [capOp_apply, cupOp_apply, del_ins_far' _ _ h,
    getD_ins_lt _ _ (show p < p + 2 + k by omega) h,
    getD_ins_lt _ _ (show p + 1 < p + 2 + k by omega) h,
    psign_ins_le (w := w) _ _ (show p ≤ p + 2 + k by omega) h,
    psign_del_ge (p := p) (q := p + 2 + k) (w := w) (by omega) h,
    show p + 2 + k - 2 = p + k by omega]
  generalize w.getD p 0 = a
  generalize w.getD (p + 1) 0 = b
  fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_two] <;> ring

/-- Interchange of a cap (on the left) and a cup (on the right), with the Koszul sign `-1`.
@isnad1 id=eq.1h6v.s10.bd25529f02ee from=translated src=- shape=b4e0b06c vocab=1c0cb2ac
-/
theorem cap_cup_op {p k : ℕ} (F : Fn R) {w : List (Fin 2)} (h : p + k + 2 ≤ w.length) :
    cupOp R q (p + k) (capOp R q p F) w = -capOp R q p (cupOp R q (p + 2 + k) F) w := by
  simp only [cupOp_apply, capOp_apply, del_ins_far _ _ h,
    psign_del_le (R := R) w (show p ≤ p + k by omega)]
  simp only [show p + 2 + k = (p + k) + 2 by omega,
    getD_ins_ge _ _ (show p ≤ p + k by omega) (show p ≤ w.length by omega),
    getD_ins_ge _ _ (show p ≤ p + k + 1 by omega) (show p ≤ w.length by omega),
    psign_ins_ge (w := w) _ _ (show p ≤ p + k by omega) (show p ≤ w.length by omega)]
  generalize w.getD (p + k) 0 = a
  generalize w.getD (p + k + 1) 0 = b
  fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_two] <;> ring

/-! ## Soundness -/

/-- The loop value of the representation.-/
abbrev delta (q : Rˣ) : R := -((q : R) - ((q⁻¹ : Rˣ) : R))

variable (R q)

variable {R q}

/-- The basis vector `v_w = v_{w₁} ⊗ ⋯ ⊗ v_{wₙ}` of `V^{⊗n}`, as a function on words.-/
def vec {n : ℕ} (w : Word n) : Word n → R := fun t => if t = w then 1 else 0

end StringDiagrams.OddTemperleyLieb.Rep

end
