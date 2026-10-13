/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Tengoku

/-!
# The arithmetic a certificate for `CODEHALT` has to speak

Everything the `∃SO[new]` certificate of `DescriptiveComplexity.CODEHALT` needs
to know about `Nat.Partrec.Code`, stated over `ℕ` alone – no logic, no
structures. Three groups:

* **codes are numbers.** `DescriptiveComplexity.CodeHalt.dec` decodes a number
  into a code, and the four `dec_pair`/`dec_comp`/`dec_prec`/`dec_rfind`
  lemmas read the shape of a code off the arithmetic of its number: a `pair` is
  a `4 * ⟨e₁, e₂⟩ + 4`, a `prec` a `+ 5`, a `comp` a `+ 6`, an `rfind'` a
  `4 * e + 7`. This is what lets the certificate carry codes as *numerals*
  rather than as nodes of the instance, and it is what makes decoding
  unambiguous without asking the instance to be well-formed.
* **`Nat.pair` has a successor rule.**
  `DescriptiveComplexity.CodeHalt.NextP` names the four ways the pair
  enumerated next after `⟨a, b⟩` arises, and
  `DescriptiveComplexity.CodeHalt.pair_next` /
  `DescriptiveComplexity.CodeHalt.exists_next` make it a recurrence. A guessed
  pairing relation checked against that recurrence *is* `Nat.pair`, which is
  much cheaper than guessing addition and multiplication and building the
  closed form out of them.
* **bounded evaluation unfolds.** One `mem_evaln_*_iff` per constructor, plus
  `DescriptiveComplexity.CodeHalt.evaln_rfind'_spec`, which turns the
  step-by-step search of `evaln` on an `rfind'` into the *bounded universal*
  statement a first-order kernel can make: the answer is a place where the
  argument returns `0` and every earlier place returns something nonzero.
  Finally `DescriptiveComplexity.CodeHalt.valBound` bounds every value a
  bounded evaluation can produce, which is what makes the numeral segment of a
  certificate finite.
-/

namespace DescriptiveComplexity

namespace CodeHalt

open Nat.Partrec.Code

/-! ### Codes as numbers -/

/-- The code a number denotes. -/
def dec (e : ℕ) : Nat.Partrec.Code := Denumerable.ofNat Nat.Partrec.Code e

/--
@isnad1 id=eq.0h1v.s3.a16de2bf8256 from=translated src=- shape=47dcad53 vocab=69bcee36
-/
@[simp]
theorem dec_encodeCode (c : Nat.Partrec.Code) : dec (encodeCode c) = c := by
  rw [dec, ← encodeCode_eq]
  exact Denumerable.ofNat_encode c

/--
@isnad1 id=eq.0h1v.s3.fe4a72d40a6a from=translated src=- shape=47dcad53 vocab=74fc2b36
-/
@[simp]
theorem encodeCode_dec (e : ℕ) : encodeCode (dec e) = e := by
  rw [dec, ← encodeCode_eq]
  exact Denumerable.encode_ofNat e

/--
@isnad1 id=eq.0h2v.s5.b135f9b79feb from=translated src=- shape=e04ad34c vocab=91a53dbe
-/
theorem encodeCode_pair (cf cg : Nat.Partrec.Code) :
    encodeCode (.pair cf cg) = 4 * Nat.pair (encodeCode cf) (encodeCode cg) + 4 := by
  simp only [encodeCode]
  omega

/--
@isnad1 id=eq.0h2v.s5.1cf96066b7ea from=translated src=- shape=e04ad34c vocab=efc685c9
-/
theorem encodeCode_comp (cf cg : Nat.Partrec.Code) :
    encodeCode (.comp cf cg) = 4 * Nat.pair (encodeCode cf) (encodeCode cg) + 6 := by
  simp only [encodeCode]
  omega

/--
@isnad1 id=eq.0h2v.s5.47392c3349cf from=translated src=- shape=e04ad34c vocab=9869413b
-/
theorem encodeCode_prec (cf cg : Nat.Partrec.Code) :
    encodeCode (.prec cf cg) = 4 * Nat.pair (encodeCode cf) (encodeCode cg) + 5 := by
  simp only [encodeCode]
  omega

/--
@isnad1 id=eq.0h1v.s5.d12af6030232 from=translated src=- shape=e34eb7e3 vocab=1ad69bfd
-/
theorem encodeCode_rfind' (cf : Nat.Partrec.Code) :
    encodeCode (.rfind' cf) = 4 * encodeCode cf + 7 := by
  simp only [encodeCode]
  omega

/--
@isnad1 id=eq.0h0v.s3.c5edbc13db36 from=translated src=- shape=d3a93718 vocab=00a17237
-/
@[simp] theorem dec_zero : dec 0 = .zero := dec_encodeCode .zero
/--
@isnad1 id=eq.0h0v.s3.b450d75cc4b9 from=translated src=- shape=d3a93718 vocab=818ee52a
-/
@[simp] theorem dec_one : dec 1 = .succ := dec_encodeCode .succ
/--
@isnad1 id=eq.0h0v.s3.542cdbc04285 from=translated src=- shape=d3a93718 vocab=dea0f749
-/
@[simp] theorem dec_two : dec 2 = .left := dec_encodeCode .left
/--
@isnad1 id=eq.0h0v.s3.680c7e6b092f from=translated src=- shape=d3a93718 vocab=d2d26a19
-/
@[simp] theorem dec_three : dec 3 = .right := dec_encodeCode .right

/--
@isnad1 id=eq.0h2v.s5.e563b55a0384 from=translated src=- shape=04dcf07b vocab=f8a004f9
-/
theorem dec_pair (a b : ℕ) : dec (4 * Nat.pair a b + 4) = .pair (dec a) (dec b) := by
  conv_lhs =>
    rw [show 4 * Nat.pair a b + 4 = encodeCode (.pair (dec a) (dec b)) by
      rw [encodeCode_pair, encodeCode_dec, encodeCode_dec]]
  exact dec_encodeCode _

/--
@isnad1 id=eq.0h2v.s5.7f056ffe9a87 from=translated src=- shape=04dcf07b vocab=0303f3b1
-/
theorem dec_comp (a b : ℕ) : dec (4 * Nat.pair a b + 6) = .comp (dec a) (dec b) := by
  conv_lhs =>
    rw [show 4 * Nat.pair a b + 6 = encodeCode (.comp (dec a) (dec b)) by
      rw [encodeCode_comp, encodeCode_dec, encodeCode_dec]]
  exact dec_encodeCode _

/--
@isnad1 id=eq.0h2v.s5.8e1f05915f5d from=translated src=- shape=04dcf07b vocab=634f7773
-/
theorem dec_prec (a b : ℕ) : dec (4 * Nat.pair a b + 5) = .prec (dec a) (dec b) := by
  conv_lhs =>
    rw [show 4 * Nat.pair a b + 5 = encodeCode (.prec (dec a) (dec b)) by
      rw [encodeCode_prec, encodeCode_dec, encodeCode_dec]]
  exact dec_encodeCode _

/--
@isnad1 id=eq.0h1v.s5.c11cd695ca70 from=translated src=- shape=f53f1fde vocab=7ab0c907
-/
theorem dec_rfind (a : ℕ) : dec (4 * a + 7) = .rfind' (dec a) := by
  conv_lhs =>
    rw [show 4 * a + 7 = encodeCode (.rfind' (dec a)) by
      rw [encodeCode_rfind', encodeCode_dec]]
  exact dec_encodeCode _

/-- The number of a proper subcode is smaller: this is the well-founded measure
the soundness of a certificate runs on.
@isnad1 id=and.0h2v.s6.603d1c6143bc from=translated src=- shape=d9bcc776 vocab=ef2ed37c
-/
theorem lt_of_pair_encode (a b : ℕ) : a < 4 * Nat.pair a b + 4 ∧ b < 4 * Nat.pair a b + 4 := by
  have h1 := Nat.left_le_pair a b
  have h2 := Nat.right_le_pair a b
  omega

/-! ### The successor rule of `Nat.pair` -/

/-- **`(a, b)` is the pair enumerated just after `(a', b')`.** The four cases
are: move up inside a shell, close a shell, move along a shell, and open the
next one. -/
def NextP (a' b' a b : ℕ) : Prop :=
  (a' < b' ∧ a = a' + 1 ∧ a < b' ∧ b = b') ∨
    (b' = a' + 1 ∧ a = b' ∧ b = 0) ∨
      (b' ≤ a' ∧ b = b' + 1 ∧ b ≤ a' ∧ a = a') ∨
        (a' = b' ∧ a = 0 ∧ b = b' + 1)

/--
@isnad1 id=eq.1h4v.s5.73c87cb41138 from=translated src=- shape=65b99e0e vocab=7510fbad
-/
theorem pair_next {a' b' a b : ℕ} (h : NextP a' b' a b) :
    Nat.pair a b = Nat.pair a' b' + 1 := by
  rcases h with ⟨hlt, rfl, hab, rfl⟩ | ⟨hb, rfl, rfl⟩ | ⟨hba, rfl, hb, rfl⟩ | ⟨hab, rfl, rfl⟩
  · rw [Nat.pair, Nat.pair, ite_eq_left hab, ite_eq_left hlt]
    omega
  · rw [Nat.pair, Nat.pair, ite_eq_right (by omega), ite_eq_left (by omega)]
    omega
  · rw [Nat.pair, Nat.pair, ite_eq_right (by omega), ite_eq_right (by omega)]
    omega
  · subst hab
    rw [Nat.pair, Nat.pair, ite_eq_left (by omega), ite_eq_right (by omega)]
    ring

/--
@isnad1 id=ex.0h2v.s4.8dae71771fa0 from=translated src=- shape=e449df73 vocab=40ba81b3
-/
theorem exists_next (a' b' : ℕ) : ∃ a b, NextP a' b' a b := by
  rcases Nat.lt_or_ge a' b' with h | h
  · rcases Nat.lt_or_ge (a' + 1) b' with h' | h'
    · exact ⟨a' + 1, b', Or.inl ⟨h, rfl, h', rfl⟩⟩
    · exact ⟨b', 0, Or.inr (Or.inl ⟨by omega, rfl, rfl⟩)⟩
  · rcases Nat.lt_or_ge b' a' with h' | h'
    · exact ⟨a', b' + 1, Or.inr (Or.inr (Or.inl ⟨h, rfl, by omega, rfl⟩))⟩
    · exact ⟨0, b' + 1, Or.inr (Or.inr (Or.inr ⟨by omega, rfl, rfl⟩))⟩

/--
@isnad1 id=and.1h2v.s5.4401e04311ff from=translated src=- shape=1ffb72a7 vocab=23744838
-/
theorem pair_eq_zero {a b : ℕ} (h : Nat.pair a b = 0) : a = 0 ∧ b = 0 := by
  have h0 : Nat.pair 0 0 = 0 := by simp [Nat.pair]
  exact Nat.pair_eq_pair.mp (h.trans h0.symm)

/-- The predecessor of a nonzero pair, together with the step relating them:
the completeness half of the recurrence.
@isnad1 id=ex.1h2v.s5.4d4d256749c8 from=translated src=- shape=a5f7296d vocab=7510fbad
-/
theorem exists_pred_pair {a b : ℕ} (h : Nat.pair a b ≠ 0) :
    ∃ a' b', Nat.pair a' b' + 1 = Nat.pair a b ∧ NextP a' b' a b := by
  set a' := (Nat.unpair (Nat.pair a b - 1)).1 with ha'
  set b' := (Nat.unpair (Nat.pair a b - 1)).2 with hb'
  have hp : Nat.pair a' b' = Nat.pair a b - 1 := Nat.pair_unpair _
  obtain ⟨a₁, b₁, hstep⟩ := exists_next a' b'
  have hnext := pair_next hstep
  have hab : Nat.pair a₁ b₁ = Nat.pair a b := by omega
  obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp hab
  exact ⟨a', b', by omega, hstep⟩

/-! ### Unfolding bounded evaluation -/

section Evaln

variable {k n v : ℕ} {cf cg : Nat.Partrec.Code}

/--
@isnad1 id=iff.0h3v.s5.45807f1a8cc7 from=translated src=- shape=89351c21 vocab=472774b3
-/
theorem mem_evaln_zero_iff : v ∈ evaln (k + 1) .zero n ↔ n ≤ k ∧ v = 0 := by
  by_cases h : n ≤ k <;> simp [evaln, guard, h, eq_comm]

/--
@isnad1 id=iff.0h3v.s5.0798e9160e6f from=translated src=- shape=d5c3d619 vocab=c432b538
-/
theorem mem_evaln_succ_iff : v ∈ evaln (k + 1) .succ n ↔ n ≤ k ∧ v = n + 1 := by
  by_cases h : n ≤ k <;> simp [evaln, guard, h, eq_comm]

/--
@isnad1 id=iff.0h3v.s5.218ce3782778 from=translated src=- shape=6e82a7f8 vocab=d14dc4ee
-/
theorem mem_evaln_left_iff : v ∈ evaln (k + 1) .left n ↔ n ≤ k ∧ v = (Nat.unpair n).1 := by
  by_cases h : n ≤ k <;> simp [evaln, guard, h, eq_comm]

/--
@isnad1 id=iff.0h3v.s5.840127a97d4a from=translated src=- shape=6e82a7f8 vocab=bb0c4dab
-/
theorem mem_evaln_right_iff : v ∈ evaln (k + 1) .right n ↔ n ≤ k ∧ v = (Nat.unpair n).2 := by
  by_cases h : n ≤ k <;> simp [evaln, guard, h, eq_comm]

/--
@isnad1 id=iff.0h5v.s6.712a05068b42 from=translated src=- shape=76f98648 vocab=8c758795
-/
theorem mem_evaln_pair_iff :
    v ∈ evaln (k + 1) (.pair cf cg) n ↔
      n ≤ k ∧ ∃ x y, x ∈ evaln (k + 1) cf n ∧ y ∈ evaln (k + 1) cg n ∧ Nat.pair x y = v := by
  by_cases h : n ≤ k <;>
    simp [evaln, guard, h, Seq.seq, Option.bind_eq_some_iff, Option.map_eq_some_iff]

/--
@isnad1 id=iff.0h5v.s6.bfc23ba07bbb from=translated src=- shape=2a21729a vocab=f75dcd50
-/
theorem mem_evaln_comp_iff :
    v ∈ evaln (k + 1) (.comp cf cg) n ↔
      n ≤ k ∧ ∃ y, y ∈ evaln (k + 1) cg n ∧ v ∈ evaln (k + 1) cf y := by
  by_cases h : n ≤ k <;> simp [evaln, guard, h, Option.bind_eq_some_iff]

/--
@isnad1 id=iff.0h5v.s6.5bfb94ccfca4 from=translated src=- shape=7eb5ccc6 vocab=e78ca923
-/
theorem mem_evaln_prec_zero_iff {a : ℕ} :
    v ∈ evaln (k + 1) (.prec cf cg) (Nat.pair a 0) ↔
      Nat.pair a 0 ≤ k ∧ v ∈ evaln (k + 1) cf a := by
  by_cases h : Nat.pair a 0 ≤ k <;> simp [evaln, guard, h, Nat.unpaired]

/--
@isnad1 id=iff.0h6v.s6.1e45bb43e312 from=translated src=- shape=4b0a5ba8 vocab=e78ca923
-/
theorem mem_evaln_prec_succ_iff {a j : ℕ} :
    v ∈ evaln (k + 1) (.prec cf cg) (Nat.pair a (j + 1)) ↔
      Nat.pair a (j + 1) ≤ k ∧ ∃ i, i ∈ evaln k (.prec cf cg) (Nat.pair a j) ∧
        v ∈ evaln (k + 1) cg (Nat.pair a (Nat.pair j i)) := by
  by_cases h : Nat.pair a (j + 1) ≤ k <;>
    simp [evaln, guard, h, Nat.unpaired, Option.bind_eq_some_iff]

/--
@isnad1 id=iff.0h5v.s6.e9ae6886d909 from=translated src=- shape=78b9f6d4 vocab=43e0bc40
-/
theorem mem_evaln_rfind'_iff {a m : ℕ} :
    v ∈ evaln (k + 1) (.rfind' cf) (Nat.pair a m) ↔
      Nat.pair a m ≤ k ∧ ∃ x, x ∈ evaln (k + 1) cf (Nat.pair a m) ∧
        (if x = 0 then v = m else v ∈ evaln k (.rfind' cf) (Nat.pair a (m + 1))) := by
  by_cases h : Nat.pair a m ≤ k
  · simp only [Option.mem_def, h, true_and]
    simp only [evaln, guard, ite_eq_left h, Nat.unpaired, Nat.unpair_pair, bind, pure,
      Option.bind_eq_some_iff, true_and, exists_const]
    refine exists_congr fun x => and_congr_right fun _ => ?_
    by_cases hx : x = 0 <;> simp [hx, eq_comm]
  · simp [evaln, guard, h, Nat.unpaired]

/-- **The search an `rfind'` performs, read as a bounded universal statement.**
A bounded evaluation of `rfind' cf` on `⟨a, m⟩` returns some `v ≥ m` such that
`cf` returns `0` at `⟨a, v⟩` and something nonzero at every `⟨a, w⟩` with
`m ≤ w < v` – and all of that within the *same* budget, which is what lets a
first-order kernel state the search without a chain.
@isnad1 id=and.1h5v.s6.7d744b53d12f from=translated src=- shape=f1183a2a vocab=29568821
-/
theorem evaln_rfind'_spec :
    ∀ (k : ℕ) {cf : Nat.Partrec.Code} {a m v : ℕ}, v ∈ evaln k (.rfind' cf) (Nat.pair a m) →
      m ≤ v ∧ 0 ∈ evaln k cf (Nat.pair a v) ∧
        ∀ w, m ≤ w → w < v → ∃ u, u ≠ 0 ∧ u ∈ evaln k cf (Nat.pair a w) := by
  intro k
  induction k with
  | zero => intro cf a m v h; simp [evaln] at h
  | succ k ih =>
    intro cf a m v h
    obtain ⟨-, x, hx, hv⟩ := mem_evaln_rfind'_iff.mp h
    by_cases hx0 : x = 0
    · subst hx0
      simp only [reduceIte] at hv
      subst hv
      exact ⟨le_rfl, hx, fun w hw hlt => absurd hlt (by omega)⟩
    · simp only [hx0, reduceIte] at hv
      obtain ⟨hle, hz, hall⟩ := ih hv
      refine ⟨by omega, evaln_mono (Nat.le_succ _) hz, fun w hw hlt => ?_⟩
      rcases Nat.eq_or_lt_of_le hw with rfl | hw'
      · exact ⟨x, hx0, hx⟩
      · obtain ⟨u, hu0, hu⟩ := hall w (by omega) hlt
        exact ⟨u, hu0, evaln_mono (Nat.le_succ _) hu⟩

end Evaln

/-! ### Introduction rules for evaluation

One per constructor: what has to hold of the arguments for a value to be in the
evaluation of a code. They are what the soundness of a certificate discharges
its case analysis with. -/

section EvalIntro

variable {cf cg : Nat.Partrec.Code} {n : ℕ}

/--
@isnad1 id=mem.0h1v.s4.810406a646d0 from=translated src=- shape=2faed2b5 vocab=eb82976b
-/
theorem mem_eval_zero : (0 : ℕ) ∈ eval .zero n := by
  rw [eval]; exact Part.mem_some 0

/--
@isnad1 id=mem.0h1v.s4.75ed5ff4aaad from=translated src=- shape=7fa56529 vocab=a09a1e16
-/
theorem mem_eval_succ : n + 1 ∈ eval .succ n := by
  rw [eval]; exact Part.mem_some _

/--
@isnad1 id=mem.0h1v.s4.a01871f63da5 from=translated src=- shape=01fd2add vocab=0f80891b
-/
theorem mem_eval_left : (Nat.unpair n).1 ∈ eval .left n := by
  rw [eval]; exact Part.mem_some _

/--
@isnad1 id=mem.0h1v.s4.248b0387822c from=translated src=- shape=01fd2add vocab=57c8af04
-/
theorem mem_eval_right : (Nat.unpair n).2 ∈ eval .right n := by
  rw [eval]; exact Part.mem_some _

/--
@isnad1 id=mem.2h5v.s5.cbd30d9c96ff from=translated src=- shape=71c3a596 vocab=6b011c65
-/
theorem mem_eval_pair {a b : ℕ} (ha : a ∈ eval cf n) (hb : b ∈ eval cg n) :
    Nat.pair a b ∈ eval (.pair cf cg) n := by
  change Nat.pair a b ∈ (Nat.pair <$> eval cf n <*> eval cg n)
  rw [seq_eq_bind_map]
  exact Part.mem_bind (Part.mem_map _ ha) (Part.mem_map _ hb)

/--
@isnad1 id=mem.2h5v.s5.29d81551b205 from=translated src=- shape=f854bbd1 vocab=620ffed0
-/
theorem mem_eval_comp {y v : ℕ} (hy : y ∈ eval cg n) (hv : v ∈ eval cf y) :
    v ∈ eval (.comp cf cg) n := by
  rw [eval]; exact Part.mem_bind hy hv

/--
@isnad1 id=mem.1h4v.s5.be623fb563a9 from=translated src=- shape=a7ee008f vocab=ef2b742c
-/
theorem mem_eval_prec_zero {a v : ℕ} (h : v ∈ eval cf a) :
    v ∈ eval (.prec cf cg) (Nat.pair a 0) := by
  rw [eval_prec_zero]; exact h

/--
@isnad1 id=mem.2h6v.s6.89354abd6089 from=translated src=- shape=e81ee9d4 vocab=561d9be8
-/
theorem mem_eval_prec_succ {a j i v : ℕ} (hi : i ∈ eval (.prec cf cg) (Nat.pair a j))
    (hv : v ∈ eval cg (Nat.pair a (Nat.pair j i))) :
    v ∈ eval (.prec cf cg) (Nat.pair a (j + 1)) := by
  rw [eval_prec_succ]; exact Part.mem_bind hi hv

/-- The evaluation of an `rfind'`, from the *bounded universal* shape of the
search: `v` is a place at or above `m` where `cf` returns `0`, and every place
in between returns something nonzero.
@isnad1 id=mem.3h4v.s6.1e141ee22c22 from=translated src=- shape=4abaea66 vocab=a47ebedf
-/
theorem mem_eval_rfind' {a m v : ℕ} (hmv : m ≤ v) (h0 : 0 ∈ eval cf (Nat.pair a v))
    (hlt : ∀ w, m ≤ w → w < v → ∃ u, u ≠ 0 ∧ u ∈ eval cf (Nat.pair a w)) :
    v ∈ eval (.rfind' cf) (Nat.pair a m) := by
  change v ∈ (Nat.unpaired fun a m =>
    (Nat.rfind fun n => (fun m => m = 0) <$> eval cf (Nat.pair a (n + m))).map (· + m))
      (Nat.pair a m)
  simp only [Nat.unpaired, Nat.unpair_pair]
  refine (Part.mem_map_iff _).mpr ⟨v - m, Nat.mem_rfind.mpr ⟨?_, ?_⟩, by omega⟩
  · refine (Part.mem_map_iff _).mpr ⟨0, ?_, rfl⟩
    rw [show v - m + m = v by omega]
    exact h0
  · intro i hi
    obtain ⟨u, hu0, hu⟩ := hlt (i + m) (by omega) (by omega)
    exact (Part.mem_map_iff _).mpr ⟨u, hu, by simp [hu0]⟩

end EvalIntro

/-! ### A bound on the values a bounded evaluation produces -/

/-- Every value a bounded evaluation with budget `k` of a code numbered at most
`E` can produce. The numeral segment of a certificate is an initial segment of
`ℕ` reaching this far, which is what makes it finite. -/
def valBound (E k : ℕ) : ℕ :=
  (Finset.range (E + 1)).sup fun e =>
    (Finset.range (k + 1)).sup fun x => (evaln k (dec e) x).getD 0

/--
@isnad1 id=le.2h5v.s5.875b068275bd from=translated src=- shape=5ce0e705 vocab=0099ec55
-/
theorem le_valBound {E k e x v : ℕ} (he : e ≤ E) (hv : v ∈ evaln k (dec e) x) :
    v ≤ valBound E k := by
  have hx : x < k := evaln_bound hv
  have hinner : v ≤ (Finset.range (k + 1)).sup fun x => (evaln k (dec e) x).getD 0 := by
    have := Finset.le_sup (f := fun x => (evaln k (dec e) x).getD 0)
      (Finset.mem_range.mpr (by omega : x < k + 1))
    rwa [show (evaln k (dec e) x).getD 0 = v from by rw [Option.mem_def.mp hv]; rfl] at this
  exact hinner.trans
    (Finset.le_sup (f := fun e => (Finset.range (k + 1)).sup fun x => (evaln k (dec e) x).getD 0)
      (Finset.mem_range.mpr (by omega : e < E + 1)))

end CodeHalt

end DescriptiveComplexity
