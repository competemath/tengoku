module

public import Tengoku.TheoremAFpGroups.RequestProject.TheoremA.RelPres.Class

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Program codes for computations relative to the oracle `χ_R`

* `OracleCode` — finite program syntax, one constructor per constructor of Mathlib's
  `RecursiveIn`; the constructor `query` denotes the fixed oracle `chi R` and carries no data.
* `OracleCode.eval R c : ℕ →. ℕ` — partial evaluation, using literally the same pairing,
  primitive-recursion and minimization expressions as the constructors of `RecursiveIn`.
* `OracleCode.eval_recursive` and `OracleCode.exists_code` — the evaluated functions are
  exactly the functions recursive in `oracle R`.
* `OracleCode.encode` / `OracleCode.decode` — an explicit bijective numbering
  (`0,…,4` for the atoms, `4·⟨f,g⟩+5`, `4·⟨f,g⟩+6`, `4·⟨f,g⟩+7` for `pair`, `comp`, `prec`,
  and `4·f+8` for `rfind`), with both round-trip lemmas, and the primitive recursive
  constructor inspection functions `codeTag`, `codeArg`.
-/

@[expose] public section

namespace TheoremA.RelPres

/-- Finite program syntax for functions recursive in the fixed oracle `χ_R`.-/
inductive OracleCode : Type
  | zero : OracleCode
  | succ : OracleCode
  | left : OracleCode
  | right : OracleCode
  | query : OracleCode
  | pair : OracleCode → OracleCode → OracleCode
  | comp : OracleCode → OracleCode → OracleCode
  | prec : OracleCode → OracleCode → OracleCode
  | rfind : OracleCode → OracleCode
  deriving DecidableEq, Inhabited

namespace OracleCode

/-- Partial evaluation relative to `χ_R`; each clause is the corresponding `RecursiveIn`
constructor's function.  `comp f g` computes `f ∘ g`.-/
noncomputable def eval (R : Set ℕ) : OracleCode → ℕ →. ℕ
  | zero => fun _ => 0
  | succ => Nat.succ
  | left => fun n => (Nat.unpair n).1
  | right => fun n => (Nat.unpair n).2
  | query => chi R
  | pair f g => fun n => (Nat.pair <$> eval R f n <*> eval R g n)
  | comp f g => fun n => eval R g n >>= eval R f
  | prec f g => fun p =>
      let (a, n) := Nat.unpair p
      n.rec (eval R f a) fun y IH => do
        let i ← IH
        eval R g (Nat.pair a (Nat.pair y i))
  | rfind f => fun a =>
      Nat.rfind fun n => (fun m => m = 0) <$> eval R f (Nat.pair a n)

variable {R : Set ℕ}

/-- Every program evaluates to a function recursive in `oracle R`.-/
theorem eval_recursive (c : OracleCode) : RecursiveIn (oracle R) (eval R c) := by
  induction c with
  | zero => exact RecursiveIn.zero
  | succ => exact RecursiveIn.succ
  | left => exact RecursiveIn.left
  | right => exact RecursiveIn.right
  | query => exact RecursiveIn.oracle _ rfl
  | pair f g ihf ihg => exact RecursiveIn.pair ihf ihg
  | comp f g ihf ihg => exact RecursiveIn.comp ihf ihg
  | prec f g ihf ihg => exact RecursiveIn.prec ihf ihg
  | rfind f ihf => exact RecursiveIn.rfind ihf

/-- Every function recursive in `oracle R` is computed by some program.  Proved by induction
on the `RecursiveIn` derivation with an existential motive.-/
theorem exists_code {f : ℕ →. ℕ} (hf : RecursiveIn (oracle R) f) : ∃ c, eval R c = f := by
  induction hf with
  | zero => exact ⟨zero, rfl⟩
  | succ => exact ⟨succ, rfl⟩
  | left => exact ⟨left, rfl⟩
  | right => exact ⟨right, rfl⟩
  | oracle g hg =>
    have hg' : g = chi R := hg
    exact ⟨query, hg'.symm⟩
  | pair _ _ ih₁ ih₂ =>
    obtain ⟨c₁, rfl⟩ := ih₁
    obtain ⟨c₂, rfl⟩ := ih₂
    exact ⟨pair c₁ c₂, rfl⟩
  | comp _ _ ih₁ ih₂ =>
    obtain ⟨c₁, rfl⟩ := ih₁
    obtain ⟨c₂, rfl⟩ := ih₂
    exact ⟨comp c₁ c₂, rfl⟩
  | prec _ _ ih₁ ih₂ =>
    obtain ⟨c₁, rfl⟩ := ih₁
    obtain ⟨c₂, rfl⟩ := ih₂
    exact ⟨prec c₁ c₂, rfl⟩
  | rfind _ ih =>
    obtain ⟨c₁, rfl⟩ := ih
    exact ⟨rfind c₁, rfl⟩

/-- A function is recursive in `oracle R` iff it is computed by a program.-/
theorem recursiveIn_iff_exists_code {f : ℕ →. ℕ} :
    RecursiveIn (oracle R) f ↔ ∃ c, eval R c = f :=
  ⟨exists_code, fun ⟨c, hc⟩ => hc ▸ eval_recursive c⟩

/-! ### Explicit numbering -/

/-- The explicit numbering of programs.-/
def encode : OracleCode → ℕ
  | zero => 0
  | succ => 1
  | left => 2
  | right => 3
  | query => 4
  | pair f g => 4 * Nat.pair (encode f) (encode g) + 5
  | comp f g => 4 * Nat.pair (encode f) (encode g) + 6
  | prec f g => 4 * Nat.pair (encode f) (encode g) + 7
  | rfind f => 4 * encode f + 8

/-- Constructor tag of a program number: `0,…,4` for the atoms `zero, succ, left, right, query`
and `5,6,7,8` for `pair, comp, prec, rfind`.-/
def codeTag (n : ℕ) : ℕ := if n < 5 then n else (n - 5) % 4 + 5

/-- Argument of a composite program number: `⟨f, g⟩` for `pair, comp, prec`, and `f` for
`rfind`.-/
def codeArg (n : ℕ) : ℕ := (n - 5) / 4

theorem primrec_codeTag : Primrec codeTag :=
  Primrec.ite (Primrec.nat_lt.comp Primrec.id (Primrec.const 5)) Primrec.id
    (Primrec.nat_add.comp (Primrec.nat_mod.comp (Primrec.nat_sub.comp Primrec.id
      (Primrec.const 5)) (Primrec.const 4)) (Primrec.const 5))

theorem primrec_codeArg : Primrec codeArg :=
  Primrec.nat_div.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 5)) (Primrec.const 4)

theorem codeArg_lt {n : ℕ} (h : ¬ n < 5) : codeArg n < n := by
  unfold codeArg; omega

/-- Decoding of program numbers (inverse of `encode`).-/
def decode (n : ℕ) : OracleCode :=
  if n < 5 then
    (if n = 0 then zero else if n = 1 then succ else if n = 2 then left else if n = 3 then right
      else query)
  else
    if (n - 5) % 4 = 0 then pair (decode (Nat.unpair (codeArg n)).1)
        (decode (Nat.unpair (codeArg n)).2)
    else if (n - 5) % 4 = 1 then comp (decode (Nat.unpair (codeArg n)).1)
        (decode (Nat.unpair (codeArg n)).2)
    else if (n - 5) % 4 = 2 then prec (decode (Nat.unpair (codeArg n)).1)
        (decode (Nat.unpair (codeArg n)).2)
    else rfind (decode (codeArg n))
termination_by n
decreasing_by
  all_goals first
    | exact codeArg_lt ‹_›
    | exact lt_of_le_of_lt (Nat.unpair_left_le _) (codeArg_lt ‹_›)
    | exact lt_of_le_of_lt (Nat.unpair_right_le _) (codeArg_lt ‹_›)

theorem decode_zero : decode 0 = zero := by rw [decode]; rfl
theorem decode_one : decode 1 = succ := by rw [decode]; rfl
theorem decode_two : decode 2 = left := by rw [decode]; rfl
theorem decode_three : decode 3 = right := by rw [decode]; rfl
theorem decode_four : decode 4 = query := by rw [decode]; rfl

/-- Constructor inspection on numbers: decoding a number with tag `5` (`pair`).-/
theorem decode_of_tag_pair {n : ℕ} (h : codeTag n = 5) :
    decode n = pair (decode (Nat.unpair (codeArg n)).1) (decode (Nat.unpair (codeArg n)).2) := by
  unfold codeTag at h
  rw [decode]
  split_ifs at h ⊢ <;> first | rfl | omega

theorem decode_of_tag_comp {n : ℕ} (h : codeTag n = 6) :
    decode n = comp (decode (Nat.unpair (codeArg n)).1) (decode (Nat.unpair (codeArg n)).2) := by
  unfold codeTag at h
  rw [decode]
  split_ifs at h ⊢ <;> first | rfl | omega

theorem decode_of_tag_prec {n : ℕ} (h : codeTag n = 7) :
    decode n = prec (decode (Nat.unpair (codeArg n)).1) (decode (Nat.unpair (codeArg n)).2) := by
  unfold codeTag at h
  rw [decode]
  split_ifs at h ⊢ <;> first | rfl | omega

theorem decode_of_tag_rfind {n : ℕ} (h : codeTag n = 8) :
    decode n = rfind (decode (codeArg n)) := by
  unfold codeTag at h
  rw [decode]
  split_ifs at h ⊢ <;> first | rfl | omega

theorem codeTag_eq_of_lt {n : ℕ} (h : n < 5) : codeTag n = n := by
  simp [codeTag, h]

theorem codeTag_lt (n : ℕ) : codeTag n < 9 := by
  unfold codeTag; split_ifs <;> omega

@[simp] theorem codeArg_encode_pair (f g : OracleCode) :
    codeArg (encode (pair f g)) = Nat.pair (encode f) (encode g) := by
  simp only [encode, codeArg]; omega
@[simp] theorem codeArg_encode_comp (f g : OracleCode) :
    codeArg (encode (comp f g)) = Nat.pair (encode f) (encode g) := by
  simp only [encode, codeArg]; omega
@[simp] theorem codeArg_encode_prec (f g : OracleCode) :
    codeArg (encode (prec f g)) = Nat.pair (encode f) (encode g) := by
  simp only [encode, codeArg]; omega
@[simp] theorem codeArg_encode_rfind (f : OracleCode) :
    codeArg (encode (rfind f)) = encode f := by
  simp only [encode, codeArg]; omega

/-- Round trip `encode ∘ decode = id`.-/
@[simp] theorem encode_decode (n : ℕ) : encode (decode n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 5
    · interval_cases n
      · rw [decode_zero]; rfl
      · rw [decode_one]; rfl
      · rw [decode_two]; rfl
      · rw [decode_three]; rfl
      · rw [decode_four]; rfl
    · have h0 := codeArg_lt h
      have h1 : (Nat.unpair (codeArg n)).1 < n := lt_of_le_of_lt (Nat.unpair_left_le _) h0
      have h2 : (Nat.unpair (codeArg n)).2 < n := lt_of_le_of_lt (Nat.unpair_right_le _) h0
      have ht := codeTag_lt n
      have hge : 5 ≤ codeTag n := by unfold codeTag; split_ifs; omega
      have key : ∀ k, k < 4 → codeTag n = k + 5 → 4 * codeArg n + (k + 5) = n := by
        intro k _ hk; unfold codeTag codeArg at *; split_ifs at hk; omega
      rcases (by omega : codeTag n = 5 ∨ codeTag n = 6 ∨ codeTag n = 7 ∨ codeTag n = 8)
        with h5 | h5 | h5 | h5
      · rw [decode_of_tag_pair h5]
        simp only [encode, ih _ h1, ih _ h2, Nat.pair_unpair]
        exact key 0 (by omega) h5
      · rw [decode_of_tag_comp h5]
        simp only [encode, ih _ h1, ih _ h2, Nat.pair_unpair]
        exact key 1 (by omega) h5
      · rw [decode_of_tag_prec h5]
        simp only [encode, ih _ h1, ih _ h2, Nat.pair_unpair]
        exact key 2 (by omega) h5
      · rw [decode_of_tag_rfind h5]
        simp only [encode, ih _ h0]
        have := key 3 (by omega) h5
        omega

/-! ### Unfolding lemmas for evaluation -/

@[simp] theorem eval_zero (x : ℕ) : eval R zero x = Part.some 0 := rfl
@[simp] theorem eval_succ (x : ℕ) : eval R succ x = Part.some (x + 1) := rfl
@[simp] theorem eval_left (x : ℕ) : eval R left x = Part.some (Nat.unpair x).1 := rfl
@[simp] theorem eval_right (x : ℕ) : eval R right x = Part.some (Nat.unpair x).2 := rfl
@[simp] theorem eval_query (x : ℕ) : eval R query x = chi R x := rfl

theorem mem_eval_pair {f g : OracleCode} {x y : ℕ} :
    y ∈ eval R (pair f g) x ↔ ∃ a ∈ eval R f x, ∃ b ∈ eval R g x, y = Nat.pair a b := by
  simp only [eval, Seq.seq, Part.mem_bind_iff]
  constructor
  · rintro ⟨u, hu, hy⟩
    obtain ⟨a, ha, rfl⟩ := (Part.mem_map_iff _).1 hu
    obtain ⟨b, hb, rfl⟩ := (Part.mem_map_iff _).1 hy
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨_, (Part.mem_map_iff _).2 ⟨a, ha, rfl⟩, (Part.mem_map_iff _).2 ⟨b, hb, rfl⟩⟩

theorem mem_eval_comp {f g : OracleCode} {x y : ℕ} :
    y ∈ eval R (comp f g) x ↔ ∃ z ∈ eval R g x, y ∈ eval R f z := by
  simp only [eval]
  exact Part.mem_bind_iff

theorem eval_prec_zero (f g : OracleCode) (a : ℕ) :
    eval R (prec f g) (Nat.pair a 0) = eval R f a := by
  simp only [eval, Nat.unpair_pair]; rfl

theorem eval_prec_succ (f g : OracleCode) (a n : ℕ) :
    eval R (prec f g) (Nat.pair a (n + 1)) =
      eval R (prec f g) (Nat.pair a n) >>= fun i => eval R g (Nat.pair a (Nat.pair n i)) := by
  simp only [eval, Nat.unpair_pair]

theorem mem_eval_prec_succ {f g : OracleCode} {a n y : ℕ} :
    y ∈ eval R (prec f g) (Nat.pair a (n + 1)) ↔
      ∃ i ∈ eval R (prec f g) (Nat.pair a n), y ∈ eval R g (Nat.pair a (Nat.pair n i)) := by
  rw [eval_prec_succ]; exact Part.mem_bind_iff

end OracleCode

end TheoremA.RelPres
