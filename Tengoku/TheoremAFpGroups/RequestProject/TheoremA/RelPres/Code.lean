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

/-- Every program evaluates to a function recursive in `oracle R`.
@isnad1 id=recursiv.0h2v.s3.d8f0ff87a469 from=translated src=- shape=7d0aa4b5 vocab=d1fa8d2c
-/
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
on the `RecursiveIn` derivation with an existential motive.
@isnad1 id=ex.1h2v.s4.966cf9584322 from=translated src=- shape=7625f443 vocab=f84a462f
-/
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

/-- A function is recursive in `oracle R` iff it is computed by a program.
@isnad1 id=iff.0h2v.s4.135f2b9cf4b8 from=translated src=- shape=78467482 vocab=f84a462f
-/
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

/--
@isnad1 id=primrec.0h0v.s3.7387f4ec913b from=translated src=- shape=e3d48bcb vocab=3a22b847
-/
theorem primrec_codeTag : Primrec codeTag :=
  Primrec.ite (Primrec.nat_lt.comp Primrec.id (Primrec.const 5)) Primrec.id
    (Primrec.nat_add.comp (Primrec.nat_mod.comp (Primrec.nat_sub.comp Primrec.id
      (Primrec.const 5)) (Primrec.const 4)) (Primrec.const 5))

/--
@isnad1 id=primrec.0h0v.s3.9aebdc25c2be from=translated src=- shape=e3d48bcb vocab=b03c2458
-/
theorem primrec_codeArg : Primrec codeArg :=
  Primrec.nat_div.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 5)) (Primrec.const 4)

/--
@isnad1 id=lt.1h1v.s4.cfd8c80fdc74 from=translated src=- shape=8a60f7e2 vocab=1a8d3768
-/
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

/--
@isnad1 id=eq.0h0v.s3.c5a62db9741d from=translated src=- shape=d3a93718 vocab=5e1f81c3
-/
theorem decode_zero : decode 0 = zero := by rw [decode]; rfl
/--
@isnad1 id=eq.0h0v.s3.3dda04d532cd from=translated src=- shape=d3a93718 vocab=636dd989
-/
theorem decode_one : decode 1 = succ := by rw [decode]; rfl
/--
@isnad1 id=eq.0h0v.s3.1359be128d2b from=translated src=- shape=d3a93718 vocab=107d3c22
-/
theorem decode_two : decode 2 = left := by rw [decode]; rfl
/--
@isnad1 id=eq.0h0v.s3.a562d8818a47 from=translated src=- shape=d3a93718 vocab=979b8348
-/
theorem decode_three : decode 3 = right := by rw [decode]; rfl
/--
@isnad1 id=eq.0h0v.s3.a1df885f7780 from=translated src=- shape=d3a93718 vocab=cc46cf44
-/
theorem decode_four : decode 4 = query := by rw [decode]; rfl

/-- Constructor inspection on numbers: decoding a number with tag `5` (`pair`).
@isnad1 id=eq.1h1v.s4.8a1c77b7274f from=translated src=- shape=1e2db51b vocab=3f8f58a1
-/
theorem decode_of_tag_pair {n : ℕ} (h : codeTag n = 5) :
    decode n = pair (decode (Nat.unpair (codeArg n)).1) (decode (Nat.unpair (codeArg n)).2) := by
  unfold codeTag at h
  rw [decode]
  split_ifs at h ⊢ <;> first | rfl | omega

/--
@isnad1 id=eq.1h1v.s4.02b28e299303 from=translated src=- shape=1e2db51b vocab=89f003f9
-/
theorem decode_of_tag_comp {n : ℕ} (h : codeTag n = 6) :
    decode n = comp (decode (Nat.unpair (codeArg n)).1) (decode (Nat.unpair (codeArg n)).2) := by
  unfold codeTag at h
  rw [decode]
  split_ifs at h ⊢ <;> first | rfl | omega

/--
@isnad1 id=eq.1h1v.s4.9c79c0d03c30 from=translated src=- shape=1e2db51b vocab=3d81664e
-/
theorem decode_of_tag_prec {n : ℕ} (h : codeTag n = 7) :
    decode n = prec (decode (Nat.unpair (codeArg n)).1) (decode (Nat.unpair (codeArg n)).2) := by
  unfold codeTag at h
  rw [decode]
  split_ifs at h ⊢ <;> first | rfl | omega

/--
@isnad1 id=eq.1h1v.s4.c9daff2841c7 from=translated src=- shape=ec65cc21 vocab=2b08b80f
-/
theorem decode_of_tag_rfind {n : ℕ} (h : codeTag n = 8) :
    decode n = rfind (decode (codeArg n)) := by
  unfold codeTag at h
  rw [decode]
  split_ifs at h ⊢ <;> first | rfl | omega

/--
@isnad1 id=eq.1h1v.s4.78b2197f4105 from=translated src=- shape=fc845374 vocab=bbb4a73a
-/
theorem codeTag_eq_of_lt {n : ℕ} (h : n < 5) : codeTag n = n := by
  simp [codeTag, h]

/--
@isnad1 id=lt.0h1v.s3.6148f9356989 from=translated src=- shape=b14ee516 vocab=bbb4a73a
-/
theorem codeTag_lt (n : ℕ) : codeTag n < 9 := by
  unfold codeTag; split_ifs <;> omega

/--
@isnad1 id=eq.0h2v.s4.bc2d62e172eb from=translated src=- shape=d506cc15 vocab=6309117f
-/
@[simp] theorem codeArg_encode_pair (f g : OracleCode) :
    codeArg (encode (pair f g)) = Nat.pair (encode f) (encode g) := by
  simp only [encode, codeArg]; omega
/--
@isnad1 id=eq.0h2v.s4.ba8a5b677dee from=translated src=- shape=d506cc15 vocab=ad56289a
-/
@[simp] theorem codeArg_encode_comp (f g : OracleCode) :
    codeArg (encode (comp f g)) = Nat.pair (encode f) (encode g) := by
  simp only [encode, codeArg]; omega
/--
@isnad1 id=eq.0h2v.s4.62ba7a857896 from=translated src=- shape=d506cc15 vocab=317bfd7a
-/
@[simp] theorem codeArg_encode_prec (f g : OracleCode) :
    codeArg (encode (prec f g)) = Nat.pair (encode f) (encode g) := by
  simp only [encode, codeArg]; omega
/--
@isnad1 id=eq.0h1v.s3.6718a530633f from=translated src=- shape=e0f744a2 vocab=a1d77417
-/
@[simp] theorem codeArg_encode_rfind (f : OracleCode) :
    codeArg (encode (rfind f)) = encode f := by
  simp only [encode, codeArg]; omega

/-- Round trip `encode ∘ decode = id`.
@isnad1 id=eq.0h1v.s3.d85d35551807 from=translated src=- shape=47dcad53 vocab=d981948e
-/
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

/--
@isnad1 id=eq.0h2v.s4.24fc42b8c8be from=translated src=- shape=a8bd842c vocab=28cdf235
-/
@[simp] theorem eval_zero (x : ℕ) : eval R zero x = Part.some 0 := rfl
/--
@isnad1 id=eq.0h2v.s4.eb50fbfda1d4 from=translated src=- shape=284febf5 vocab=ba5e2b94
-/
@[simp] theorem eval_succ (x : ℕ) : eval R succ x = Part.some (x + 1) := rfl
/--
@isnad1 id=eq.0h2v.s4.feff30afe037 from=translated src=- shape=a34834ee vocab=19361c82
-/
@[simp] theorem eval_left (x : ℕ) : eval R left x = Part.some (Nat.unpair x).1 := rfl
/--
@isnad1 id=eq.0h2v.s4.5839432ffbcf from=translated src=- shape=a34834ee vocab=13cc8f2c
-/
@[simp] theorem eval_right (x : ℕ) : eval R right x = Part.some (Nat.unpair x).2 := rfl
/--
@isnad1 id=eq.0h2v.s3.4b1aedcdccd9 from=translated src=- shape=236dfd10 vocab=c3937148
-/
@[simp] theorem eval_query (x : ℕ) : eval R query x = chi R x := rfl

/--
@isnad1 id=iff.0h5v.s5.48acbfc9e464 from=translated src=- shape=a6023fa3 vocab=0b02148c
-/
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

/--
@isnad1 id=iff.0h5v.s5.46e62a25d90a from=translated src=- shape=f6524e12 vocab=a2fd6276
-/
theorem mem_eval_comp {f g : OracleCode} {x y : ℕ} :
    y ∈ eval R (comp f g) x ↔ ∃ z ∈ eval R g x, y ∈ eval R f z := by
  simp only [eval]
  exact Part.mem_bind_iff

/--
@isnad1 id=eq.0h4v.s4.8acb7d1c72fc from=translated src=- shape=f6269f5c vocab=ca9b491a
-/
theorem eval_prec_zero (f g : OracleCode) (a : ℕ) :
    eval R (prec f g) (Nat.pair a 0) = eval R f a := by
  simp only [eval, Nat.unpair_pair]; rfl

/--
@isnad1 id=eq.0h5v.s5.7062b36c08c2 from=translated src=- shape=65a88150 vocab=178e5ac9
-/
theorem eval_prec_succ (f g : OracleCode) (a n : ℕ) :
    eval R (prec f g) (Nat.pair a (n + 1)) =
      eval R (prec f g) (Nat.pair a n) >>= fun i => eval R g (Nat.pair a (Nat.pair n i)) := by
  simp only [eval, Nat.unpair_pair]

/--
@isnad1 id=iff.0h6v.s6.5ff959397a0a from=translated src=- shape=e7501885 vocab=24117960
-/
theorem mem_eval_prec_succ {f g : OracleCode} {a n y : ℕ} :
    y ∈ eval R (prec f g) (Nat.pair a (n + 1)) ↔
      ∃ i ∈ eval R (prec f g) (Nat.pair a n), y ∈ eval R g (Nat.pair a (Nat.pair n i)) := by
  rw [eval_prec_succ]; exact Part.mem_bind_iff

end OracleCode

end TheoremA.RelPres
