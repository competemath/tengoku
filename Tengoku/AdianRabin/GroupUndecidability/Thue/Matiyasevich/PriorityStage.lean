import Tengoku.AdianRabin.GroupUndecidability.Thue.Matiyasevich.FinalStage
import Tengoku.Seed.Data.List.GetD
import Tengoku.Seed.Data.Nat.Log

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Undecidability
namespace Thue
namespace Matiyasevich1993
namespace Priority

/-!
The power-of-two padding, transposition, and first priority block from
Sections 2.3--2.4 of Matiyasevich (1995).  This file is deliberately
parameterized by the binary rule words; the preceding binary encoding stage
supplies those words and their common-length/code-language properties.
-/

abbrev A₂ := Fin 3

def a : A₂ := 0
def b : A₂ := 1
def e : A₂ := 2

/-- The exponent `u` for the least power `t = 2^u` not below `r`.-/
def exponent (r : ℕ) : ℕ := Nat.clog 2 r

/-- The number `t` of rows used in the transposed long relation.-/
def powerCount (r : ℕ) : ℕ := 2 ^ exponent r

/--
@isnad1 id=le.0h1v.s3.c8fcd9e159d2 from=translated src=- shape=e63234f4 vocab=284cdd1b
-/
theorem relationCount_le_powerCount (r : ℕ) : r ≤ powerCount r :=
  (Nat.clog_le_iff_le_pow (b := 2) (by omega)).mp le_rfl

/--
@isnad1 id=lt.0h1v.s3.1fd753840937 from=translated src=- shape=8a62b088 vocab=976a0861
-/
theorem powerCount_pos (r : ℕ) : 0 < powerCount r :=
  pow_pos (by omega) _

/-- Repeat the first relation when the original list is extended to `2^u`
relations.  The paper repeats the last relation; either choice has the same
effect.-/
def paddedIndex {r : ℕ} (hr : 0 < r) (i : Fin (powerCount r)) : Fin r :=
  if h : i.val < r then ⟨i.val, h⟩ else ⟨0, hr⟩

def paddedSide {r : ℕ} (hr : 0 < r) {α : Type*}
    (W : Fin r → List α) (i : Fin (powerCount r)) : List α :=
  W (paddedIndex hr i)

/-- A column of a rectangular family of words.-/
def column {t : ℕ} (rows : Fin t → List (Fin 2)) (j : ℕ) : List (Fin 2) :=
  List.ofFn fun i => (rows i).getD j 0

/-- Consecutive columns, starting at column `j`.-/
def columnsFrom {t : ℕ} (rows : Fin t → List (Fin 2)) : ℕ → ℕ → List (Fin 2)
  | _, 0 => []
  | j, k + 1 => column rows j ++ columnsFrom rows (j + 1) k

/-- The column-major words `L` and `M` displayed at the bottom of page 48.-/
def transpose {t : ℕ} (width : ℕ)
    (rows : Fin t → List (Fin 2)) : List (Fin 2) :=
  columnsFrom rows 0 width

/--
@isnad1 id=eq.0h4v.s6.4f478cdebd8e from=translated src=- shape=05d0fcb0 vocab=b776a806
-/
@[simp] theorem columnsFrom_succ {t : ℕ} (rows : Fin t → List (Fin 2))
    (j k : ℕ) :
    columnsFrom rows j (k + 1) =
      column rows j ++ columnsFrom rows (j + 1) k := rfl

/--
@isnad1 id=eq.0h3v.s4.bb0fa491650b from=translated src=- shape=9a3f3c1c vocab=d81b9260
-/
theorem column_length {t : ℕ} (rows : Fin t → List (Fin 2)) (j : ℕ) :
    (column rows j).length = t := by
  simp [column]

/--
@isnad1 id=eq.0h4v.s5.aeb802a0b7f4 from=translated src=- shape=98b286d9 vocab=fab07cf3
-/
theorem columnsFrom_length {t width : ℕ}
    (rows : Fin t → List (Fin 2)) (start : ℕ) :
    (columnsFrom rows start width).length = width * t := by
  induction width generalizing start with
  | zero => simp [columnsFrom]
  | succ width ih =>
      simp [columnsFrom, column_length, ih, Nat.succ_mul, Nat.add_comm]

/--
@isnad1 id=eq.0h3v.s5.4b3fdc6accb7 from=translated src=- shape=c066949e vocab=8ffc85b1
-/
theorem transpose_length {t width : ℕ}
    (rows : Fin t → List (Fin 2)) :
    (transpose width rows).length = width * t :=
  columnsFrom_length rows 0

/--
@isnad1 id=eq.1h2v.s7.0e2d6150d1cd from=translated src=- shape=24d840b9 vocab=c80f1416
-/
theorem column_zero_of_starts_aa {t : ℕ}
    (rows : Fin t → List (Fin 2))
    (hrows : ∀ i, ∃ tail, rows i = (0 : Fin 2) :: 0 :: tail) :
    column rows 0 = List.replicate t 0 := by
  unfold column
  have hfun :
      (fun i : Fin t => (rows i).getD 0 0) = fun _ => (0 : Fin 2) := by
    funext i
    obtain ⟨tail, hi⟩ := hrows i
    simp [hi]
  rw [hfun, List.ofFn_const]

/--
@isnad1 id=eq.1h2v.s7.5d4a2adccb83 from=translated src=- shape=24d840b9 vocab=c80f1416
-/
theorem column_one_of_starts_aa {t : ℕ}
    (rows : Fin t → List (Fin 2))
    (hrows : ∀ i, ∃ tail, rows i = (0 : Fin 2) :: 0 :: tail) :
    column rows 1 = List.replicate t 0 := by
  unfold column
  have hfun :
      (fun i : Fin t => (rows i).getD 1 0) = fun _ => (0 : Fin 2) := by
    funext i
    obtain ⟨tail, hi⟩ := hrows i
    simp [hi]
  rw [hfun, List.ofFn_const]

/-- The long word begins with `2t` copies of `a`, the fact used on page 50.
@isnad1 id=ex.2h3v.s7.5662fd9449c1 from=translated src=- shape=69a7b619 vocab=846f11c1
-/
theorem transpose_starts_two_columns {t width : ℕ}
    (rows : Fin t → List (Fin 2)) (hwidth : 2 ≤ width)
    (hrows : ∀ i, ∃ tail, rows i = (0 : Fin 2) :: 0 :: tail) :
    ∃ tail,
      transpose width rows = List.replicate (2 * t) 0 ++ tail := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hwidth
  refine ⟨columnsFrom rows 2 k, ?_⟩
  simp only [transpose, Nat.add_comm 2 k, columnsFrom]
  rw [column_zero_of_starts_aa rows hrows,
    column_one_of_starts_aa rows hrows]
  change List.replicate t 0 ++
      (List.replicate t 0 ++ columnsFrom rows 2 k) =
    List.replicate (2 * t) 0 ++ columnsFrom rows 2 k
  rw [← List.append_assoc]
  rw [← List.replicate_add]
  congr 2
  omega

/-! ### The first priority block -/

/-- Move one `e` rightwards through pairs of binary letters.  On a binary
word this retains every second letter and leaves the `e` at the end.-/
def pushE : List A₂ → List A₂
  | x :: y :: rest =>
      if x ≠ e ∧ y ≠ e then y :: pushE rest else e :: x :: y :: rest
  | rest => e :: rest

/-- Canonical normalization for rules (20)--(23), processing from right to
left.-/
def firstNormal : List A₂ → List A₂
  | [] => []
  | x :: rest =>
      if x = e then pushE (firstNormal rest)
      else x :: firstNormal rest

/--
@isnad1 id=eq.0h1v.s4.88c98c8c66ce from=translated src=- shape=7e140789 vocab=b725800e
-/
@[simp] theorem firstNormal_a_cons (W : List A₂) :
    firstNormal (a :: W) = a :: firstNormal W := by
  simp [firstNormal, a, e]

/--
@isnad1 id=eq.0h1v.s4.0d3830c50eb8 from=translated src=- shape=7e140789 vocab=f126a468
-/
@[simp] theorem firstNormal_b_cons (W : List A₂) :
    firstNormal (b :: W) = b :: firstNormal W := by
  simp [firstNormal, b, e]

/--
@isnad1 id=eq.0h1v.s3.e9051328d937 from=translated src=- shape=26286207 vocab=5a352115
-/
@[simp] theorem firstNormal_e_cons (W : List A₂) :
    firstNormal (e :: W) = pushE (firstNormal W) := by
  simp [firstNormal]

/--
@isnad1 id=eq.0h1v.s4.c6d8f849de9f from=translated src=- shape=d001ed8a vocab=41f9396f
-/
@[simp] theorem pushE_aa (W : List A₂) :
    pushE (a :: a :: W) = a :: pushE W := by
  simp [pushE, a, e]

/--
@isnad1 id=eq.0h1v.s4.539679f82a0f from=translated src=- shape=e513e15c vocab=e88df3e6
-/
@[simp] theorem pushE_ab (W : List A₂) :
    pushE (a :: b :: W) = b :: pushE W := by
  simp [pushE, a, b, e]

/--
@isnad1 id=eq.0h1v.s4.3dceb9521729 from=translated src=- shape=e513e15c vocab=e88df3e6
-/
@[simp] theorem pushE_ba (W : List A₂) :
    pushE (b :: a :: W) = a :: pushE W := by
  simp [pushE, a, b, e]

/--
@isnad1 id=eq.0h1v.s4.b0d9edb25092 from=translated src=- shape=d001ed8a vocab=9d93a046
-/
@[simp] theorem pushE_bb (W : List A₂) :
    pushE (b :: b :: W) = b :: pushE W := by
  simp [pushE, b, e]

/--
@isnad1 id=eq.1h3v.s5.047bc6c71970 from=translated src=- shape=422458b8 vocab=cb78b73d
-/
theorem firstNormal_prefix_congr (l : List A₂) {X Y : List A₂}
    (h : firstNormal X = firstNormal Y) :
    firstNormal (l ++ X) = firstNormal (l ++ Y) := by
  induction l with
  | nil => simpa
  | cons x l ih =>
      rw [List.cons_append, List.cons_append]
      unfold firstNormal
      split <;> simp_all

/-- The four left sides (20)--(23), using the local names for `a,b,e`.-/
def housekeepingF : Fin 4 → List A₂ := ![
  [e, a, a], [e, a, b], [e, b, a], [e, b, b]
]

/-- The four right sides (20)--(23).-/
def housekeepingE : Fin 4 → List A₂ := ![
  [a, e], [b, e], [a, e], [b, e]
]

/-- One use of a housekeeping rule in any two-sided context preserves the
first priority normal form.
@isnad1 id=eq.0h3v.s6.3d13d1c8400a from=translated src=- shape=9e3e91c0 vocab=c6d53dcd
-/
theorem firstNormal_housekeeping
    (l r : List A₂) (i : Fin 4) :
    firstNormal (l ++ housekeepingF i ++ r) =
      firstNormal (l ++ housekeepingE i ++ r) := by
  rw [List.append_assoc, List.append_assoc]
  apply firstNormal_prefix_congr l
  fin_cases i <;> simp [housekeepingF, housekeepingE]

/-- One directed rewrite from the first priority block.-/
def FirstStep (X Y : List A₂) : Prop :=
  ∃ l r i,
    X = l ++ housekeepingF i ++ r ∧
    Y = l ++ housekeepingE i ++ r

abbrev FirstEq := Relation.ReflTransGen FirstStep

private theorem firstStep_rule (i : Fin 4) (l r : List A₂) :
    FirstStep (l ++ housekeepingF i ++ r) (l ++ housekeepingE i ++ r) :=
  ⟨l, r, i, rfl, rfl⟩

/--
@isnad1 id=firstste.1h3v.s5.b8309f6c90f3 from=translated src=- shape=a94430c7 vocab=0a17d2a4
-/
theorem firstStep_prefix (l : List A₂) {X Y : List A₂}
    (h : FirstStep X Y) : FirstStep (l ++ X) (l ++ Y) := by
  rcases h with ⟨l', r, i, rfl, rfl⟩
  refine ⟨l ++ l', r, i, ?_, ?_⟩ <;> simp [List.append_assoc]

/--
@isnad1 id=firsteq.1h3v.s5.1d95f26bf6dc from=translated src=- shape=a94430c7 vocab=795cf9cd
-/
theorem firstEq_prefix (l : List A₂) {X Y : List A₂}
    (h : FirstEq X Y) : FirstEq (l ++ X) (l ++ Y) :=
  h.lift (l ++ ·) (fun _ _ hstep => firstStep_prefix l hstep)

/-- Greedily moving one `e` is itself a directed derivation.
@isnad1 id=firsteq.0h1v.s3.b7255efb2b77 from=translated src=- shape=d213e086 vocab=2bb97bc0
-/
theorem pushE_reachable (W : List A₂) : FirstEq (e :: W) (pushE W) := by
  induction W using List.twoStepInduction with
  | nil => exact Relation.ReflTransGen.refl
  | singleton x => exact Relation.ReflTransGen.refl
  | cons_cons x y rest ih _ =>
      fin_cases x <;> fin_cases y
      · exact (Relation.ReflTransGen.single
          (firstStep_rule 0 [] rest)).trans (firstEq_prefix [a] ih)
      · exact (Relation.ReflTransGen.single
          (firstStep_rule 1 [] rest)).trans (firstEq_prefix [b] ih)
      · exact Relation.ReflTransGen.refl
      · exact (Relation.ReflTransGen.single
          (firstStep_rule 2 [] rest)).trans (firstEq_prefix [a] ih)
      · exact (Relation.ReflTransGen.single
          (firstStep_rule 3 [] rest)).trans (firstEq_prefix [b] ih)
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.refl

/-- Every word reduces to the canonical value computed by `firstNormal`.
@isnad1 id=firsteq.0h1v.s2.4968dcfbb741 from=translated src=- shape=802d6110 vocab=bed6a7e1
-/
theorem firstNormal_reachable (W : List A₂) : FirstEq W (firstNormal W) := by
  induction W with
  | nil => exact Relation.ReflTransGen.refl
  | cons x W ih =>
      have htail : FirstEq (x :: W) (x :: firstNormal W) := by
        simpa only [List.singleton_append] using firstEq_prefix [x] ih
      by_cases hx : x = e
      · subst x
        exact htail.trans (by simpa using pushE_reachable (firstNormal W))
      · simpa [firstNormal, hx] using htail

/-! ### The `e`-count and the final alignment argument -/

def eCount (W : List A₂) : ℕ := W.count e

/--
@isnad1 id=eq.0h0v.s3.f52bd5deb0c9 from=translated src=- shape=35225b15 vocab=df661042
-/
@[simp] theorem eCount_nil : eCount [] = 0 := rfl

/--
@isnad1 id=eq.0h2v.s5.fb1e75799e0a from=translated src=- shape=31b9e54f vocab=aefa2c54
-/
@[simp] theorem eCount_append (X Y : List A₂) :
    eCount (X ++ Y) = eCount X + eCount Y := by
  simp [eCount]

/--
@isnad1 id=eq.0h1v.s3.2a6b0ec84fb4 from=translated src=- shape=43b70bd7 vocab=94e8966f
-/
@[simp] theorem eCount_replicate_a (n : ℕ) :
    eCount (List.replicate n a) = 0 := by
  unfold eCount
  rw [List.count_eq_zero]
  simp [a, e]

/--
@isnad1 id=eq.0h0v.s4.c255d97617ec from=translated src=- shape=8bd47bdb vocab=67590ef9
-/
@[simp] theorem eCount_ae : eCount [a, e] = 1 := by decide

/--
@isnad1 id=eq.1h2v.s4.367baf39e436 from=translated src=- shape=930726e8 vocab=72a47615
-/
theorem firstStep_eCount {X Y : List A₂} (h : FirstStep X Y) :
    eCount X = eCount Y := by
  rcases h with ⟨l, r, i, rfl, rfl⟩
  fin_cases i <;> simp [housekeepingF, housekeepingE, eCount, a, b, e]

/--
@isnad1 id=eq.1h2v.s4.522ae2239990 from=translated src=- shape=930726e8 vocab=e236104c
-/
theorem firstEq_eCount {X Y : List A₂} (h : FirstEq X Y) :
    eCount X = eCount Y := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (firstStep_eCount hstep)

/--
@isnad1 id=eq.0h1v.s3.50d16119a881 from=translated src=- shape=b59b98b7 vocab=8567eae2
-/
theorem firstNormal_eCount (W : List A₂) :
    eCount (firstNormal W) = eCount W :=
  (firstEq_eCount (firstNormal_reachable W)).symm

/-- Include a binary word into the alphabet `{a,b,e}`.-/
def liftBit (x : Fin 2) : A₂ := Fin.castLE (by omega) x

def liftBinary (W : List (Fin 2)) : List A₂ := W.map liftBit

/--
@isnad1 id=eq.0h2v.s5.48351f469192 from=translated src=- shape=95c3e8a8 vocab=7ee7918d
-/
@[simp] theorem liftBinary_cons (x : Fin 2) (W : List (Fin 2)) :
    liftBinary (x :: W) = liftBit x :: liftBinary W := rfl

/--
@isnad1 id=eq.0h2v.s6.83fa0db4638d from=translated src=- shape=3d0fbb06 vocab=4fb73f8e
-/
@[simp] theorem liftBinary_append (X Y : List (Fin 2)) :
    liftBinary (X ++ Y) = liftBinary X ++ liftBinary Y := by
  simp [liftBinary]

/--
@isnad1 id=eq.0h1v.s4.16a6c8731377 from=translated src=- shape=dc1acdc6 vocab=178bd818
-/
@[simp] theorem eCount_liftBinary (W : List (Fin 2)) :
    eCount (liftBinary W) = 0 := by
  unfold eCount
  rw [List.count_eq_zero]
  simp [liftBinary, liftBit, e]

/--
@isnad1 id=injectiv.0h0v.s3.a84293dbe0ec from=translated src=- shape=bfe16b09 vocab=e177e3bc
-/
theorem liftBit_injective : Function.Injective liftBit := by
  intro x y h
  apply Fin.ext
  exact congrArg (fun z : A₂ => z.val) h

/--
@isnad1 id=injectiv.0h0v.s3.32b3fcff90e0 from=translated src=- shape=4b0fdcd1 vocab=0464c442
-/
theorem liftBinary_injective : Function.Injective liftBinary :=
  liftBit_injective.list_map

/-- Equation (11) for `i=1`: append `a e^u` to the binary encoding.-/
def encode (u : ℕ) (W : List (Fin 2)) : List A₂ :=
  liftBinary W ++ [a] ++ List.replicate u e

/--
@isnad1 id=computab.0h1v.s5.d1f3e4c1643c from=translated src=- shape=08ae0ce5 vocab=d2698c24
-/
theorem encode_computable (u : ℕ) : Computable (encode u) := by
  have hlift : Primrec liftBinary :=
    Primrec.list_map Primrec.id
      ((Primrec.dom_finite liftBit).comp₂ Primrec₂.right)
  have hwithA : Primrec fun W : List (Fin 2) => liftBinary W ++ [a] :=
    Primrec.list_append.comp hlift (Primrec.const [a])
  exact (Primrec.list_append.comp hwithA
    (Primrec.const (List.replicate u e))).to_comp

/--
@isnad1 id=ne.0h2v.s4.d43c677e2eb6 from=translated src=- shape=58e8495d vocab=e32ff5fa
-/
theorem encode_ne_nil (u : ℕ) (W : List (Fin 2)) : encode u W ≠ [] := by
  simp [encode]

/--
@isnad1 id=eq.0h2v.s4.fdd7b69c8842 from=translated src=- shape=306e8207 vocab=d3b6b511
-/
@[simp] theorem encode_eCount (u : ℕ) (W : List (Fin 2)) :
    eCount (encode u W) = u := by
  rw [show encode u W =
    liftBinary W ++ ([a] ++ List.replicate u e) by simp [encode]]
  rw [eCount_append, eCount_liftBinary]
  simp [eCount, a, e]

/--
@isnad1 id=eq.0h1v.s4.6e65821eadc2 from=translated src=- shape=bd6b4149 vocab=d51958f3
-/
@[simp] theorem pushE_replicate_e (u : ℕ) :
    pushE (List.replicate u e) = e :: List.replicate u e := by
  cases u with
  | zero => rfl
  | succ u =>
      cases u with
      | zero => rfl
      | succ u =>
          rw [List.replicate_succ, List.replicate_succ]
          simp [pushE, e]

/--
@isnad1 id=eq.0h1v.s3.75727a1ae9a0 from=translated src=- shape=93d34c32 vocab=8e5671cd
-/
theorem firstNormal_replicate_e (u : ℕ) :
    firstNormal (List.replicate u e) = List.replicate u e := by
  induction u with
  | zero => rfl
  | succ u ih =>
      rw [List.replicate_succ, firstNormal_e_cons, ih]
      exact pushE_replicate_e u

/--
@isnad1 id=eq.0h2v.s5.3657127f82e5 from=translated src=- shape=915c267a vocab=60c3c1b5
-/
theorem firstNormal_liftBinary_append (W : List (Fin 2)) (T : List A₂) :
    firstNormal (liftBinary W ++ T) =
      liftBinary W ++ firstNormal T := by
  induction W with
  | nil => rfl
  | cons x W ih =>
      rw [liftBinary_cons, List.cons_append]
      fin_cases x
      · change firstNormal (a :: (liftBinary W ++ T)) =
          a :: (liftBinary W ++ firstNormal T)
        rw [firstNormal_a_cons, ih]
      · change firstNormal (b :: (liftBinary W ++ T)) =
          b :: (liftBinary W ++ firstNormal T)
        rw [firstNormal_b_cons, ih]

/--
@isnad1 id=eq.0h2v.s4.d118d9771365 from=translated src=- shape=c33e3e61 vocab=c991ea5a
-/
@[simp] theorem firstNormal_encode (u : ℕ) (W : List (Fin 2)) :
    firstNormal (encode u W) = encode u W := by
  unfold encode
  rw [List.append_assoc]
  rw [firstNormal_liftBinary_append]
  simp only [List.singleton_append, firstNormal_a_cons,
    firstNormal_replicate_e]

/--
@isnad1 id=eq.1h3v.s4.7e2470745c43 from=translated src=- shape=1dcdb26d vocab=14504d49
-/
theorem stage₂_side_eCount (L M : List A₂)
    (hLM : eCount L = eCount M) (i : Fin 5) :
    eCount (stage₂F L i) = eCount (stage₂E M i) := by
  fin_cases i
  · change List.count (2 : Fin 3) [2, 0, 0] = List.count 2 [0, 2]
    decide
  · change List.count (2 : Fin 3) [2, 0, 1] = List.count 2 [1, 2]
    decide
  · change List.count (2 : Fin 3) [2, 1, 0] = List.count 2 [0, 2]
    decide
  · change List.count (2 : Fin 3) [2, 1, 1] = List.count 2 [1, 2]
    decide
  · change eCount L = eCount M
    exact hLM

/--
@isnad1 id=eq.2h4v.s5.71edc67c17ac from=translated src=- shape=7dc32450 vocab=279c28b4
-/
theorem stage₂Step_eCount (L M : List A₂)
    (hLM : eCount L = eCount M) {X Y : List A₂}
    (h : ThueStep (stage₂System L M) X Y) : eCount X = eCount Y := by
  rcases h with ⟨l, r, x, y, ⟨i, hxy⟩, hwords⟩
  injection hxy with hx hy
  subst x
  subst y
  have hsides := stage₂_side_eCount L M hLM i
  rcases hwords with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa [eCount, Nat.add_assoc] using
      congrArg (fun n => eCount l + n + eCount r) hsides
  · simpa [eCount, Nat.add_assoc] using
      (congrArg (fun n => eCount l + n + eCount r) hsides).symm

/--
@isnad1 id=eq.2h4v.s5.dcafa288a0e2 from=translated src=- shape=7dc32450 vocab=1770c46b
-/
theorem stage₂Eq_eCount (L M : List A₂)
    (hLM : eCount L = eCount M) {X Y : List A₂}
    (h : ThueEq (stage₂System L M) X Y) : eCount X = eCount Y := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (stage₂Step_eCount L M hLM hstep)

/-- Absence of a run `aaa`.-/
def NoAAA (W : List A₂) : Prop :=
  ¬ ∃ l r, W = l ++ [a, a, a] ++ r

/-- A word contains `k` consecutive copies of `a`.-/
def HasARun (k : ℕ) (W : List A₂) : Prop :=
  ∃ l r, W = l ++ List.replicate k a ++ r

/--
@isnad1 id=hasarun.1h3v.s4.408a01232eea from=translated src=- shape=cb36b207 vocab=9dba44f2
-/
theorem hasARun_prefix (p : List A₂) {k : ℕ} {W : List A₂}
    (h : HasARun k W) : HasARun k (p ++ W) := by
  obtain ⟨l, r, rfl⟩ := h
  refine ⟨p ++ l, r, ?_⟩
  simp only [List.append_assoc]

/--
@isnad1 id=hasarun.2h3v.s4.d4479a245944 from=translated src=- shape=03c0ee99 vocab=ec309abc
-/
theorem hasARun_of_le {m n : ℕ} {W : List A₂} (hmn : m ≤ n)
    (h : HasARun n W) : HasARun m W := by
  obtain ⟨l, r, rfl⟩ := h
  refine ⟨l, List.replicate (n - m) a ++ r, ?_⟩
  calc
    l ++ List.replicate n a ++ r =
        l ++ List.replicate (m + (n - m)) a ++ r := by
          rw [Nat.add_sub_of_le hmn]
    _ = l ++ List.replicate m a ++
        (List.replicate (n - m) a ++ r) := by
          simp only [List.replicate_add, List.append_assoc]

/-- On a binary run, `pushE` keeps every second letter.
@isnad1 id=eq.0h2v.s5.030f5d085d7e from=translated src=- shape=922b8f54 vocab=6038e0de
-/
theorem pushE_replicate_even (k : ℕ) (W : List A₂) :
    pushE (List.replicate (2 * k) a ++ W) =
      List.replicate k a ++ pushE W := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 + 2 * k by omega,
        List.replicate_add]
      change pushE (a :: a :: (List.replicate (2 * k) a ++ W)) =
        a :: (List.replicate k a ++ pushE W)
      rw [pushE_aa, ih]

/-- A possible one-letter parity offset before an even run does not affect
the sharp halving estimate.
@isnad1 id=hasarun.0h3v.s5.983eebd450c3 from=translated src=- shape=1d294d1e vocab=ea9c6323
-/
theorem pushE_singleton_hasARun (x : A₂) (k : ℕ) (W : List A₂) :
    HasARun k (pushE (x :: List.replicate (2 * k) a ++ W)) := by
  cases k with
  | zero =>
      exact ⟨[], pushE (x :: W), by simp⟩
  | succ k =>
      have hrep :
          List.replicate (2 * (k + 1)) a ++ W =
            a :: (List.replicate (2 * k) a ++ (a :: W)) := by
        rw [show 2 * (k + 1) = 1 + 2 * k + 1 by omega,
          List.replicate_add, List.replicate_add]
        simp only [List.replicate_one,
          List.append_assoc, List.cons_append, List.nil_append]
      change HasARun (k + 1)
        (pushE (x :: (List.replicate (2 * (k + 1)) a ++ W)))
      by_cases hx : x = e
      · subst x
        apply hasARun_of_le (by omega : k + 1 ≤ 2 * (k + 1))
        refine ⟨[e, e], W, ?_⟩
        calc
          pushE (e :: (List.replicate (2 * (k + 1)) a ++ W)) =
              e :: e :: (List.replicate (2 * (k + 1)) a ++ W) := by
                rw [hrep]
                simp [pushE, a, e]
          _ = [e, e] ++ List.replicate (2 * (k + 1)) a ++ W := by
                simp
      · rw [hrep]
        have hpush : ∀ Z : List A₂,
            pushE (x :: a :: Z) = a :: pushE Z := by
          intro Z
          have hxe : x ≠ (2 : A₂) := by simpa [e] using hx
          simp [pushE, hxe, a, e]
        rw [hpush, pushE_replicate_even]
        refine ⟨[], pushE (a :: W), ?_⟩
        simp only [List.nil_append]
        rw [show k + 1 = Nat.succ k by omega, List.replicate_succ]
        simp only [List.cons_append]

/-- The sharp run estimate for one first-priority normalization step: one
`e` can at most halve the length of an `a`-run.
@isnad1 id=hasarun.1h2v.s4.33350951268f from=translated src=- shape=6964c726 vocab=7d8c2a3f
-/
theorem pushE_hasARun_half {k : ℕ} {W : List A₂}
    (h : HasARun (2 * k) W) : HasARun k (pushE W) := by
  obtain ⟨l, r, rfl⟩ := h
  induction l using List.twoStepInduction with
  | nil =>
      simp only [List.nil_append]
      rw [pushE_replicate_even]
      exact ⟨[], pushE r, by simp⟩
  | singleton x =>
      exact pushE_singleton_hasARun x k r
  | cons_cons x y l ih _ =>
      by_cases hxy : x ≠ e ∧ y ≠ e
      · rw [show x :: y :: l ++ List.replicate (2 * k) a ++ r =
            x :: y :: (l ++ List.replicate (2 * k) a ++ r) by simp]
        change HasARun k (if x ≠ e ∧ y ≠ e then
          y :: pushE (l ++ List.replicate (2 * k) a ++ r)
          else e :: x :: y :: (l ++ List.replicate (2 * k) a ++ r))
        rw [ite_eq_left hxy]
        exact hasARun_prefix [y] ih
      · rw [show x :: y :: l ++ List.replicate (2 * k) a ++ r =
            x :: y :: (l ++ List.replicate (2 * k) a ++ r) by simp]
        change HasARun k (if x ≠ e ∧ y ≠ e then
          y :: pushE (l ++ List.replicate (2 * k) a ++ r)
          else e :: x :: y :: (l ++ List.replicate (2 * k) a ++ r))
        rw [ite_eq_right hxy]
        apply hasARun_of_le (by omega : k ≤ 2 * k)
        exact ⟨[e, x, y] ++ l, r, by simp [List.append_assoc]⟩

/--
@isnad1 id=eq.0h2v.s5.c12eeeb8ff5e from=translated src=- shape=fc42b7bf vocab=f9464cc7
-/
theorem firstNormal_replicate_a_append (n : ℕ) (W : List A₂) :
    firstNormal (List.replicate n a ++ W) =
      List.replicate n a ++ firstNormal W := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ]
      simp only [List.cons_append, firstNormal_a_cons, ih]

/-- After normalizing a prefix `X`, every one of its `e` letters can have
halved a following run at most once.
@isnad1 id=hasarun.0h3v.s6.6f0311948ad0 from=translated src=- shape=32da0ce4 vocab=a5661a5e
-/
theorem firstNormal_hasARun_scaled (X Y : List A₂) (k : ℕ) :
    HasARun k (firstNormal
      (X ++ List.replicate (2 ^ eCount X * k) a ++ Y)) := by
  induction X generalizing k with
  | nil =>
      rw [eCount_nil, pow_zero, one_mul, List.nil_append,
        firstNormal_replicate_a_append]
      exact ⟨[], firstNormal Y, by simp⟩
  | cons x X ih =>
      by_cases hx : x = e
      · subst x
        change HasARun k (pushE (firstNormal
          (X ++ List.replicate (2 ^ eCount (e :: X) * k) a ++ Y)))
        simpa [eCount, pow_succ, Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm] using
            (pushE_hasARun_half (ih (k := 2 * k)))
      · have hi := hasARun_prefix [x] (ih (k := k))
        simpa [eCount, hx, firstNormal] using hi

/--
@isnad1 id=not.1h1v.s3.65844698e353 from=translated src=- shape=e1534e72 vocab=109f7f9d
-/
theorem noAAA_not_hasARun_three {W : List A₂} (h : NoAAA W) :
    ¬ HasARun 3 W := by
  simpa [NoAAA, HasARun] using h

/-- The elementary but nontrivial run estimate invoked on page 50: destroying
a run of `run` many `a`'s while producing a first-block normal form with no
`aaa` requires at least `u` occurrences of `e` in the left context.-/
def LongRunRequirement (u run : ℕ) : Prop :=
  ∀ X Y,
    NoAAA (firstNormal (X ++ List.replicate run a ++ Y)) →
    u ≤ eCount X

/-- The quantitative assertion used on page 50.  The transposed long side
starts with `2t = 2 * 2^u` copies of `a`; if fewer than `u` priority letters
occur to its left, at least four consecutive `a`'s survive normalization.
@isnad1 id=longrunr.0h1v.s5.1a34c65052c0 from=translated src=- shape=6d03ee5b vocab=0f8ec1df
-/
theorem longRunRequirement_two_power (u : ℕ) :
    LongRunRequirement u (2 * 2 ^ u) := by
  intro X Y hnormal
  by_contra hbound
  have hlt : eCount X < u := Nat.lt_of_not_ge hbound
  have hpow : 2 ^ (eCount X + 2) ≤ 2 ^ (u + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hscale : 2 ^ eCount X * 4 ≤ 2 * 2 ^ u := by
    calc
      2 ^ eCount X * 4 = 2 ^ (eCount X + 2) := by
        rw [pow_add]
        congr
      _ ≤ 2 ^ (u + 1) := hpow
      _ = 2 * 2 ^ u := by simp [pow_succ, Nat.mul_comm]
  have hrep :
      List.replicate (2 * 2 ^ u) a ++ Y =
        List.replicate (2 ^ eCount X * 4) a ++
          (List.replicate (2 * 2 ^ u - 2 ^ eCount X * 4) a ++ Y) := by
    calc
      List.replicate (2 * 2 ^ u) a ++ Y =
          List.replicate
            (2 ^ eCount X * 4 + (2 * 2 ^ u - 2 ^ eCount X * 4)) a ++ Y := by
              rw [Nat.add_sub_of_le hscale]
      _ = List.replicate (2 ^ eCount X * 4) a ++
          (List.replicate (2 * 2 ^ u - 2 ^ eCount X * 4) a ++ Y) := by
            simp only [List.replicate_add, List.append_assoc]
  have hfour : HasARun 4
      (firstNormal (X ++ List.replicate (2 * 2 ^ u) a ++ Y)) := by
    rw [List.append_assoc, hrep, ← List.append_assoc]
    exact firstNormal_hasARun_scaled X
      (List.replicate (2 * 2 ^ u - 2 ^ eCount X * 4) a ++ Y) 4
  exact noAAA_not_hasARun_three hnormal
    (hasARun_of_le (by omega : 3 ≤ 4) hfour)

/-- The invariant furnished by equation (25): every reachable first priority
normal form remains in the binary code language and hence has no `aaa`.-/
def ReachableNoAAA (L M X : List A₂) : Prop :=
  ∀ W, ThueEq (stage₂System L M) X W → NoAAA (firstNormal W)

/-- The exact shape needed from the transposed words: the initial `2t` copies
of `a` and a final `b`.-/
def LongShape (run : ℕ) (W : List A₂) : Prop :=
  ∃ middle, W = List.replicate run a ++ middle ++ [b]

/-- Decode a long side with a residual `d` inside arbitrary contexts.
@isnad1 id=ex.1h4v.s7.fc167d378196 from=translated src=- shape=683ea014 vocab=a923da12
-/
theorem phi₂_residual_long_context {run : ℕ} {W : List A₂}
    (hshape : LongShape run W) (l : List (Fin 2)) (R : List A₂) :
    ∃ middle,
      phi₂ (l ++ rho₂ W ++ (0 : Fin 2) :: rho₂ R) =
        phi₂ l ++ List.replicate run a ++ middle ++ [a, e] ++ R := by
  obtain ⟨middle, rfl⟩ := hshape
  refine ⟨middle, ?_⟩
  have hblock :
      rho₂ (List.replicate run a ++ middle ++ [b]) ++ [(0 : Fin 2)] =
      rho₂ (List.replicate run a ++ middle ++ [a, e]) := by
    simp [rho₂, rho₂Letter, a, b, e, List.append_assoc]
  calc
    phi₂ (l ++ rho₂ (List.replicate run a ++ middle ++ [b]) ++
        (0 : Fin 2) :: rho₂ R) =
        phi₂ (l ++ (rho₂ (List.replicate run a ++ middle ++ [b]) ++
          [(0 : Fin 2)]) ++ rho₂ R) := by
          simp only [List.append_assoc, List.singleton_append]
    _ = phi₂ (l ++ rho₂ (List.replicate run a ++ middle ++ [a, e]) ++
          rho₂ R) := by rw [hblock]
    _ = phi₂ l ++ (List.replicate run a ++ middle ++ [a, e]) ++ R :=
      phi₂_context_rho₂ l _ R
    _ = phi₂ l ++ List.replicate run a ++ middle ++ [a, e] ++ R := by
      simp only [List.append_assoc]

/-! ### Excluding the residual decoder alignment -/

/-- If the two invariants isolated on page 50 hold, then an occurrence of
the long final relation cannot be followed by the residual unmatched `d`.
This is the counting core of the converse `T₃ → T₂`: the initial run of
`a`'s forces all `u` priority letters into the left context, while decoding
the residual `d` creates one additional `e`.
@isnad1 id=eq.8h8v.s8.26c265b1403c from=translated src=- shape=519f007e vocab=0444b927
-/
theorem long_aligned_of_decoded_reachable {u run : ℕ}
    {L M X : List A₂} {W : List (Fin 2)}
    (hLM : eCount L = eCount M)
    (hX : eCount X = u)
    (hNoAAA : ReachableNoAAA L M X)
    (hRun : LongRunRequirement u run)
    (hshapeL : LongShape run L)
    (hshapeM : LongShape run M)
    (hdecode : ThueEq (stage₂System L M) X (phi₂ W)) :
    ∀ l r,
      (W = l ++ rho₂ L ++ r ∨ W = l ++ rho₂ M ++ r) →
      rho₂ (phi₂ r) = r := by
  intro l r hocc
  rcases rho₂_phi₂_reconstruct r with hexact | hresidual
  · exact hexact
  · have hnormal : NoAAA (firstNormal (phi₂ W)) :=
      hNoAAA (phi₂ W) hdecode
    have hform : ∃ middle,
        phi₂ W = phi₂ l ++ List.replicate run a ++
          middle ++ [a, e] ++ phi₂ r := by
      rcases hocc with hocc | hocc
      · obtain ⟨middle, hmiddle⟩ :=
          phi₂_residual_long_context hshapeL l (phi₂ r)
        refine ⟨middle, ?_⟩
        calc
          phi₂ W = phi₂ (l ++ rho₂ L ++ r) := congrArg phi₂ hocc
          _ = phi₂ (l ++ rho₂ L ++
              (0 : Fin 2) :: rho₂ (phi₂ r)) := by rw [hresidual]
          _ = _ := hmiddle
      · obtain ⟨middle, hmiddle⟩ :=
          phi₂_residual_long_context hshapeM l (phi₂ r)
        refine ⟨middle, ?_⟩
        calc
          phi₂ W = phi₂ (l ++ rho₂ M ++ r) := congrArg phi₂ hocc
          _ = phi₂ (l ++ rho₂ M ++
              (0 : Fin 2) :: rho₂ (phi₂ r)) := by rw [hresidual]
          _ = _ := hmiddle
    obtain ⟨middle, hform⟩ := hform
    rw [hform] at hnormal
    have hleft : u ≤ eCount (phi₂ l) := by
      apply hRun (phi₂ l) (middle ++ [a, e] ++ phi₂ r)
      simpa only [List.append_assoc] using hnormal
    have hcount := stage₂Eq_eCount L M hLM hdecode
    rw [hX, hform] at hcount
    simp only [eCount_append, eCount_replicate_a, eCount_ae,
      Nat.add_zero] at hcount
    omega

/-- Simultaneously decode a final-system derivation and establish the
alignment invariant required for its next long-rule step.  The simultaneous
induction avoids any circularity: alignment at the current word decodes the
next step, and the decoded prefix derivation re-establishes alignment at the
new word by `long_aligned_of_decoded_reachable`.
@isnad1 id=and.7h6v.s8.41f9781370ac from=translated src=- shape=36fab73c vocab=d5901f23
-/
theorem final_decode_and_aligned {u run : ℕ}
    {L M X : List A₂} {W : List (Fin 2)}
    (hLM : eCount L = eCount M)
    (hX : eCount X = u)
    (hNoAAA : ReachableNoAAA L M X)
    (hRun : LongRunRequirement u run)
    (hshapeL : LongShape run L)
    (hshapeM : LongShape run M)
    (hfinal : ThueEq (baseSystem (rho₂ L) (rho₂ M)) (rho₂ X) W) :
    ThueEq (stage₂System L M) X (phi₂ W) ∧
      ∀ l r,
        (W = l ++ rho₂ L ++ r ∨ W = l ++ rho₂ M ++ r) →
        rho₂ (phi₂ r) = r := by
  induction hfinal with
  | refl =>
      have hdecode :
          ThueEq (stage₂System L M) X (phi₂ (rho₂ X)) := by
        rw [phi₂_rho₂]
        exact Relation.ReflTransGen.refl
      exact ⟨hdecode, long_aligned_of_decoded_reachable hLM hX hNoAAA
        hRun hshapeL hshapeM hdecode⟩
  | tail hab hbc ih =>
      have hstep : ThueEq (stage₂System L M) (phi₂ _) (phi₂ _) :=
        phi₂_step_of_long_aligned L M ih.2 hbc
      have hdecode := ih.1.trans hstep
      exact ⟨hdecode, long_aligned_of_decoded_reachable hLM hX hNoAAA
        hRun hshapeL hshapeM hdecode⟩

/-- The page-50 invariants imply the exact alignment predicate consumed by
the final-stage reflection theorem.
@isnad1 id=longrule.6h5v.s5.0e968112c59f from=translated src=- shape=1f5a9c31 vocab=4b0b672a
-/
theorem longRuleAlignedFrom_of_invariants {u run : ℕ}
    {L M X : List A₂}
    (hLM : eCount L = eCount M)
    (hX : eCount X = u)
    (hNoAAA : ReachableNoAAA L M X)
    (hRun : LongRunRequirement u run)
    (hshapeL : LongShape run L)
    (hshapeM : LongShape run M) :
    LongRuleAlignedFrom L M X := by
  intro W hfinal
  exact (final_decode_and_aligned hLM hX hNoAAA hRun
    hshapeL hshapeM hfinal).2

/-- A convenient conditional form of equivalence (10), with the two
priority invariants made explicit.
@isnad1 id=iff.6h6v.s6.f90ce78b7ddd from=translated src=- shape=89aefff8 vocab=d2cf4ff8
-/
theorem rho₂_iff_of_priority_invariants {u run : ℕ}
    {L M X : List A₂}
    (hLM : eCount L = eCount M)
    (hX : eCount X = u)
    (hNoAAA : ReachableNoAAA L M X)
    (hRun : LongRunRequirement u run)
    (hshapeL : LongShape run L)
    (hshapeM : LongShape run M) (Y : List A₂) :
    ThueEq (stage₂System L M) X Y ↔
      ThueEq (baseSystem (rho₂ L) (rho₂ M)) (rho₂ X) (rho₂ Y) := by
  apply rho₂_iff_of_longRuleAligned
  exact longRuleAlignedFrom_of_invariants hLM hX hNoAAA hRun
    hshapeL hshapeM

end Priority
end Matiyasevich1993
end Thue
end Undecidability
