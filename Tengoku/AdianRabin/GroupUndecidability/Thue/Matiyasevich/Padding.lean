import Tengoku.AdianRabin.GroupUndecidability.Thue.Matiyasevich.Reduction
import Tengoku.Seed.Data.List.MinMax

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Undecidability
namespace Thue
namespace Matiyasevich1993
namespace Padding

/-!
The first, padding, stage of Section 2.2 of Matiyasevich (1995).  Starting
from a finite system `T₀`, it adds one letter `d` and produces a system `T₁`
whose left sides all have one common positive length `p`, and whose right
sides all have the common length `q = p + 1`.
-/

variable {n r : ℕ}

/-- The new letter `a_{n+1}` in the paper.-/
def pad : Fin (n + 1) := Fin.last n

/-- The inclusion `A₀ ↪ A₁`.-/
def liftLetter (x : Fin n) : Fin (n + 1) := x.castSucc

/-- The homomorphic extension of `liftLetter`.-/
def liftWord (W : List (Fin n)) : List (Fin (n + 1)) :=
  W.map liftLetter

/--
@isnad1 id=eq.0h3v.s7.bfeb227d8237 from=translated src=- shape=74605ae0 vocab=cb928700
-/
@[simp] theorem liftWord_append (X Y : List (Fin n)) :
    liftWord (X ++ Y) = liftWord X ++ liftWord Y := by
  simp [liftWord]

/--
@isnad1 id=eq.0h2v.s4.e6e279dc8955 from=translated src=- shape=b6cad4f7 vocab=0d881dc1
-/
@[simp] theorem liftWord_length (W : List (Fin n)) :
    (liftWord W).length = W.length := by
  simp [liftWord]

/-- Delete every occurrence of the new padding letter.  This is `φ₀`.-/
def projectLetter (x : Fin (n + 1)) : Option (Fin n) :=
  Fin.lastCases none some x

def decode (W : List (Fin (n + 1))) : List (Fin n) :=
  W.filterMap projectLetter

/--
@isnad1 id=eq.0h1v.s3.8e70a9df3132 from=translated src=- shape=38d6f9b1 vocab=7a71b072
-/
@[simp] theorem projectLetter_pad : projectLetter (pad (n := n)) = none := by
  simp [projectLetter, pad]

/--
@isnad1 id=eq.0h2v.s4.78d3b381aba1 from=translated src=- shape=e515e695 vocab=1ff9dba5
-/
@[simp] theorem projectLetter_lift (x : Fin n) :
    projectLetter (liftLetter x) = some x := by
  simp [projectLetter, liftLetter]

/--
@isnad1 id=eq.0h3v.s7.7869d5077c45 from=translated src=- shape=894c900d vocab=fa64753b
-/
@[simp] theorem decode_append (X Y : List (Fin (n + 1))) :
    decode (X ++ Y) = decode X ++ decode Y := by
  simp [decode]

/--
@isnad1 id=eq.0h2v.s4.af9085e19236 from=translated src=- shape=60f8d03b vocab=a87df5e7
-/
@[simp] theorem decode_liftWord (W : List (Fin n)) :
    decode (liftWord W) = W := by
  induction W with
  | nil => rfl
  | cons x W ih => simp [liftWord, decode]

/--
@isnad1 id=eq.0h2v.s4.321e2b8a532c from=translated src=- shape=3a8fe518 vocab=1854b30e
-/
@[simp] theorem decode_replicate_pad (k : ℕ) :
    decode (List.replicate k (pad (n := n))) = [] := by
  induction k with
  | zero => rfl
  | succ k ih => simp [decode]

/-- A computable upper bound for every source-rule side length.-/
def sideBound (F E : Fin r → List (Fin n)) : ℕ :=
  (List.ofFn fun i => max (F i).length (E i).length).foldr max 0

/-- The common length of the left sides of `T₁`.-/
def p (F E : Fin r → List (Fin n)) : ℕ := sideBound F E + 1

/-- The common length of the right sides of `T₁`.-/
def q (F E : Fin r → List (Fin n)) : ℕ := p F E + 1

/--
@isnad1 id=lt.0h5v.s5.197530b8650f from=translated src=- shape=23a69ddc vocab=7faf1d34
-/
theorem F_length_lt_p (F E : Fin r → List (Fin n)) (i : Fin r) :
    (F i).length < p F E := by
  have hmem : max (F i).length (E i).length ∈
      List.ofFn (fun j => max (F j).length (E j).length) :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  have hle : (F i).length ≤ sideBound F E :=
    List.le_max_of_le hmem (Nat.le_max_left _ _)
  simp only [p]
  omega

/--
@isnad1 id=lt.0h5v.s5.b078034523de from=translated src=- shape=7e052996 vocab=7faf1d34
-/
theorem E_length_lt_p (F E : Fin r → List (Fin n)) (i : Fin r) :
    (E i).length < p F E := by
  have hmem : max (F i).length (E i).length ∈
      List.ofFn (fun j => max (F j).length (E j).length) :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  have hle : (E i).length ≤ sideBound F E :=
    List.le_max_of_le hmem (Nat.le_max_right _ _)
  simp only [p]
  omega

/--
@isnad1 id=lt.0h4v.s4.8f9e67bb9490 from=translated src=- shape=1c2dba3e vocab=5f6b9977
-/
theorem p_pos (F E : Fin r → List (Fin n)) : 0 < p F E := by
  simp [p]

/--
@isnad1 id=le.0h4v.s4.8da46dbf8a2e from=translated src=- shape=41cf4cd7 vocab=d6628a24
-/
theorem p_le_q (F E : Fin r → List (Fin n)) : p F E ≤ q F E := by
  simp [q]

/-- Relations (16) and the left sides of relations (17).-/
def stage₁F (F E : Fin r → List (Fin n)) :
    Fin (r + (n + 1)) → List (Fin (n + 1)) :=
  Fin.addCases
    (fun i => liftWord (F i) ++
      List.replicate (p F E - (F i).length) pad)
    (fun j => [j] ++ List.replicate (p F E - 1) pad)

/-- Relations (16) and the right sides of relations (17).-/
def stage₁E (F E : Fin r → List (Fin n)) :
    Fin (r + (n + 1)) → List (Fin (n + 1)) :=
  Fin.addCases
    (fun i => liftWord (E i) ++
      List.replicate (q F E - (E i).length) pad)
    (fun j => [pad, j] ++ List.replicate (q F E - 2) pad)

def stage₁System (F E : Fin r → List (Fin n)) :
    ThueSystem (Fin (n + 1)) :=
  finiteSystem (stage₁F F E) (stage₁E F E)

/-- `τ₀(G) = ρ₀(G)d^q`, equation (11) for the first stage.-/
def encode (F E : Fin r → List (Fin n)) (W : List (Fin n)) :
    List (Fin (n + 1)) :=
  liftWord W ++ List.replicate (q F E) pad

/--
@isnad1 id=eq.0h5v.s5.512c1cd65e41 from=translated src=- shape=a683dcee vocab=b922836d
-/
@[simp] theorem decode_encode (F E : Fin r → List (Fin n))
    (W : List (Fin n)) : decode (encode F E W) = W := by
  simp [encode]

/--
@isnad1 id=computab.0h4v.s6.5427ea436fa5 from=translated src=- shape=1fdd3b7f vocab=5a1ae904
-/
theorem encode_computable (F E : Fin r → List (Fin n)) :
    Computable (encode F E) := by
  have hlift : Primrec (liftWord : List (Fin n) → List (Fin (n + 1))) :=
    Primrec.list_map Primrec.id
      ((Primrec.dom_finite liftLetter).comp₂ Primrec₂.right)
  exact (Primrec.list_append.comp hlift
    (Primrec.const (List.replicate (q F E) (pad (n := n))))).to_comp

/--
@isnad1 id=eq.0h5v.s7.5512e01ea0db from=translated src=- shape=dc107453 vocab=798548cf
-/
@[simp] theorem stage₁F_primary (F E : Fin r → List (Fin n)) (i : Fin r) :
    stage₁F F E (Fin.castAdd (n + 1) i) =
      liftWord (F i) ++ List.replicate (p F E - (F i).length) pad := by
  simp [stage₁F]

/--
@isnad1 id=eq.0h5v.s7.c23e179617a6 from=translated src=- shape=920407cd vocab=404f736a
-/
@[simp] theorem stage₁E_primary (F E : Fin r → List (Fin n)) (i : Fin r) :
    stage₁E F E (Fin.castAdd (n + 1) i) =
      liftWord (E i) ++ List.replicate (q F E - (E i).length) pad := by
  simp [stage₁E]

/--
@isnad1 id=eq.0h5v.s7.8aed28e5df60 from=translated src=- shape=ad75e99a vocab=ef4c5101
-/
@[simp] theorem stage₁F_shift (F E : Fin r → List (Fin n))
    (j : Fin (n + 1)) :
    stage₁F F E (Fin.natAdd r j) =
      [j] ++ List.replicate (p F E - 1) pad := by
  simp [stage₁F]

/--
@isnad1 id=eq.0h5v.s7.b64bda8a6772 from=translated src=- shape=8c1e6871 vocab=b2442ee2
-/
@[simp] theorem stage₁E_shift (F E : Fin r → List (Fin n))
    (j : Fin (n + 1)) :
    stage₁E F E (Fin.natAdd r j) =
      [pad, j] ++ List.replicate (q F E - 2) pad := by
  simp [stage₁E]

/--
@isnad1 id=eq.0h5v.s6.afb1e62200dd from=translated src=- shape=8a768de9 vocab=ef3a0c3e
-/
theorem stage₁F_length (F E : Fin r → List (Fin n))
    (i : Fin (r + (n + 1))) : (stage₁F F E i).length = p F E := by
  induction i using Fin.addCases with
  | left i =>
      simp only [stage₁F_primary, List.length_append, liftWord_length,
        List.length_replicate]
      have := F_length_lt_p F E i
      omega
  | right j =>
      simp only [stage₁F_shift, List.length_append, List.length_cons,
        List.length_nil, List.length_replicate]
      have := p_pos F E
      omega

/--
@isnad1 id=eq.0h5v.s6.495c06562368 from=translated src=- shape=8a768de9 vocab=909b4043
-/
theorem stage₁E_length (F E : Fin r → List (Fin n))
    (i : Fin (r + (n + 1))) : (stage₁E F E i).length = q F E := by
  induction i using Fin.addCases with
  | left i =>
      simp only [stage₁E_primary, List.length_append, liftWord_length,
        List.length_replicate]
      have := E_length_lt_p F E i
      simp only [q]
      omega
  | right j =>
      simp only [stage₁E_shift, List.length_append, List.length_cons,
        List.length_nil, List.length_replicate]
      have := p_pos F E
      simp only [q]
      omega

@[simp] private theorem stage₁F_pad (F E : Fin r → List (Fin n)) :
    stage₁F F E (Fin.natAdd r (pad (n := n))) =
      List.replicate (p F E) pad := by
  rw [stage₁F_shift]
  simp only [List.singleton_append]
  rw [← List.replicate_succ]
  congr 1

@[simp] private theorem stage₁E_pad (F E : Fin r → List (Fin n)) :
    stage₁E F E (Fin.natAdd r (pad (n := n))) =
      List.replicate (q F E) pad := by
  rw [stage₁E_shift]
  simp only [List.cons_append, List.nil_append]
  rw [← List.replicate_succ, ← List.replicate_succ]
  congr 1

/-- The padding-only instance of (17) changes a run of at least `p` padding
letters into the run one letter longer.-/
private theorem pad_run_step (F E : Fin r → List (Fin n)) (k : ℕ)
    (hk : p F E ≤ k) :
    ThueStep (stage₁System F E)
      (List.replicate k pad) (List.replicate (k + 1) pad) := by
  let rest := k - p F E
  refine ⟨[], List.replicate rest pad,
    stage₁F F E (Fin.natAdd r (pad (n := n))),
    stage₁E F E (Fin.natAdd r (pad (n := n))),
    ⟨Fin.natAdd r (pad (n := n)), rfl⟩, Or.inl ⟨?_, ?_⟩⟩
  · simp only [List.nil_append, stage₁F_pad, ← List.replicate_add]
    congr 1
    simp only [rest]
    omega
  · simp only [List.nil_append, stage₁E_pad, ← List.replicate_add]
    congr 1
    simp only [rest, q]
    omega

/-- A run of at least `p` padding letters can be lengthened arbitrarily.-/
private theorem pad_grow (F E : Fin r → List (Fin n)) (k t : ℕ)
    (hk : p F E ≤ k) :
    ThueEq (stage₁System F E)
      (List.replicate k pad) (List.replicate (k + t) pad) := by
  change Relation.ReflTransGen (ThueStep (stage₁System F E)) _ _
  induction t with
  | zero => simp only [Nat.add_zero]; exact Relation.ReflTransGen.refl
  | succ t ih =>
      have hkt : p F E ≤ k + t := hk.trans (Nat.le_add_right k t)
      have hs := pad_run_step F E (k + t) hkt
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using ih.tail hs

/-- A padded copy of a source relation rewrites with an arbitrary right
context.-/
private theorem primary_step (F E : Fin r → List (Fin n)) (i : Fin r)
    (s : List (Fin (n + 1))) :
    ThueStep (stage₁System F E)
      (stage₁F F E (Fin.castAdd (n + 1) i) ++ s)
      (stage₁E F E (Fin.castAdd (n + 1) i) ++ s) :=
  ⟨[], s,
    stage₁F F E (Fin.castAdd (n + 1) i),
    stage₁E F E (Fin.castAdd (n + 1) i),
    ⟨Fin.castAdd (n + 1) i, rfl⟩,
    Or.inl ⟨by simp, by simp⟩⟩

/-- One source rule can be applied immediately before the terminal block
`d^q`.  Extra padding is first created, then removed after relation (16).-/
private theorem source_rule_at_suffix (F E : Fin r → List (Fin n))
    (i : Fin r) :
    ThueEq (stage₁System F E)
      (liftWord (F i) ++ List.replicate (q F E) pad)
      (liftWord (E i) ++ List.replicate (q F E) pad) := by
  let N := q F E + (E i).length
  let K := q F E + ((F i).length + 1)
  have hpq : p F E ≤ q F E := p_le_q F E
  have h₁raw := thueEq_context (liftWord (F i)) []
    (pad_grow F E (q F E) (E i).length hpq)
  have h₁ : ThueEq (stage₁System F E)
      (liftWord (F i) ++ List.replicate (q F E) pad)
      (liftWord (F i) ++ List.replicate N pad) := by
    simpa only [List.append_nil, N] using h₁raw
  let rest := N - (p F E - (F i).length)
  have hrest : p F E - (F i).length ≤ N := by
    have := F_length_lt_p F E i
    dsimp only [N]
    omega
  have hleft :
      stage₁F F E (Fin.castAdd (n + 1) i) ++
          List.replicate rest pad =
        liftWord (F i) ++ List.replicate N pad := by
    rw [stage₁F_primary, List.append_assoc, ← List.replicate_add]
    congr 2
    dsimp only [rest]
    omega
  have hright :
      stage₁E F E (Fin.castAdd (n + 1) i) ++
          List.replicate rest pad =
        liftWord (E i) ++ List.replicate K pad := by
    rw [stage₁E_primary, List.append_assoc, ← List.replicate_add]
    congr 2
    have hF := F_length_lt_p F E i
    have hE := E_length_lt_p F E i
    dsimp only [rest, N, K, q]
    omega
  have h₂ : ThueEq (stage₁System F E)
      (liftWord (F i) ++ List.replicate N pad)
      (liftWord (E i) ++ List.replicate K pad) := by
    change Relation.ReflTransGen (ThueStep (stage₁System F E)) _ _
    exact Relation.ReflTransGen.single
      (hleft ▸ hright ▸ primary_step F E i (List.replicate rest pad))
  have hgrowK := pad_grow F E (q F E) ((F i).length + 1) hpq
  have h₃raw := thueEq_context (liftWord (E i)) [] (thueEq_symm hgrowK)
  have h₃ : ThueEq (stage₁System F E)
      (liftWord (E i) ++ List.replicate K pad)
      (liftWord (E i) ++ List.replicate (q F E) pad) := by
    simpa only [List.append_nil, K] using h₃raw
  exact (h₁.trans h₂).trans h₃

/-- One use of relation (17) moves one fresh padding letter from immediately
after `j` to immediately before it, while preserving the terminal `d^q`.-/
private theorem shift_step (F E : Fin r → List (Fin n))
    (j : Fin (n + 1)) (k : ℕ) :
    ThueStep (stage₁System F E)
      (List.replicate k pad ++ [j] ++ List.replicate (q F E) pad)
      (List.replicate (k + 1) pad ++ [j] ++
        List.replicate (q F E) pad) := by
  have hleftTail :
      List.replicate (p F E - 1) (pad (n := n)) ++
          List.replicate 2 (pad (n := n)) =
        List.replicate (q F E) (pad (n := n)) := by
    rw [← List.replicate_add]
    congr 1
  have hrightTail :
      List.replicate (q F E - 2) (pad (n := n)) ++
          List.replicate 2 (pad (n := n)) =
        List.replicate (q F E) (pad (n := n)) := by
    rw [← List.replicate_add]
    congr 1
  have hprefix :
      List.replicate k (pad (n := n)) ++ [pad (n := n), j] =
        List.replicate (k + 1) (pad (n := n)) ++ [j] := by
    rw [List.replicate_add]
    simp only [List.replicate_one, List.singleton_append,
      List.append_assoc]
  let idx := Fin.natAdd r j
  refine ⟨List.replicate k (pad (n := n)),
    List.replicate 2 (pad (n := n)),
    stage₁F F E idx, stage₁E F E idx, ⟨idx, rfl⟩,
    Or.inl ⟨?_, ?_⟩⟩
  · dsimp only [idx]
    rw [stage₁F_shift]
    simp only [List.append_assoc]
    rw [hleftTail]
  · dsimp only [idx]
    rw [stage₁E_shift]
    simp only [List.append_assoc]
    rw [hrightTail]
    simpa only [List.append_assoc] using congrArg
      (fun z => z ++ List.replicate (q F E) (pad (n := n))) hprefix.symm

/-- Iterating (17) creates `t` padding letters before a letter.-/
private theorem shift_letter_aux (F E : Fin r → List (Fin n))
    (j : Fin (n + 1)) (t : ℕ) :
    ThueEq (stage₁System F E)
      ([j] ++ List.replicate (q F E) pad)
      (List.replicate t pad ++ [j] ++ List.replicate (q F E) pad) := by
  change Relation.ReflTransGen (ThueStep (stage₁System F E)) _ _
  induction t with
  | zero => simpa using
      (Relation.ReflTransGen.refl :
        Relation.ReflTransGen (ThueStep (stage₁System F E))
          ([j] ++ List.replicate (q F E) pad)
          ([j] ++ List.replicate (q F E) pad))
  | succ t ih =>
      have hs := shift_step F E j t
      simpa only [Nat.succ_eq_add_one] using ih.tail hs

/-- The displayed consequence of (17) on page 47:
`j d^q ↔* d^q j d^q`.-/
private theorem shift_letter (F E : Fin r → List (Fin n))
    (j : Fin (n + 1)) :
    ThueEq (stage₁System F E)
      ([j] ++ List.replicate (q F E) pad)
      (List.replicate (q F E) pad ++ [j] ++
        List.replicate (q F E) pad) :=
  shift_letter_aux F E j (q F E)

/-- Padding can be brought in front of an arbitrary suffix.  The intermediate
word `W'` is deliberately existential, exactly as on page 47.-/
private theorem expose_suffix (F E : Fin r → List (Fin n))
    (W : List (Fin (n + 1))) :
    ∃ W' : List (Fin (n + 1)),
      ThueEq (stage₁System F E)
        (W ++ List.replicate (q F E) pad)
        (List.replicate (q F E) pad ++ W' ++
          List.replicate (q F E) pad) := by
  induction W with
  | nil =>
      refine ⟨[], ?_⟩
      have hg := pad_grow F E (q F E) (q F E) (p_le_q F E)
      simpa only [List.nil_append, List.append_nil, ← List.replicate_add] using hg
  | cons j W ih =>
      obtain ⟨W', hW⟩ := ih
      refine ⟨[j] ++ List.replicate (q F E) pad ++ W', ?_⟩
      have h₁raw := thueEq_context [j] [] hW
      have h₁ : ThueEq (stage₁System F E)
          ((j :: W) ++ List.replicate (q F E) pad)
          ([j] ++ List.replicate (q F E) pad ++ W' ++
            List.replicate (q F E) pad) := by
        simpa only [List.cons_append, List.singleton_append, List.append_nil,
          List.nil_append, List.append_assoc] using h₁raw
      have h₂raw := thueEq_context []
        (W' ++ List.replicate (q F E) pad) (shift_letter F E j)
      have h₂ : ThueEq (stage₁System F E)
          ([j] ++ List.replicate (q F E) pad ++ W' ++
            List.replicate (q F E) pad)
          (List.replicate (q F E) pad ++
            ([j] ++ List.replicate (q F E) pad ++ W') ++
            List.replicate (q F E) pad) := by
        simpa only [List.nil_append, List.append_assoc] using h₂raw
      exact h₁.trans h₂

/-- Forward simulation of one explicitly chosen source relation.-/
private theorem simulate_rule (F E : Fin r → List (Fin n))
    (i : Fin r) (l s : List (Fin n)) :
    ThueEq (stage₁System F E)
      (encode F E (l ++ F i ++ s))
      (encode F E (l ++ E i ++ s)) := by
  obtain ⟨W', hW⟩ := expose_suffix F E (liftWord s)
  have h₁raw := thueEq_context (liftWord l ++ liftWord (F i)) [] hW
  have h₁ : ThueEq (stage₁System F E)
      (encode F E (l ++ F i ++ s))
      (liftWord l ++ liftWord (F i) ++ List.replicate (q F E) pad ++
        W' ++ List.replicate (q F E) pad) := by
    simpa only [encode, liftWord_append, List.append_nil,
      List.append_assoc] using h₁raw
  have h₂raw := thueEq_context (liftWord l)
    (W' ++ List.replicate (q F E) pad) (source_rule_at_suffix F E i)
  have h₂ : ThueEq (stage₁System F E)
      (liftWord l ++ liftWord (F i) ++ List.replicate (q F E) pad ++
        W' ++ List.replicate (q F E) pad)
      (liftWord l ++ liftWord (E i) ++ List.replicate (q F E) pad ++
        W' ++ List.replicate (q F E) pad) := by
    simpa only [List.append_assoc] using h₂raw
  have h₃raw := thueEq_context (liftWord l ++ liftWord (E i)) []
    (thueEq_symm hW)
  have h₃ : ThueEq (stage₁System F E)
      (liftWord l ++ liftWord (E i) ++ List.replicate (q F E) pad ++
        W' ++ List.replicate (q F E) pad)
      (encode F E (l ++ E i ++ s)) := by
    simpa only [encode, liftWord_append, List.append_nil,
      List.append_assoc] using h₃raw
  exact (h₁.trans h₂).trans h₃

/-- Forward simulation of one arbitrary `T₀` step.
@isnad1 id=thueeq.1h6v.s6.3278b75f5ec1 from=translated src=- shape=deb35a35 vocab=bfe489a6
-/
theorem simulate_step (F E : Fin r → List (Fin n))
    {X Y : List (Fin n)} (h : ThueStep (finiteSystem F E) X Y) :
    ThueEq (stage₁System F E) (encode F E X) (encode F E Y) := by
  rcases h with ⟨l, s, x, y, ⟨i, hxy⟩, hwords⟩
  injection hxy with hx hy
  subst x
  subst y
  rcases hwords with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact simulate_rule F E i l s
  · exact thueEq_symm (simulate_rule F E i l s)

/-- Forward half of equivalence (10) for all derivations.
@isnad1 id=thueeq.1h6v.s6.577c7af6b99c from=translated src=- shape=ea234727 vocab=cc20be72
-/
theorem simulate (F E : Fin r → List (Fin n)) {X Y : List (Fin n)}
    (h : ThueEq (finiteSystem F E) X Y) :
    ThueEq (stage₁System F E) (encode F E X) (encode F E Y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.trans (simulate_step F E hstep)

private theorem source_rule_step (F E : Fin r → List (Fin n)) (i : Fin r)
    (l s : List (Fin n)) :
    ThueStep (finiteSystem F E)
      (l ++ F i ++ s) (l ++ E i ++ s) :=
  ⟨l, s, F i, E i, ⟨i, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩

private theorem decode_shift_sides (F E : Fin r → List (Fin n))
    (j : Fin (n + 1)) :
    decode (stage₁F F E (Fin.natAdd r j)) =
      decode (stage₁E F E (Fin.natAdd r j)) := by
  rw [stage₁F_shift, stage₁E_shift, decode_append, decode_append,
    decode_replicate_pad, decode_replicate_pad]
  simp [decode]

/-- Every first-stage rewrite decodes either to one source rewrite or to an
identity.  This is the argument in the last paragraph of Section 2.2.
@isnad1 id=thueeq.1h6v.s6.c1df26310cd3 from=translated src=- shape=4f133d46 vocab=23c6fa3d
-/
theorem decode_step (F E : Fin r → List (Fin n))
    {X Y : List (Fin (n + 1))}
    (h : ThueStep (stage₁System F E) X Y) :
    ThueEq (finiteSystem F E) (decode X) (decode Y) := by
  rcases h with ⟨l, s, x, y, ⟨i, hxy⟩, hwords⟩
  injection hxy with hx hy
  subst x
  subst y
  induction i using Fin.addCases with
  | left i =>
      rcases hwords with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · change Relation.ReflTransGen (ThueStep (finiteSystem F E))
          (decode (l ++ stage₁F F E (Fin.castAdd (n + 1) i) ++ s))
          (decode (l ++ stage₁E F E (Fin.castAdd (n + 1) i) ++ s))
        simpa only [decode_append, stage₁F_primary, stage₁E_primary,
          decode_liftWord, decode_replicate_pad, List.append_nil,
          List.nil_append, List.append_assoc] using Relation.ReflTransGen.single
            (source_rule_step F E i (decode l) (decode s))
      · change Relation.ReflTransGen (ThueStep (finiteSystem F E))
          (decode (l ++ stage₁E F E (Fin.castAdd (n + 1) i) ++ s))
          (decode (l ++ stage₁F F E (Fin.castAdd (n + 1) i) ++ s))
        have hstep : ThueStep (finiteSystem F E)
            (decode l ++ E i ++ decode s)
            (decode l ++ F i ++ decode s) :=
          ⟨decode l, decode s, F i, E i, ⟨i, rfl⟩,
            Or.inr ⟨rfl, rfl⟩⟩
        have hpath := Relation.ReflTransGen.single hstep
        simpa only [decode_append, stage₁F_primary, stage₁E_primary,
          decode_liftWord, decode_replicate_pad, List.append_nil,
          List.nil_append, List.append_assoc] using hpath
  | right j =>
      rcases hwords with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · change Relation.ReflTransGen (ThueStep (finiteSystem F E)) _ _
        have heq := decode_shift_sides F E j
        rw [decode_append, decode_append, decode_append, decode_append, heq]
      · change Relation.ReflTransGen (ThueStep (finiteSystem F E)) _ _
        have heq := decode_shift_sides F E j
        rw [decode_append, decode_append, decode_append, decode_append, heq]

/-- `φ₀` maps an entire first-stage derivation to a source derivation.
@isnad1 id=thueeq.1h6v.s6.d259a78dcc19 from=translated src=- shape=ee5c52c0 vocab=56ae9bd0
-/
theorem decode_thueEq (F E : Fin r → List (Fin n))
    {X Y : List (Fin (n + 1))}
    (h : ThueEq (stage₁System F E) X Y) :
    ThueEq (finiteSystem F E) (decode X) (decode Y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.trans (decode_step F E hstep)

/-- Reflection half of equivalence (10) for the padding stage.
@isnad1 id=thueeq.1h6v.s6.7dd5923ad1cb from=translated src=- shape=7d69bed6 vocab=cc20be72
-/
theorem reflect (F E : Fin r → List (Fin n)) {X Y : List (Fin n)}
    (h : ThueEq (stage₁System F E) (encode F E X) (encode F E Y)) :
    ThueEq (finiteSystem F E) X Y := by
  simpa using decode_thueEq F E h

/-- The complete first-stage instance of equivalence (10).-/
def embedding (F E : Fin r → List (Fin n)) :
    Embedding (finiteSystem F E) (stage₁System F E) where
  encode := encode F E
  encode_computable := encode_computable F E
  thueEq_iff := fun _ _ => ⟨simulate F E, reflect F E⟩

end Padding
end Matiyasevich1993
end Thue
end Undecidability
