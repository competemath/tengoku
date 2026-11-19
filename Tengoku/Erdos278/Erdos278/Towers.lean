import Tengoku.Erdos278.Erdos278.Core
import Tengoku.Seed.Data.Fintype.EquivFin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos278

/-- Every fiber with at most p children admits p distinct digit labels.
The ordered pair of parent and digit uniquely identifies the child.-/
theorem fiber_digits {P C : Type*} [Fintype C] [DecidableEq P]
    (parent : C → P) (p : ℕ)
    (h : ∀ b, Fintype.card {c : C // parent c = b} ≤ p) :
    ∃ digit : C → Fin p, Function.Injective (fun c => (parent c, digit c)) := by
  classical
  have he (b : P) : Nonempty ({c : C // parent c = b} ↪ Fin p) :=
    Function.Embedding.nonempty_of_card_le (by simpa using h b)
  let enc (b : P) : {c : C // parent c = b} ↪ Fin p := Classical.choice (he b)
  let paired : C ↪ P × Fin p :=
    ((Equiv.sigmaFiberEquiv parent).symm.toEmbedding.trans
      (Function.Embedding.sigmaMap (Function.Embedding.refl P) enc)).trans
        (Equiv.sigmaEquivProd P (Fin p)).toEmbedding
  refine ⟨fun c => (paired c).2, ?_⟩
  intro c d hcd
  exact paired.injective hcd

/-- Blocks are the parts of the prescribed partitions. A parent map records
nested refinement; allowing parents with no children handles shrinking domains.
The virtual root is a subsingleton level B 0. No primality is needed: the theorem
holds for any positive radix p.-/
def TowerAdmissible (B : ℕ → Type*) [∀ k, Fintype (B k)]
    [∀ k, DecidableEq (B k)] (parent : ∀ k, B (k+1) → B k) (p : ℕ) : Prop :=
  ∀ k b, Fintype.card {c : B (k+1) // parent k c = b} ≤ p

def TowerRealized (B : ℕ → Type*) (parent : ∀ k, B (k+1) → B k) (p : ℕ) : Prop :=
  ∃ code : ∀ k, B k → ℕ,
    (∀ k b, code k b < p ^ k) ∧
    (∀ k, Function.Injective (code k)) ∧
    (∀ k c, code (k+1) c % p^k = code k (parent k c))

def towerCode {B : ℕ → Type*} (parent : ∀ k, B (k+1) → B k)
    {p : ℕ} (digit : ∀ k, B (k+1) → Fin p) : ∀ k, B k → ℕ
  | 0, _ => 0
  | k+1, c => towerCode parent digit k (parent k c) + p^k * (digit k c).val

/-- The repaired local realizability theorem, in a representation by block
types and parent maps. Refinement is the existence of those parent maps.-/
theorem corrected_tower_realizability (B : ℕ → Type*)
    [∀ k, Fintype (B k)] [∀ k, DecidableEq (B k)] [Subsingleton (B 0)]
    (parent : ∀ k, B (k+1) → B k) (p : ℕ) (hp : 0 < p) :
    TowerAdmissible B parent p ↔ TowerRealized B parent p := by
  classical
  constructor
  · intro h
    have hd (k : ℕ) := fiber_digits (parent k) p (h k)
    let digit (k : ℕ) : B (k+1) → Fin p := Classical.choose (hd k)
    have hdi (k : ℕ) : Function.Injective (fun c => (parent k c, digit k c)) :=
      Classical.choose_spec (hd k)
    let code := towerCode parent digit
    have hb : ∀ k b, code k b < p^k := by
      intro k
      induction k with
      | zero => intro b; simp [code, towerCode]
      | succ k ih =>
        intro c
        have hprev := ih (parent k c)
        have hdigit := (digit k c).isLt
        have hpow : 0 < p^k := pow_pos hp k
        dsimp [code, towerCode] at *
        rw [pow_succ]
        nlinarith
    have hm : ∀ k c, code (k+1) c % p^k = code k (parent k c) := by
      intro k c
      dsimp [code, towerCode]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hb k (parent k c))]
    have hi : ∀ k, Function.Injective (code k) := by
      intro k
      induction k with
      | zero => intro b c _; exact Subsingleton.elim b c
      | succ k ih =>
        intro b c heq
        have hmod := congrArg (fun t => t % p^k) heq
        rw [hm, hm] at hmod
        have hparent := ih hmod
        have hv : (digit k b).val = (digit k c).val := by
          have hpow : 0 < p^k := pow_pos hp k
          change code k (parent k b) + p^k * (digit k b).val =
            code k (parent k c) + p^k * (digit k c).val at heq
          rw [hparent] at heq
          nlinarith
        exact hdi k (Prod.ext hparent (Fin.ext hv))
    exact ⟨code, hb, hi, hm⟩
  · rintro ⟨code, hb, hi, hm⟩ k b
    let enc : {c : B (k+1) // parent k c = b} → Fin p := fun c =>
      ⟨code (k+1) c.1 / p^k, by
        apply (Nat.div_lt_iff_lt_mul (pow_pos hp k)).mpr
        simpa [pow_succ, Nat.mul_comm] using hb (k+1) c.1⟩
    have he : Function.Injective enc := by
      intro c d heq
      have hdiv : code (k+1) c.1 / p^k = code (k+1) d.1 / p^k :=
        congrArg Fin.val heq
      have hmod : code (k+1) c.1 % p^k = code (k+1) d.1 % p^k := by
        rw [hm, hm, c.2, d.2]
      apply Subtype.ext
      apply hi (k+1)
      have hc := Nat.mod_add_div (code (k+1) c.1) (p^k)
      have hd := Nat.mod_add_div (code (k+1) d.1) (p^k)
      rw [hmod, hdiv] at hc
      exact hc.symm.trans hd
    simpa using Fintype.card_le_of_injective enc he

/-- Any realization has at most p first-level blocks. This is the missing
root-capacity condition in the previous manuscript.-/
theorem root_capacity (B : ℕ → Type*) [Fintype (B 1)]
    (parent : ∀ k, B (k+1) → B k) (p : ℕ)
    (h : TowerRealized B parent p) : Fintype.card (B 1) ≤ p := by
  obtain ⟨code, hb, hi, _⟩ := h
  let f : B 1 → Fin p := fun b => ⟨code 1 b, by simpa using hb 1 b⟩
  have hinj : Function.Injective f := fun _ _ h => hi 1 (congrArg Fin.val h)
  simpa using Fintype.card_le_of_injective f hinj

/-- Coherence along a vertex's path: its chosen terminal residue induces the
prescribed block at every shallower level. Paths may stop at different depths.-/
theorem tower_path_residue {B : ℕ → Type*} {parent : ∀ k, B (k+1) → B k}
    {p : ℕ} (code : ∀ k, B k → ℕ)
    (hb : ∀ k b, code k b < p^k)
    (hm : ∀ k c, code (k+1) c % p^k = code k (parent k c))
    (d : ℕ) (path : ∀ k, k ≤ d → B k)
    (hpath : ∀ k (hk : k+1 ≤ d), parent k (path (k+1) hk) =
      path k (Nat.le_trans (Nat.le_succ k) hk)) (k : ℕ) (hk : k ≤ d) :
    code d (path d le_rfl) % p^k = code k (path k hk) := by
  have aux : ∀ j (hkj : k ≤ j) (hjd : j ≤ d),
      code j (path j hjd) % p^k = code k (path k hk) := by
    intro j hkj
    induction j, hkj using Nat.le_induction with
    | base => intro hkd; exact Nat.mod_eq_of_lt (hb k _)
    | succ j hkj ih =>
      intro hjd
      have hdiv : p^k ∣ p^j := pow_dvd_pow p hkj
      rw [← Nat.mod_mod_of_dvd (code (j+1) (path (j+1) hjd)) hdiv,
        hm, hpath j hjd]
      exact ih (Nat.le_trans (Nat.le_succ j) hjd)
  exact aux d hk le_rfl

/-- Terminal residues agree mod p^k exactly when the two paths occupy the
same level-k block, even when their terminal depths differ.-/
theorem tower_paths_agree_iff {B : ℕ → Type*} {parent : ∀ k, B (k+1) → B k}
    {p : ℕ} (code : ∀ k, B k → ℕ)
    (hb : ∀ k b, code k b < p^k) (hi : ∀ k, Function.Injective (code k))
    (hm : ∀ k c, code (k+1) c % p^k = code k (parent k c))
    (d e : ℕ) (path : ∀ k, k ≤ d → B k) (path' : ∀ k, k ≤ e → B k)
    (hpath : ∀ k (hk : k+1 ≤ d), parent k (path (k+1) hk) =
      path k (Nat.le_trans (Nat.le_succ k) hk))
    (hpath' : ∀ k (hk : k+1 ≤ e), parent k (path' (k+1) hk) =
      path' k (Nat.le_trans (Nat.le_succ k) hk))
    (k : ℕ) (hkd : k ≤ d) (hke : k ≤ e) :
    code d (path d le_rfl) ≡ code e (path' e le_rfl) [MOD p^k] ↔
      path k hkd = path' k hke := by
  rw [Nat.ModEq, tower_path_residue code hb hm d path hpath k hkd,
    tower_path_residue code hb hm e path' hpath' k hke]
  exact (hi k).eq_iff

/-- Local coordinates with pairwise coprime moduli have no gluing obstruction.
Applied to distinct prime powers, this is the global CRT step in section 5.-/
theorem coprime_local_gluing {α : Type*} [DecidableEq α]
    (s : Finset α) (n : α → ℕ) (hn : ∀ i ∈ s, n i ≠ 0) (a : α → ℤ)
    (hc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (n i).Coprime (n j)) :
    ∃ z : ℤ, ∀ i ∈ s, z ≡ a i [ZMOD n i] := by
  apply (generalized_crt s n a hn).mpr
  intro i hi j hj
  by_cases hij : i = j
  · subst j; exact Int.ModEq.refl _
  · unfold Compatible
    rw [(hc i hi j hj hij).gcd_eq_one]
    simp [Int.ModEq]

theorem three_blocks_cannot_fit_two_residues :
    ¬ ∃ a : Fin 3 → Fin 2, Function.Injective a := by
  rintro ⟨a, ha⟩
  have := Fintype.card_le_of_injective a ha
  norm_num at this

end Erdos278
