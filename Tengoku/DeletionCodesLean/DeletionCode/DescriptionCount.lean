import Tengoku.Seed.Data.Fintype.BigOperators
import Tengoku.Seed.Tactic.GCongr
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms description_card` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms description_bound` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Finite description-space bound checked with Lean 4.34.0.
RecordSerialization implements and verifies this format. GeneratingCount and
SignedRuleCount transfer the bound to decoded words and signed rule sets;
ManuscriptCounting supplies the catalogue-level counting theorem.
-/
namespace DeletionCode.DescriptionCount

def fieldBound (L ν : ℕ) : ℕ := 16 * L * (ν + 1)

/--
Root positions; headers; root names; padded instructions with 12 fields.
RecordCodec verifies the twelve-field instruction serialization.-/
abbrev Description (n L ν c : ℕ) :=
  (Fin c → Fin n) × (Fin ν → Fin (4 * L)) × (Fin c → Fin ν) ×
  (Fin (4 * ν) → (Fin 12 → Fin (fieldBound L ν)))

/--
@isnad1 id=eq.0h4v.s8.c8224bde6a0e from=translated src=- shape=c70e4b7b vocab=2f72ac77
-/
theorem description_card (n L ν c : ℕ) :
    Fintype.card (Description n L ν c) =
      n ^ c * (4 * L) ^ ν * ν ^ c * ((fieldBound L ν) ^ 12) ^ (4 * ν) := by
  simp [Description, Fintype.card_prod, Fintype.card_fun]
  <;> ring

/-- Positions alone contribute the factor n^c in this raw record space.
@isnad1 id=le.3h4v.s8.08b5659ea7ce from=translated src=- shape=a3381a95 vocab=1319f3da
-/
theorem description_bound (n L ν c : ℕ)
    (hL : 1 ≤ L) (hν : 1 ≤ ν) (hc : c ≤ ν) :
    Fintype.card (Description n L ν c) ≤
      n ^ c * (fieldBound L ν) ^ (50 * ν) := by
  let B := fieldBound L ν
  have hmul : ν ≤ L * ν := by
    calc
      ν = 1 * ν := (one_mul ν).symm
      _ ≤ L * ν := Nat.mul_le_mul_right ν hL
  have hB : 1 ≤ B := by
    dsimp [B, fieldBound]
    nlinarith
  have hheader : 4 * L ≤ B := by
    dsimp [B, fieldBound]
    nlinarith
  have hname : ν ≤ B := by
    dsimp [B, fieldBound]
    nlinarith
  have hp1 : (4 * L) ^ ν ≤ B ^ ν := by gcongr
  have hp2 : ν ^ c ≤ B ^ ν := by
    calc
      ν ^ c ≤ B ^ c := by gcongr
      _ ≤ B ^ ν := by gcongr
  have hpower : B ^ ν * B ^ ν * (B ^ 12) ^ (4 * ν) = B ^ (50 * ν) := by
    rw [← pow_add, ← pow_mul, ← pow_add]
    congr 1
    omega
  calc
    Fintype.card (Description n L ν c) =
        n ^ c * ((4 * L) ^ ν * ν ^ c * (B ^ 12) ^ (4 * ν)) := by
          rw [description_card]
          dsimp [B]
          ring
    _ ≤ n ^ c * (B ^ ν * B ^ ν * (B ^ 12) ^ (4 * ν)) := by gcongr
    _ = n ^ c * B ^ (50 * ν) := by rw [hpower]

end DeletionCode.DescriptionCount
