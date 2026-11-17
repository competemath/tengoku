import Tengoku.SingularityCompleteLean.Singularity.GreenPositive

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The directed word distance of a finite admissible support

The distance is the minimum length of an actual permitted jump word. It is
left invariant and satisfies the triangle inequality. Symmetry is not assumed:
for a nonsymmetric support this is a directed distance, not a metric instance.
-/

noncomputable section
open Set
open scoped Classical

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- Concatenate two permitted words in chronological order.-/
def walkWordAppend (s : Finset Γ) : (n m : ℕ) → WalkWord s n → WalkWord s m → WalkWord s (m + n)
  | 0, _, _, v => v
  | n + 1, m, w, v => (w.1, walkWordAppend s n m w.2 v)

/-- Concatenation follows the first word and then the second.
@isnad1 id=eq.0h7v.s6.f21b1b7c2607 from=translated src=- shape=0a37f2a5 vocab=1abca9ab
-/
theorem walkEndpoint_append (s : Finset Γ) (n m : ℕ)
    (w : WalkWord s n) (v : WalkWord s m) (x : Γ) :
    walkEndpoint s (m + n) x (walkWordAppend s n m w v) =
      walkEndpoint s m (walkEndpoint s n x w) v := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    exact ih w.2 (x * w.1)

/-- Minimum number of permitted jumps from `x` to `y`.-/
def jumpDistance (s : Finset Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (x y : Γ) : ℕ :=
  Nat.find (exists_walkWord_between s hgen x y)

/-- A shortest permitted path exists.
@isnad1 id=ex.1h4v.s6.3b7b26e2169a from=translated src=- shape=67c2dd21 vocab=d6b1789a
-/
theorem jumpDistance_realized (s : Finset Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (x y : Γ) : ∃ w : WalkWord s (jumpDistance s hgen x y),
      walkEndpoint s (jumpDistance s hgen x y) x w = y :=
  Nat.find_spec (exists_walkWord_between s hgen x y)

/-- Any permitted path bounds the minimum jump distance.
@isnad1 id=le.2h6v.s6.4f908bffa967 from=translated src=- shape=eec3c7e8 vocab=e45b4465
-/
theorem jumpDistance_le_length (s : Finset Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (n : ℕ) (w : WalkWord s n) (x y : Γ) (hw : walkEndpoint s n x w = y) :
    jumpDistance s hgen x y ≤ n :=
  Nat.find_min' (exists_walkWord_between s hgen x y) ⟨w, hw⟩

/-- Distance zero occurs exactly at equal group vertices.
@isnad1 id=iff.1h4v.s6.aa83cb40e271 from=translated src=- shape=c7689df9 vocab=13054ff8
-/
theorem jumpDistance_eq_zero_iff (s : Finset Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (x y : Γ) : jumpDistance s hgen x y = 0 ↔ x = y := by
  constructor
  · intro h
    have hw := jumpDistance_realized s hgen x y
    rw [h] at hw
    obtain ⟨w, hw⟩ := hw
    exact hw
  · rintro rfl
    exact Nat.eq_zero_of_le_zero (jumpDistance_le_length s hgen 0 PUnit.unit x x rfl)

/-- Left translation preserves the minimum permitted length.
@isnad1 id=eq.1h5v.s6.7d5ec8e98668 from=translated src=- shape=2f2137cd vocab=00a19894
-/
theorem jumpDistance_left (s : Finset Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (g x y : Γ) : jumpDistance s hgen (g * x) (g * y) = jumpDistance s hgen x y := by
  apply Nat.le_antisymm
  · obtain ⟨w, hw⟩ := jumpDistance_realized s hgen x y
    exact jumpDistance_le_length s hgen _ w _ _ (by rw [walkEndpoint_left, hw])
  · obtain ⟨w, hw⟩ := jumpDistance_realized s hgen (g * x) (g * y)
    exact jumpDistance_le_length s hgen _ w _ _ (mul_left_cancel (by rwa [walkEndpoint_left] at hw))

/-- Directed triangle inequality, using concatenation of shortest paths.
@isnad1 id=le.1h5v.s6.6718e86b8b2d from=translated src=- shape=1d74471f vocab=efabed29
-/
theorem jumpDistance_triangle (s : Finset Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (x y z : Γ) : jumpDistance s hgen x z ≤ jumpDistance s hgen x y + jumpDistance s hgen y z := by
  obtain ⟨w, hw⟩ := jumpDistance_realized s hgen x y
  obtain ⟨v, hv⟩ := jumpDistance_realized s hgen y z
  simpa only [Nat.add_comm] using jumpDistance_le_length s hgen _ (walkWordAppend s _ _ w v) x z
    (by rw [walkEndpoint_append, hw, hv])

/-- Every support element can be reached in one jump.
@isnad1 id=le.2h4v.s6.545d9cc59f38 from=translated src=- shape=fec59fa1 vocab=2149a549
-/
theorem jumpDistance_jump_le_one (s : Finset Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (x : Γ) {g : Γ} (hg : g ∈ s) : jumpDistance s hgen x (x * g) ≤ 1 :=
  jumpDistance_le_length s hgen 1 (⟨g, hg⟩, PUnit.unit) x (x * g) rfl

/-- A word in another support has bounded length when each of its jumps does.
@isnad1 id=le.2h7v.s7.7eb97a4f7e60 from=translated src=- shape=c20814a8 vocab=0f805fb9
-/
theorem jumpDistance_word_bound (s : Finset Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (t : Finset Γ) (L : ℕ) (hL : ∀ g ∈ t, jumpDistance s hgen 1 g ≤ L)
    (n : ℕ) (w : WalkWord t n) (x : Γ) :
    jumpDistance s hgen x (walkEndpoint t n x w) ≤ L * n := by
  induction n generalizing x with
  | zero => simp [walkEndpoint, (jumpDistance_eq_zero_iff s hgen x x).mpr rfl]
  | succ n ih =>
    change jumpDistance s hgen x (walkEndpoint t n (x * w.1) w.2) ≤ _
    have hstep : jumpDistance s hgen x (x * w.1) ≤ L := by
      simpa only [mul_one] using (jumpDistance_left s hgen x 1 w.1).trans_le (hL w.1 w.1.property)
    calc
      _ ≤ jumpDistance s hgen x (x * w.1) +
          jumpDistance s hgen (x * w.1) (walkEndpoint t n (x * w.1) w.2) :=
        jumpDistance_triangle s hgen _ _ _
      _ ≤ L + L * n := Nat.add_le_add hstep (ih w.2 _)
      _ = L * (n + 1) := by ring

/-- Finite admissible supports give uniformly comparable directed word distances.
@isnad1 id=ex.2h3v.s7.7bad3e16c2c4 from=translated src=- shape=b8543335 vocab=d039516d
-/
theorem jumpDistance_comparison (s t : Finset Γ)
    (hs : Submonoid.closure (s : Set Γ) = ⊤) (ht : Submonoid.closure (t : Set Γ) = ⊤) :
    ∃ L : ℕ, 0 < L ∧ ∀ x y, jumpDistance s hs x y ≤ L * jumpDistance t ht x y := by
  let L := 1 + ∑ g ∈ t, jumpDistance s hs 1 g
  have hL (g : Γ) (hg : g ∈ t) : jumpDistance s hs 1 g ≤ L := by
    have h := Finset.single_le_sum (fun a (_ : a ∈ t) => Nat.zero_le (jumpDistance s hs 1 a)) hg
    dsimp [L]
    omega
  refine ⟨L, by dsimp [L]; omega, fun x y => ?_⟩
  obtain ⟨w, hw⟩ := jumpDistance_realized t ht x y
  simpa only [hw] using jumpDistance_word_bound s hs t L hL _ w x

end Singularity
