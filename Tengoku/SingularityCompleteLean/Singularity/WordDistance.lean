import Tengoku.SingularityCompleteLean.Singularity.JumpDistance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The symmetric word distance and its comparison with jump distance

Adjoin the inverses of the finite support and minimize permitted path length.
The resulting natural-valued distance is symmetric, separates points, is left
invariant, and satisfies the triangle inequality. The original directed jump
distance is uniformly comparable to this symmetric word distance.
-/

noncomputable section
open Set
open scoped Classical

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- Reversing a path in an inverse-closed support costs at most the same number of jumps.
@isnad1 id=le.2h5v.s7.37576ce58d6d from=translated src=- shape=0a661640 vocab=1f805157
-/
theorem jumpDistance_reverse_word_bound (s : Finset Γ)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) (hinv : ∀ g ∈ s, g⁻¹ ∈ s)
    (n : ℕ) (w : WalkWord s n) (x : Γ) :
    jumpDistance s hgen (walkEndpoint s n x w) x ≤ n := by
  induction n generalizing x with
  | zero => exact Nat.le_of_eq ((jumpDistance_eq_zero_iff s hgen x x).mpr rfl)
  | succ n ih =>
    change jumpDistance s hgen (walkEndpoint s n (x * w.1) w.2) x ≤ n + 1
    have hstep : jumpDistance s hgen (x * w.1) x ≤ 1 := by
      simpa only [mul_inv_cancel_right] using
        jumpDistance_jump_le_one s hgen (x * w.1) (hinv w.1 w.1.property)
    exact (jumpDistance_triangle s hgen _ (x * w.1) x).trans (Nat.add_le_add (ih w.2 _) hstep)

/-- Inverse-closed supports have symmetric minimum jump distance.
@isnad1 id=eq.2h4v.s6.1b0477bc1688 from=translated src=- shape=fd9296a2 vocab=aa31a88e
-/
theorem jumpDistance_symm_of_inverse_closed (s : Finset Γ)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) (hinv : ∀ g ∈ s, g⁻¹ ∈ s)
    (x y : Γ) : jumpDistance s hgen x y = jumpDistance s hgen y x := by
  have hle (x y : Γ) : jumpDistance s hgen y x ≤ jumpDistance s hgen x y := by
    obtain ⟨w, hw⟩ := jumpDistance_realized s hgen x y
    simpa only [hw] using jumpDistance_reverse_word_bound s hgen hinv _ w x
  exact Nat.le_antisymm (hle y x) (hle x y)

/-- The support together with its inverses.-/
def symmetricWordSupport (s : Finset Γ) : Finset Γ := s ∪ s.map ⟨Inv.inv, inv_injective⟩

/--
@isnad1 id=iff.0h3v.s5.93d2fa469087 from=translated src=- shape=bbda3650 vocab=ac4d8f43
-/
theorem mem_symmetricWordSupport (s : Finset Γ) (g : Γ) :
    g ∈ symmetricWordSupport s ↔ g ∈ s ∨ g⁻¹ ∈ s := by
  rw [symmetricWordSupport, Finset.mem_union]
  apply or_congr_right
  constructor
  · intro hg
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hg
    simpa only [Function.Embedding.coeFn_mk, inv_inv] using ha
  · intro hg
    exact Finset.mem_map.mpr ⟨g⁻¹, hg, inv_inv g⟩

/--
@isnad1 id=mem.1h3v.s5.cb9098ed38b0 from=translated src=- shape=4a10b646 vocab=ac4d8f43
-/
theorem symmetricWordSupport_inverse_closed (s : Finset Γ) (g : Γ)
    (hg : g ∈ symmetricWordSupport s) : g⁻¹ ∈ symmetricWordSupport s := by
  simpa only [mem_symmetricWordSupport, inv_inv, or_comm] using hg

/--
@isnad1 id=eq.1h2v.s6.417609957dde from=translated src=- shape=dba23af9 vocab=b473648a
-/
theorem symmetricWordSupport_generates (s : Finset Γ)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) :
    Submonoid.closure (symmetricWordSupport s : Set Γ) = ⊤ := by
  apply top_unique
  rw [← hgen]
  exact Submonoid.closure_mono (fun g hg => (mem_symmetricWordSupport s g).mpr (Or.inl hg))

/-- Minimum length for the symmetrized finite generating set.-/
def wordDistance (s : Finset Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (x y : Γ) : ℕ :=
  jumpDistance (symmetricWordSupport s) (symmetricWordSupport_generates s hgen) x y

/--
@isnad1 id=iff.1h4v.s6.6b5bdf6acbf2 from=translated src=- shape=c7689df9 vocab=06c45996
-/
theorem wordDistance_eq_zero_iff (s : Finset Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (x y : Γ) : wordDistance s hgen x y = 0 ↔ x = y :=
  jumpDistance_eq_zero_iff _ _ x y

/--
@isnad1 id=eq.1h4v.s6.31ae3b52dd3a from=translated src=- shape=f3b86e66 vocab=06c45996
-/
theorem wordDistance_symm (s : Finset Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (x y : Γ) : wordDistance s hgen x y = wordDistance s hgen y x :=
  jumpDistance_symm_of_inverse_closed _ _ (symmetricWordSupport_inverse_closed s) x y

/--
@isnad1 id=eq.1h5v.s6.c8c40cfbdd79 from=translated src=- shape=2f2137cd vocab=0bd7a34c
-/
theorem wordDistance_left (s : Finset Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (g x y : Γ) : wordDistance s hgen (g * x) (g * y) = wordDistance s hgen x y :=
  jumpDistance_left _ _ g x y

/--
@isnad1 id=le.1h5v.s6.c09c1bac797c from=translated src=- shape=1d74471f vocab=9f66428e
-/
theorem wordDistance_triangle (s : Finset Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (x y z : Γ) : wordDistance s hgen x z ≤ wordDistance s hgen x y + wordDistance s hgen y z :=
  jumpDistance_triangle _ _ x y z

/-- Adding inverse jumps cannot increase shortest-path length.
@isnad1 id=le.1h4v.s6.023ed122c6ed from=translated src=- shape=92e729d4 vocab=f9703435
-/
theorem wordDistance_le_jumpDistance (s : Finset Γ)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) (x y : Γ) :
    wordDistance s hgen x y ≤ jumpDistance s hgen x y := by
  obtain ⟨w, hw⟩ := jumpDistance_realized s hgen x y
  have h := jumpDistance_word_bound (symmetricWordSupport s) (symmetricWordSupport_generates s hgen)
    s 1 (fun g hg => by
      simpa only [one_mul] using jumpDistance_jump_le_one (symmetricWordSupport s)
        (symmetricWordSupport_generates s hgen) 1 ((mem_symmetricWordSupport s g).mpr (Or.inl hg))) _ w x
  simpa only [wordDistance, hw, one_mul] using h

/-- Semigroup generation allows inverse jumps to be replaced uniformly by forward words.
@isnad1 id=ex.1h2v.s6.a83c880ca83d from=translated src=- shape=cb57b0cd vocab=9d5bd987
-/
theorem jumpDistance_le_wordDistance_mul (s : Finset Γ)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) :
    ∃ L : ℕ, 0 < L ∧ ∀ x y, jumpDistance s hgen x y ≤ L * wordDistance s hgen x y :=
  jumpDistance_comparison s (symmetricWordSupport s) hgen (symmetricWordSupport_generates s hgen)

end Singularity
