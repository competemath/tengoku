import Tengoku.DeletionCodesLean.DeletionCode.PartialWords
import Tengoku.DeletionCodesLean.DeletionCode.Recovery

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms adjacent_window_seed` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms selected_window_cover` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms seed_selects_window` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms all_windows_known` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Realizes.ready_seedKnown` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Realizes.complete_wordKnown` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Realizes.mono` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Realizes.start` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Realizes.fill` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Realizes.update_mem` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Realizes.start_update` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Realizes.fill_update` (it only prints; the queue checks the axioms of every declaration). -/

/-!
The three selected recovery windows, interpreted in actual partial-word memory.
The realization invariant records stored seeds and filled windows. Readiness then
gives a readable seed by overlap, and completion gives the entire readable word.
ConcreteProgress uses this invariant to realize each kind of abstract step.
-/
namespace DeletionCode.SelectedWindows

open Windows PartialWords Recovery

def windowStart (D : ℕ) (w : Slot) : ℕ :=
  if w.val = 0 then 0 else if w.val = 1 then D / 2 else D

/--
@isnad1 id=le.0h2v.s3.d57304e27e5e from=translated src=- shape=0dd6a2f0 vocab=b4b6e9c5
-/
theorem windowStart_le (D : ℕ) (w : Slot) : windowStart D w ≤ D := by
  fin_cases w <;> simp [windowStart, Nat.div_le_self]

def WindowKnown (s : Memory) (start len : ℕ) : Prop :=
  ∃ bits, readBits s start len = some bits

def SeedKnown (s : Memory) (start L k : ℕ) : Prop :=
  ∃ r bits, r + k ≤ L ∧ readBits s (start + r) k = some bits

/--
@isnad1 id=iff.0h3v.s5.9503490463d6 from=translated src=- shape=f511611e vocab=80d54629
-/
theorem windowKnown_iff (s : Memory) (start len : ℕ) :
    WindowKnown s start len ↔ ∀ i, i < len → ∃ b, s (start + i) = some b := by
  constructor
  · rintro ⟨bits, hread⟩ i hi
    exact ⟨bits ⟨i, hi⟩, (readBits_eq_some_iff s start len bits).mp hread ⟨i, hi⟩⟩
  · intro h
    refine ⟨fun i => (s (start + i.val)).getD false, ?_⟩
    apply (readBits_eq_some_iff _ _ _ _).mpr
    intro i
    obtain ⟨b, hb⟩ := h i.val i.isLt
    simp [hb]

/-- Every subblock of a readable block can itself be read.
@isnad1 id=windowkn.3h5v.s5.c2b04daaba6e from=translated src=- shape=2a367486 vocab=fb844558
-/
theorem windowKnown_subblock (s : Memory) (a m b len : ℕ)
    (h : WindowKnown s a m) (hab : a ≤ b) (hbound : b + len ≤ a + m) :
    WindowKnown s b len := by
  apply (windowKnown_iff _ _ _).mpr
  intro i hi
  have hidx : b + i - a < m := by omega
  have hread := (windowKnown_iff _ _ _).mp h (b + i - a) hidx
  simpa [show a + (b + i - a) = b + i by omega] using hread

/--
@isnad1 id=windowkn.2h4v.s4.8eadab19b1ab from=translated src=- shape=25f02e62 vocab=45965060
-/
theorem windowKnown_mono (s t : Memory) (start len : ℕ)
    (hext : Extends s t) (h : WindowKnown s start len) :
    WindowKnown t start len := by
  apply (windowKnown_iff _ _ _).mpr
  intro i hi
  obtain ⟨b, hb⟩ := (windowKnown_iff _ _ _).mp h i hi
  exact ⟨b, hext (start + i) b hb⟩

/--
@isnad1 id=seedknow.2h5v.s4.53ea9f435118 from=translated src=- shape=56f4aa71 vocab=1618fbca
-/
theorem seedKnown_mono (s t : Memory) (start L k : ℕ)
    (hext : Extends s t) (h : SeedKnown s start L k) :
    SeedKnown t start L k := by
  rcases h with ⟨r, bits, hr, hread⟩
  obtain ⟨newBits, hnew⟩ := windowKnown_mono s t (start + r) k hext ⟨bits, hread⟩
  exact ⟨r, newBits, hr, hnew⟩

private theorem seedKnown_of_overlap (s : Memory) (a b L k : ℕ)
    (h : WindowKnown s a L)
    (ha : max a b + k ≤ a + L) (hb : max a b + k ≤ b + L) :
    SeedKnown s b L k := by
  have hma : a ≤ max a b := le_max_left a b
  have hmb : b ≤ max a b := le_max_right a b
  obtain ⟨bits, hread⟩ := windowKnown_subblock s a L (max a b) k h hma ha
  refine ⟨max a b - b, bits, by omega, ?_⟩
  simpa [show b + (max a b - b) = max a b by omega] using hread

/-- An already read adjacent selected window supplies a readable k-seed.
@isnad1 id=seedknow.3h5v.s6.9fc8609543bf from=translated src=- shape=f48cae58 vocab=3383c577
-/
theorem adjacent_window_seed (s : Memory) (D k : ℕ) (v w : Slot)
    (hD : D < 3 * (k + 1)) (hadj : AdjSlot v w)
    (hknown : WindowKnown s (windowStart D v) (3 * (k + 1))) :
    SeedKnown s (windowStart D w) (3 * (k + 1)) k := by
  apply seedKnown_of_overlap s (windowStart D v) (windowStart D w)
    (3 * (k + 1)) k hknown
  all_goals
    have hover := three_windows_overlap k D hD
    have hhalf : D / 2 ≤ D := Nat.div_le_self D 2
    fin_cases v <;> fin_cases w <;>
      simp [AdjSlot, windowStart] at hadj ⊢ <;> omega

/-- Every in-bounds k-stretch lies in one of the actual selected slots.
@isnad1 id=ex.2h3v.s7.593834439e7c from=translated src=- shape=dc712a98 vocab=8cabea51
-/
theorem selected_window_cover (D k a : ℕ) (hD : D < 3 * (k + 1))
    (ha : a + k ≤ 3 * (k + 1) + D) :
    ∃ w : Slot, windowStart D w ≤ a ∧ a + k ≤ windowStart D w + 3 * (k + 1) := by
  obtain ⟨b, hb, hba, hab⟩ := three_windows_cover k D a hD ha
  rcases hb with hb | hb | hb
  · refine ⟨⟨0, by omega⟩, ?_⟩
    simpa [windowStart, hb] using And.intro hba hab
  · refine ⟨⟨1, by omega⟩, ?_⟩
    simpa [windowStart, hb] using And.intro hba hab
  · refine ⟨⟨2, by omega⟩, ?_⟩
    simpa [windowStart, hb] using And.intro hba hab

/-- A newly available k-stretch can initialize a realizable selected seed slot.
@isnad1 id=ex.3h4v.s6.3ced734d1918 from=translated src=- shape=dce7b4e3 vocab=adfce1ed
-/
theorem seed_selects_window (s : Memory) (D k a : ℕ) (hD : D < 3 * (k + 1))
    (ha : a + k ≤ 3 * (k + 1) + D) (hknown : WindowKnown s a k) :
    ∃ w : Slot, SeedKnown s (windowStart D w) (3 * (k + 1)) k := by
  obtain ⟨w, hwa, haw⟩ := selected_window_cover D k a hD ha
  obtain ⟨bits, hread⟩ := hknown
  refine ⟨w, a - windowStart D w, bits, by omega, ?_⟩
  simpa [show windowStart D w + (a - windowStart D w) = a by omega] using hread

/-- The first and last selected windows already cover every letter of the path.
@isnad1 id=windowkn.2h3v.s5.2bfe17f4f3b2 from=translated src=- shape=a041c1be vocab=78ab7511
-/
theorem all_windows_known (s : Memory) (D L : ℕ) (hD : D ≤ L)
    (hknown : ∀ w : Slot, WindowKnown s (windowStart D w) L) :
    WindowKnown s 0 (L + D) := by
  apply (windowKnown_iff _ _ _).mpr
  intro i hi
  by_cases hfirst : i < L
  · have hread := (windowKnown_iff _ _ _).mp (hknown ⟨0, by omega⟩) i hfirst
    simpa [windowStart] using hread
  · have hiD : D ≤ i := by omega
    have hiL : i - D < L := by omega
    have hread := (windowKnown_iff _ _ _).mp (hknown ⟨2, by omega⟩) (i - D) hiL
    simpa [windowStart, show D + (i - D) = i by omega] using hread

variable {B : Type*}

/-- Data invariant tying the abstract scheduler to actual readable memory.-/
structure Realizes (s : State B) (mem : B → Memory) (D : B → ℕ) (k : ℕ) : Prop where
  seed_known : ∀ b w, s.seed b = some w →
    SeedKnown (mem b) (windowStart (D b) w) (3 * (k + 1)) k
  done_known : ∀ b w, s.Done b w →
    WindowKnown (mem b) (windowStart (D b) w) (3 * (k + 1))

/--
@isnad1 id=seedknow.3h7v.s6.fd30e95f0777 from=translated src=- shape=b7647b62 vocab=4fc3016a
-/
theorem Realizes.ready_seedKnown (s : State B) (mem : B → Memory) (D : B → ℕ)
    (k : ℕ) (hreal : Realizes s mem D k) (b : B) (w : Slot)
    (hD : D b < 3 * (k + 1)) (hready : s.Ready b w) :
    SeedKnown (mem b) (windowStart (D b) w) (3 * (k + 1)) k := by
  rcases hready with hseed | ⟨v, hv, hadj⟩
  · exact hreal.seed_known b w hseed
  · exact adjacent_window_seed (mem b) (D b) k v w hD hadj (hreal.done_known b v hv)

/--
@isnad1 id=windowkn.3h6v.s6.d12acb4c57cc from=translated src=- shape=06c80ff3 vocab=5e92641b
-/
theorem Realizes.complete_wordKnown (s : State B) (mem : B → Memory) (D : B → ℕ)
    (k : ℕ) (hreal : Realizes s mem D k) (b : B)
    (hD : D b ≤ 3 * (k + 1)) (hcomplete : s.Complete b) :
    WindowKnown (mem b) 0 (3 * (k + 1) + D b) := by
  exact all_windows_known (mem b) (D b) (3 * (k + 1)) hD
    (fun w => hreal.done_known b w (hcomplete w))

/--
@isnad1 id=realizes.2h6v.s5.cb42a3557ff4 from=translated src=- shape=ab1bd8d2 vocab=3390c0d7
-/
theorem Realizes.mono (s : State B) (mem mem' : B → Memory) (D : B → ℕ) (k : ℕ)
    (hreal : Realizes s mem D k) (hext : ∀ b, Extends (mem b) (mem' b)) :
    Realizes s mem' D k where
  seed_known b w h := seedKnown_mono _ _ _ _ _ (hext b) (hreal.seed_known b w h)
  done_known b w h := windowKnown_mono _ _ _ _ (hext b) (hreal.done_known b w h)

/-- A start operation is realizable when its chosen slot has an actual stored seed.
@isnad1 id=realizes.2h7v.s6.23a52b876a34 from=translated src=- shape=238658f4 vocab=bb8d9531
-/
theorem Realizes.start [DecidableEq B] (s : State B) (mem : B → Memory)
    (D : B → ℕ) (k : ℕ) (hreal : Realizes s mem D k) (b : B) (w : Slot)
    (hseed : SeedKnown (mem b) (windowStart (D b) w) (3 * (k + 1)) k) :
    Realizes (s.start b w) mem D k where
  seed_known a v h := by
    by_cases hab : a = b
    · subst a
      have hv : w = v := by simpa [State.start] using h
      simpa [hv] using hseed
    · have hba : b ≠ a := Ne.symm hab
      exact hreal.seed_known a v (by simpa [State.start, hab, hba] using h)
  done_known a v h := hreal.done_known a v h

/-- Marking a filled window preserves realization once its data is stored.
@isnad1 id=realizes.2h7v.s6.da215abdf186 from=translated src=- shape=6240c23c vocab=706da6b3
-/
theorem Realizes.fill [DecidableEq B] (s : State B) (mem : B → Memory)
    (D : B → ℕ) (k : ℕ) (hreal : Realizes s mem D k) (b : B) (w : Slot)
    (hwindow : WindowKnown (mem b) (windowStart (D b) w) (3 * (k + 1))) :
    Realizes (s.fill b w) mem D k where
  seed_known a v h := hreal.seed_known a v h
  done_known a v h := by
    have hmem : (a, v) = (b, w) ∨ (a, v) ∈ s.filled := Finset.mem_insert.mp h
    rcases hmem with heq | hold
    · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
      exact hwindow
    · exact hreal.done_known a v hold

/--
@isnad1 id=realizes.2h7v.s5.e3f526d559f5 from=translated src=- shape=53355fa3 vocab=90b416ed
-/
theorem Realizes.update_mem [DecidableEq B] (s : State B) (mem : B → Memory)
    (D : B → ℕ) (k : ℕ) (hreal : Realizes s mem D k) (b : B) (t : Memory)
    (hext : Extends (mem b) t) : Realizes s (Function.update mem b t) D k := by
  apply Realizes.mono s mem (Function.update mem b t) D k hreal
  intro a
  by_cases hab : a = b
  · subst a
    simpa using hext
  · have hba : b ≠ a := Ne.symm hab
    intro j bit hj
    simpa [Function.update, hab, hba] using hj

/-- Start a chosen slot after extending just that bubble's memory.
@isnad1 id=realizes.3h8v.s6.bc4f57aafd5d from=translated src=- shape=df8f08f4 vocab=5edca2ae
-/
theorem Realizes.start_update [DecidableEq B] (s : State B) (mem : B → Memory)
    (D : B → ℕ) (k : ℕ) (hreal : Realizes s mem D k) (b : B) (w : Slot) (t : Memory)
    (hext : Extends (mem b) t)
    (hseed : SeedKnown t (windowStart (D b) w) (3 * (k + 1)) k) :
    Realizes (s.start b w) (Function.update mem b t) D k := by
  apply Realizes.start s (Function.update mem b t) D k
    (Realizes.update_mem s mem D k hreal b t hext) b w
  simpa using hseed

/-- Mark a window filled after its checked write extends that bubble's memory.
@isnad1 id=realizes.3h8v.s6.15606dd772fe from=translated src=- shape=15c54b80 vocab=788879f9
-/
theorem Realizes.fill_update [DecidableEq B] (s : State B) (mem : B → Memory)
    (D : B → ℕ) (k : ℕ) (hreal : Realizes s mem D k) (b : B) (w : Slot) (t : Memory)
    (hext : Extends (mem b) t)
    (hwindow : WindowKnown t (windowStart (D b) w) (3 * (k + 1))) :
    Realizes (s.fill b w) (Function.update mem b t) D k := by
  apply Realizes.fill s (Function.update mem b t) D k
    (Realizes.update_mem s mem D k hreal b t hext) b w
  simpa using hwindow

end DeletionCode.SelectedWindows
