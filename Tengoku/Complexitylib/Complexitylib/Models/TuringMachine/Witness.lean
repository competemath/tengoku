/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Witness.Defs
import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Witness.Internal

/-!
# Witness machines and nondeterministic machines

An online witness machine is equivalent to an NTM with exactly the same time
and charged-space bounds. The witness is external, read-only, and consumed
left to right; nonconsuming steps cannot inspect it. This theorem does not
identify a free two-way certificate tape with ordinary nondeterminism.

`NTM.toWitnessTM` supplies a witness-machine instance for every NTM.
`WitnessTM.toNTM` removes the distinguished tape. The round trip recovers the
original NTM, and both translations preserve acceptance and all-path resource
bounds. Bounds are arbitrary functions, with no polynomial or constructibility
hypotheses. Witness loading is part of initialization, not a charged computation.
`run_congr_prefix` shows that the first `t` bits determine the visible `t`-step
run, so infinite streams are only a representation of finite certificates.
-/

public section

namespace Complexity

namespace WitnessTM

variable {k : ℕ}

/-- The first `t` witness bits determine the visible result of `t` steps.
Unread tails need not agree, so a finite certificate of length `t` suffices.
@isnad1 id=eq.1h6v.s6.100fe66df388 from=translated src=- shape=cd66e462 vocab=0abd0f93
-/
theorem run_congr_prefix (W : WitnessTM k) (x : List Bool) (t : ℕ)
    (g h : ℕ → Bool) (hprefix : ∀ i < t, g i = h i) :
    NTM.dropChoice (W.run x g t) = NTM.dropChoice (W.run x h t) :=
  run_congr_prefix_internal W x t g h hprefix

/-- Every NTM trace has a witness run with exactly the same visible endpoint.
@isnad1 id=ex.0h5v.s6.6283145f7452 from=translated src=- shape=866cf201 vocab=c2a69cf7
-/
theorem exists_run_eq_trace (W : WitnessTM k) (x : List Bool) (t : ℕ)
    (choices : Fin t → Bool) :
    ∃ g, NTM.dropChoice (W.run x g t) = W.toNTM.trace t choices (W.toNTM.initCfg x) :=
  exists_run_eq_trace_internal W x t choices

/-- Every witness run has an NTM trace with exactly the same visible endpoint.
@isnad1 id=ex.0h5v.s6.0e251da55f60 from=translated src=- shape=ef276f16 vocab=d3488709
-/
theorem exists_trace_eq_run (W : WitnessTM k) (x : List Bool) (t : ℕ) (g : ℕ → Bool) :
    ∃ choices, W.toNTM.trace t choices (W.toNTM.initCfg x) =
      NTM.dropChoice (W.run x g t) :=
  exists_trace_eq_run_internal W x t g

/-- Uniform halting bounds agree exactly in the two models.
@isnad1 id=iff.0h3v.s4.3fb9fc1e9756 from=translated src=- shape=2e3fcc5f vocab=ed6a0dd3
-/
theorem allWitnessesHaltIn_iff (W : WitnessTM k) (T : ℕ → ℕ) :
    W.AllWitnessesHaltIn T ↔ W.toNTM.AllPathsHaltIn T :=
  forall_congr' fun x => forall_run_iff_internal W x (T x.length)
    (fun c => c.state = W.machine.qhalt)

/-- Existential acceptance agrees at the same clock, including clock zero.
@isnad1 id=iff.0h4v.s4.fb969c95eec8 from=translated src=- shape=824e88ed vocab=5a4c3f03
-/
theorem acceptsInTime_iff (W : WitnessTM k) (x : List Bool) (t : ℕ) :
    W.AcceptsInTime x t ↔ W.toNTM.AcceptsInTime x t :=
  exists_run_iff_internal W x t
    (fun c => c.state = W.machine.qhalt ∧ c.output.cells 1 = Γ.one)

/-- Time-bounded deciding agrees without changing the time bound.
@isnad1 id=iff.0h4v.s4.ee22086a1e3a from=translated src=- shape=4d926e7c vocab=6ef667b3
-/
theorem decidesInTime_iff (W : WitnessTM k) (L : Language) (T : ℕ → ℕ) :
    W.DecidesInTime L T ↔ W.toNTM.DecidesInTime L T :=
  decidesInTime_iff_internal W L T

/-- A single machine's time and space bounds are preserved simultaneously.
@isnad1 id=iff.0h5v.s4.dfc94a666b12 from=translated src=- shape=7a3f3bc7 vocab=f22c02cd
-/
theorem decidesInTimeSpace_iff (W : WitnessTM k) (L : Language) (T S : ℕ → ℕ) :
    W.DecidesInTimeSpace L T S ↔ W.toNTM.DecidesInTimeSpace L T S :=
  decidesInTimeSpace_iff_internal W L T S

/-- Uniformly halting, space-bounded deciding agrees without extra charged space.
@isnad1 id=iff.0h4v.s4.ff5cfb4ae664 from=translated src=- shape=4d926e7c vocab=bb68f0a3
-/
theorem decidesInSpace_iff (W : WitnessTM k) (L : Language) (S : ℕ → ℕ) :
    W.DecidesInSpace L S ↔ W.toNTM.DecidesInSpace L S :=
  exists_congr fun T => W.decidesInTimeSpace_iff L T S

end WitnessTM

namespace NTM

/-- The simultaneous predicate recovers the existing space-only definition.
@isnad1 id=iff.0h4v.s4.80765f33fd46 from=translated src=- shape=c395cb2c vocab=450cb2c7
-/
theorem decidesInSpace_iff_exists_decidesInTimeSpace (N : NTM k) (L : Language)
    (S : ℕ → ℕ) :
    N.DecidesInSpace L S ↔ ∃ T, N.DecidesInTimeSpace L T S := Iff.rfl

/-- Supplying then removing the witness stream recovers the original NTM.
@isnad1 id=eq.0h2v.s3.6eb19fcb5e4d from=translated src=- shape=6ddf6d3e vocab=bb049302
-/
@[simp] theorem toNTM_toWitnessTM (N : NTM k) : N.toWitnessTM.toNTM = N :=
  toNTM_toWitnessTM_internal N

/-- Every NTM has an online witness presentation with the exact same time bound.
@isnad1 id=iff.0h4v.s4.6c0673836556 from=translated src=- shape=a77d1bb3 vocab=29c407ac
-/
theorem toWitnessTM_decidesInTime_iff (N : NTM k) (L : Language) (T : ℕ → ℕ) :
    N.toWitnessTM.DecidesInTime L T ↔ N.DecidesInTime L T := by
  simpa using N.toWitnessTM.decidesInTime_iff L T

/-- Every NTM has an online witness presentation preserving both resource bounds.
@isnad1 id=iff.0h5v.s4.4e283f17ccc0 from=translated src=- shape=04f9e797 vocab=fc6c36c1
-/
theorem toWitnessTM_decidesInTimeSpace_iff (N : NTM k) (L : Language) (T S : ℕ → ℕ) :
    N.toWitnessTM.DecidesInTimeSpace L T S ↔ N.DecidesInTimeSpace L T S := by
  simpa using N.toWitnessTM.decidesInTimeSpace_iff L T S

/-- Every NTM has an online witness presentation with the exact same space bound.
@isnad1 id=iff.0h4v.s4.02773e5ddf21 from=translated src=- shape=a77d1bb3 vocab=ecc92ec6
-/
theorem toWitnessTM_decidesInSpace_iff (N : NTM k) (L : Language) (S : ℕ → ℕ) :
    N.toWitnessTM.DecidesInSpace L S ↔ N.DecidesInSpace L S := by
  simpa using N.toWitnessTM.decidesInSpace_iff L S

end NTM

end Complexity
