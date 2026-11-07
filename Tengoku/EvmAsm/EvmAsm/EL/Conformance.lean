/-
  EvmAsm.EL.Conformance

  Lean-side conformance vector surface for GH #125.
-/

module

@[expose] public section
namespace EvmAsm.EL
namespace Conformance

/-- Expected result for a conformance vector: either a value or an expected error.-/
inductive ExpectedResult (α : Type) where
  | value (output : α)
  | error (label : String)
  deriving Repr

/-- Typed conformance vector. Later slices can instantiate `ι`/`ο` with
    opcode inputs, transaction/state inputs, or decoded execution-spec cases.-/
structure TestVector (ι ο : Type) where
  id : String
  input : ι
  expected : ExpectedResult ο
  deriving Repr

/-- Result of checking one vector against an executable specification.-/
inductive CheckResult where
  | passed
  | failed (id : String)
  | errored (id label : String)
  deriving DecidableEq, Repr

namespace CheckResult

def isPassed : CheckResult → Prop
  | passed => True
  | _ => False

/--
@isnad1 id=ispassed.0h0v.s1.d34d0969d7d6 from=translated src=- shape=49959d42 vocab=5e9a063f
-/
@[simp] theorem isPassed_passed : passed.isPassed := trivial

/--
@isnad1 id=not.0h1v.s2.53b4373ef1df from=translated src=- shape=36b3d148 vocab=8b4706fc
-/
@[simp] theorem not_isPassed_failed (id : String) :
    ¬ (failed id).isPassed := by
  simp [isPassed]

/--
@isnad1 id=not.0h2v.s3.95eef77154aa from=translated src=- shape=bd194212 vocab=a024a026
-/
@[simp] theorem not_isPassed_errored (id label : String) :
    ¬ (errored id label).isPassed := by
  simp [isPassed]

end CheckResult

/-- Check a vector whose expected result is a concrete output.-/
def checkVector [DecidableEq ο] (run : ι → ο) (vector : TestVector ι ο) : CheckResult :=
  match vector.expected with
  | .value expected =>
      if run vector.input = expected then .passed else .failed vector.id
  | .error label => .errored vector.id label

/-- Check a vector against a partial executable specification.-/
def checkVector? [DecidableEq ο] (run : ι → Option ο) (vector : TestVector ι ο) : CheckResult :=
  match vector.expected with
  | .value expected =>
      match run vector.input with
      | some actual => if actual = expected then .passed else .failed vector.id
      | none => .failed vector.id
  | .error label =>
      match run vector.input with
      | some _ => .failed vector.id
      | none => .errored vector.id label

/--
@isnad1 id=eq.1h6v.s5.c23e4e13679b from=translated src=- shape=907149c0 vocab=a1a13695
-/
theorem checkVector_value_passed
    [DecidableEq ο] (run : ι → ο) (id : String) (input : ι) (expected : ο)
    (h_run : run input = expected) :
    checkVector run { id := id, input := input, expected := .value expected } = .passed := by
  simp [checkVector, h_run]

/--
@isnad1 id=eq.1h6v.s5.4cb5e5d028bf from=translated src=- shape=945e7bee vocab=1c711439
-/
theorem checkVector_value_failed
    [DecidableEq ο] (run : ι → ο) (id : String) (input : ι) (expected : ο)
    (h_run : run input ≠ expected) :
    checkVector run { id := id, input := input, expected := .value expected } = .failed id := by
  simp [checkVector, h_run]

/--
@isnad1 id=eq.0h6v.s5.acec5f0bd13b from=translated src=- shape=9bd7a6bf vocab=301a131f
-/
theorem checkVector_error_errored
    [DecidableEq ο] (run : ι → ο) (id label : String) (input : ι) :
    checkVector run { id := id, input := input, expected := .error label } = .errored id label := rfl

/--
@isnad1 id=eq.1h6v.s5.421541777304 from=translated src=- shape=1b93a792 vocab=af03f9b7
-/
theorem checkVector?_some_passed
    [DecidableEq ο] (run : ι → Option ο) (id : String) (input : ι) (expected : ο)
    (h_run : run input = some expected) :
    checkVector? run { id := id, input := input, expected := .value expected } = .passed := by
  simp [checkVector?, h_run]

/--
@isnad1 id=eq.1h6v.s5.4a06b42330c4 from=translated src=- shape=02742816 vocab=49b5d90e
-/
theorem checkVector?_none_error
    [DecidableEq ο] (run : ι → Option ο) (id label : String) (input : ι)
    (h_run : run input = none) :
    checkVector? run { id := id, input := input, expected := .error label } = .errored id label := by
  simp [checkVector?, h_run]

/-- Check a batch of total executable-spec conformance vectors.
    Distinctive token: conformanceBatchHelpers.-/
def checkBatch [DecidableEq ο] (run : ι → ο) (vectors : List (TestVector ι ο)) :
    List CheckResult :=
  vectors.map (checkVector run)

/-- Check a batch of partial executable-spec conformance vectors.-/
def checkBatch? [DecidableEq ο] (run : ι → Option ο) (vectors : List (TestVector ι ο)) :
    List CheckResult :=
  vectors.map (checkVector? run)

/-- Batch predicate used by conformance files that expect every vector to pass.-/
def allPassed : List CheckResult → Prop
  | [] => True
  | result :: rest => result.isPassed ∧ allPassed rest

/--
@isnad1 id=eq.0h3v.s4.76d64c36fc3c from=translated src=- shape=fbf760b4 vocab=f25ab501
-/
@[simp] theorem checkBatch_nil [DecidableEq ο] (run : ι → ο) :
    checkBatch run [] = [] := rfl

/--
@isnad1 id=eq.0h3v.s4.16b945ca9d84 from=translated src=- shape=ad4cc412 vocab=aeb6d280
-/
@[simp] theorem checkBatch?_nil [DecidableEq ο] (run : ι → Option ο) :
    checkBatch? run [] = [] := rfl

/--
@isnad1 id=eq.0h5v.s5.3ff160ed04cf from=translated src=- shape=84f7d339 vocab=4b923ed6
-/
@[simp] theorem checkBatch_cons [DecidableEq ο] (run : ι → ο)
    (vector : TestVector ι ο) (vectors : List (TestVector ι ο)) :
    checkBatch run (vector :: vectors) = checkVector run vector :: checkBatch run vectors := rfl

/--
@isnad1 id=eq.0h5v.s5.780f455548ae from=translated src=- shape=6f86c949 vocab=57173d44
-/
@[simp] theorem checkBatch?_cons [DecidableEq ο] (run : ι → Option ο)
    (vector : TestVector ι ο) (vectors : List (TestVector ι ο)) :
    checkBatch? run (vector :: vectors) = checkVector? run vector :: checkBatch? run vectors := rfl

/--
@isnad1 id=eq.0h5v.s6.0c6a273097df from=translated src=- shape=00648c1c vocab=797e4cc7
-/
@[simp] theorem checkBatch_append [DecidableEq ο] (run : ι → ο)
    (left right : List (TestVector ι ο)) :
    checkBatch run (left ++ right) = checkBatch run left ++ checkBatch run right := by
  simp [checkBatch]

/--
@isnad1 id=eq.0h5v.s6.d306562b24bc from=translated src=- shape=30487d97 vocab=2d99f8f7
-/
@[simp] theorem checkBatch?_append [DecidableEq ο] (run : ι → Option ο)
    (left right : List (TestVector ι ο)) :
    checkBatch? run (left ++ right) = checkBatch? run left ++ checkBatch? run right := by
  simp [checkBatch?]

/--
@isnad1 id=allpasse.0h0v.s1.707d1151e744 from=translated src=- shape=87ceb31f vocab=f007e1a1
-/
@[simp] theorem allPassed_nil : allPassed [] := trivial

/--
@isnad1 id=iff.0h2v.s4.7c1b0eb24484 from=translated src=- shape=5e0f7da1 vocab=998bb6c3
-/
@[simp] theorem allPassed_cons (result : CheckResult) (rest : List CheckResult) :
    allPassed (result :: rest) ↔ result.isPassed ∧ allPassed rest := Iff.rfl

/--
@isnad1 id=iff.0h1v.s3.300549e35b6f from=translated src=- shape=c2cf9e6d vocab=2f671628
-/
@[simp] theorem allPassed_passed_cons (rest : List CheckResult) :
    allPassed (.passed :: rest) ↔ allPassed rest := by
  simp [allPassed]

/--
@isnad1 id=not.0h2v.s3.a526ee2a599d from=translated src=- shape=0749db18 vocab=8e10ad4e
-/
@[simp] theorem not_allPassed_failed_cons (id : String) (rest : List CheckResult) :
    ¬ allPassed (.failed id :: rest) := by
  simp [allPassed]

/--
@isnad1 id=not.0h3v.s3.0984ec7f0aac from=translated src=- shape=7c132f6d vocab=33b9dc7a
-/
@[simp] theorem not_allPassed_errored_cons (id label : String) (rest : List CheckResult) :
    ¬ allPassed (.errored id label :: rest) := by
  simp [allPassed]

/--
@isnad1 id=iff.0h2v.s4.dcfc3a582cd6 from=translated src=- shape=d212c4a3 vocab=e5c2a458
-/
theorem allPassed_append (left right : List CheckResult) :
    allPassed (left ++ right) ↔ allPassed left ∧ allPassed right := by
  induction left with
  | nil =>
      simp [allPassed]
  | cons result rest ih =>
      cases result <;> simp [allPassed, ih]

end Conformance
end EvmAsm.EL
