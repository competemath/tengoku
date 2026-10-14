module

public import Tengoku

public section

open TopologicalSpace MeasureTheory Filter
open scoped NNReal ENNReal Topology ComplexConjugate

variable {α ε ε' E F G : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ ν : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [ENorm ε] [ENorm ε']

namespace MeasureTheory

attribute [local simp] memLp_top_const

/--
@isnad1 id=memlp.0h4v.s6.61b17a0447d2 from=translated src=- shape=d27455fa vocab=59887d47
-/
@[simp] lemma memLp_top_one [One E] : MemLp (1 : α → E) ⊤ μ := memLp_top_const _

end MeasureTheory
-- Tengoku: 1 registration(s) of this module made local so they do not change other libraries (generated)
