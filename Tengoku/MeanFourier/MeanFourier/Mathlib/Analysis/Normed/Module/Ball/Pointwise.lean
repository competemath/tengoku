module

public import Tengoku
public import Tengoku.MeanFourier.MeanFourier.Mathlib.Topology.Bornology.Basic

public section

namespace Bornology
variable {α 𝕜 E : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] {f : α → E}
  {c : 𝕜}

/--
@isnad1 id=isbddfun.1h5v.s7.e51d2a0a017b from=translated src=- shape=3a65a274 vocab=0b97b1bb
-/
@[to_fun (attr := fun_prop)]
lemma IsBddFun.const_smul (hf : IsBddFun f) : IsBddFun (c • f) := by
  simpa [Pi.smul_def, Set.range_smul, IsBddFun] using hf.smul₀ c

end Bornology
