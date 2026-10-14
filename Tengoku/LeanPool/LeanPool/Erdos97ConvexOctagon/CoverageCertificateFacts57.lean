/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData09
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (2, 21).
@isnad1 id=eq.0h0v.s5.34938f4ab0dd from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_2_21 :
    branchClaimRootValidB 2 21 (.patternThree 1) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 19).
@isnad1 id=eq.0h0v.s5.faa5face3aee from=translated src=- shape=e9e0773c vocab=d4b04ade
-/
theorem coverageBranchRoot_5_19 :
    branchClaimRootValidB 5 19 (.search branchClaims5Row19) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 18), starting at 128.
@isnad1 id=eq.0h0v.s3.7297042b13dc from=translated src=- shape=6f582f20 vocab=eaf49bc3
-/
theorem coverageBranchNodes_5_18_00128 :
    nodeClaimChunkValidB branchClaims5Row18 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 18), starting at 192.
@isnad1 id=eq.0h0v.s3.f9085f71dc5c from=translated src=- shape=6f582f20 vocab=eaf49bc3
-/
theorem coverageBranchNodes_5_18_00192 :
    nodeClaimChunkValidB branchClaims5Row18 192 62 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 19), starting at 0.
@isnad1 id=eq.0h0v.s3.eabfec41566f from=translated src=- shape=6f582f20 vocab=6b0af896
-/
theorem coverageBranchNodes_5_19_00000 :
    nodeClaimChunkValidB branchClaims5Row19 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 19), starting at 64.
@isnad1 id=eq.0h0v.s3.72507c7bcb82 from=translated src=- shape=6f582f20 vocab=6b0af896
-/
theorem coverageBranchNodes_5_19_00064 :
    nodeClaimChunkValidB branchClaims5Row19 64 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
