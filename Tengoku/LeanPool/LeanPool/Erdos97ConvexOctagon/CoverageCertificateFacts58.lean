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

/-- Root audit for fixed branch (2, 22).
@isnad1 id=eq.0h0v.s5.38a166b60966 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_2_22 :
    branchClaimRootValidB 2 22 (.patternThree 1) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 24).
@isnad1 id=eq.0h0v.s5.8ee3ce19a1a9 from=translated src=- shape=e9e0773c vocab=7b78f9b5
-/
theorem coverageBranchRoot_5_24 :
    branchClaimRootValidB 5 24 (.search branchClaims5Row24) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 19), starting at 128.
@isnad1 id=eq.0h0v.s3.fecf7d3dd7ed from=translated src=- shape=6f582f20 vocab=6b0af896
-/
theorem coverageBranchNodes_5_19_00128 :
    nodeClaimChunkValidB branchClaims5Row19 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 19), starting at 192.
@isnad1 id=eq.0h0v.s3.c05cfa7054fa from=translated src=- shape=6f582f20 vocab=6b0af896
-/
theorem coverageBranchNodes_5_19_00192 :
    nodeClaimChunkValidB branchClaims5Row19 192 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 19), starting at 256.
@isnad1 id=eq.0h0v.s3.01a4adb2971f from=translated src=- shape=6f582f20 vocab=6b0af896
-/
theorem coverageBranchNodes_5_19_00256 :
    nodeClaimChunkValidB branchClaims5Row19 256 42 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 24), starting at 0.
@isnad1 id=eq.0h0v.s3.66a44c9e02ca from=translated src=- shape=6f582f20 vocab=438d7098
-/
theorem coverageBranchNodes_5_24_00000 :
    nodeClaimChunkValidB branchClaims5Row24 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
