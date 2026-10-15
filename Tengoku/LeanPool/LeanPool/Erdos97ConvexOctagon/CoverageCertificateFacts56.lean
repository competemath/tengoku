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

/-- Root audit for fixed branch (2, 20).
@isnad1 id=eq.0h0v.s5.96912be486ba from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_2_20 :
    branchClaimRootValidB 2 20 (.patternThree 1) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 18).
@isnad1 id=eq.0h0v.s5.a2782c0d53a2 from=translated src=- shape=e9e0773c vocab=fa36cf5b
-/
theorem coverageBranchRoot_5_18 :
    branchClaimRootValidB 5 18 (.search branchClaims5Row18) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 17), starting at 128.
@isnad1 id=eq.0h0v.s3.428d7ba58ce5 from=translated src=- shape=6f582f20 vocab=e3b1c049
-/
theorem coverageBranchNodes_5_17_00128 :
    nodeClaimChunkValidB branchClaims5Row17 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 17), starting at 192.
@isnad1 id=eq.0h0v.s3.dac9b27af5f3 from=translated src=- shape=6f582f20 vocab=e3b1c049
-/
theorem coverageBranchNodes_5_17_00192 :
    nodeClaimChunkValidB branchClaims5Row17 192 28 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 18), starting at 0.
@isnad1 id=eq.0h0v.s3.7bc2b079ef07 from=translated src=- shape=6f582f20 vocab=eaf49bc3
-/
theorem coverageBranchNodes_5_18_00000 :
    nodeClaimChunkValidB branchClaims5Row18 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 18), starting at 64.
@isnad1 id=eq.0h0v.s3.0e2c93c23561 from=translated src=- shape=6f582f20 vocab=eaf49bc3
-/
theorem coverageBranchNodes_5_18_00064 :
    nodeClaimChunkValidB branchClaims5Row18 64 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
