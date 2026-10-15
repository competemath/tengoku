/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData05
public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData06
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 1).
@isnad1 id=eq.0h0v.s5.ebcd1c66a966 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_1_01 :
    branchClaimRootValidB 1 1 (.patternThree 178) = true := by
  decide +kernel

/-- Root audit for fixed branch (3, 25).
@isnad1 id=eq.0h0v.s5.9254c6639e5b from=translated src=- shape=e9e0773c vocab=4fac145a
-/
theorem coverageBranchRoot_3_25 :
    branchClaimRootValidB 3 25 (.search branchClaims3Row25) = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 24), starting at 192.
@isnad1 id=eq.0h0v.s3.548abad8606e from=translated src=- shape=6f582f20 vocab=8e98a8c6
-/
theorem coverageBranchNodes_3_24_00192 :
    nodeClaimChunkValidB branchClaims3Row24 192 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 24), starting at 256.
@isnad1 id=eq.0h0v.s3.8440bead001d from=translated src=- shape=6f582f20 vocab=8e98a8c6
-/
theorem coverageBranchNodes_3_24_00256 :
    nodeClaimChunkValidB branchClaims3Row24 256 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 24), starting at 320.
@isnad1 id=eq.0h0v.s3.0e61defe63d5 from=translated src=- shape=6f582f20 vocab=8e98a8c6
-/
theorem coverageBranchNodes_3_24_00320 :
    nodeClaimChunkValidB branchClaims3Row24 320 29 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 25), starting at 0.
@isnad1 id=eq.0h0v.s3.b2ec5a16da61 from=translated src=- shape=6f582f20 vocab=8f57ad29
-/
theorem coverageBranchNodes_3_25_00000 :
    nodeClaimChunkValidB branchClaims3Row25 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
