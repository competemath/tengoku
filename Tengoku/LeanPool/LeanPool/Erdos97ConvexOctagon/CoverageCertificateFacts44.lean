/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData07
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 15).
@isnad1 id=eq.0h0v.s5.3145069a14be from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_1_15 :
    branchClaimRootValidB 1 15 (.patternThree 178) = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 31), starting at 64.
@isnad1 id=eq.0h0v.s3.63e5cc03339b from=translated src=- shape=6f582f20 vocab=a8971433
-/
theorem coverageBranchNodes_3_31_00064 :
    nodeClaimChunkValidB branchClaims3Row31 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 31), starting at 128.
@isnad1 id=eq.0h0v.s3.bc176c0f3dc0 from=translated src=- shape=6f582f20 vocab=a8971433
-/
theorem coverageBranchNodes_3_31_00128 :
    nodeClaimChunkValidB branchClaims3Row31 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 31), starting at 192.
@isnad1 id=eq.0h0v.s3.0fa954dcbe1f from=translated src=- shape=6f582f20 vocab=a8971433
-/
theorem coverageBranchNodes_3_31_00192 :
    nodeClaimChunkValidB branchClaims3Row31 192 26 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 31), starting at 218.
@isnad1 id=eq.0h0v.s3.3838b6592980 from=translated src=- shape=6f582f20 vocab=a8971433
-/
theorem coverageBranchNodes_3_31_00218 :
    nodeClaimChunkValidB branchClaims3Row31 218 27 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
