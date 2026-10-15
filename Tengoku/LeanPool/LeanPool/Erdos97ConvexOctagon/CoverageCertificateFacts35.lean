/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData05
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 0).
@isnad1 id=eq.0h0v.s5.0720341b857e from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_1_00 :
    branchClaimRootValidB 1 0 (.patternThree 1) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 34).
@isnad1 id=eq.0h0v.s5.0f8fe406eae7 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_6_34 :
    branchClaimRootValidB 6 34 (.patternThree 6) = true := by
  decide +kernel

/-- Root audit for fixed branch (3, 24).
@isnad1 id=eq.0h0v.s5.a5a336a10549 from=translated src=- shape=e9e0773c vocab=2904e0ae
-/
theorem coverageBranchRoot_3_24 :
    branchClaimRootValidB 3 24 (.search branchClaims3Row24) = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 23), starting at 256.
@isnad1 id=eq.0h0v.s3.2324153717f8 from=translated src=- shape=6f582f20 vocab=8d09d39a
-/
theorem coverageBranchNodes_3_23_00256 :
    nodeClaimChunkValidB branchClaims3Row23 256 41 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 24), starting at 0.
@isnad1 id=eq.0h0v.s3.0a1e92924659 from=translated src=- shape=6f582f20 vocab=8e98a8c6
-/
theorem coverageBranchNodes_3_24_00000 :
    nodeClaimChunkValidB branchClaims3Row24 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 24), starting at 64.
@isnad1 id=eq.0h0v.s3.919df6a9c86e from=translated src=- shape=6f582f20 vocab=8e98a8c6
-/
theorem coverageBranchNodes_3_24_00064 :
    nodeClaimChunkValidB branchClaims3Row24 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 24), starting at 128.
@isnad1 id=eq.0h0v.s3.103e9cd525c1 from=translated src=- shape=6f582f20 vocab=8e98a8c6
-/
theorem coverageBranchNodes_3_24_00128 :
    nodeClaimChunkValidB branchClaims3Row24 128 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
