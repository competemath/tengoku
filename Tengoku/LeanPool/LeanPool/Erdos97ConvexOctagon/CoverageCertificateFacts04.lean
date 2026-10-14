/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData00
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 4).
@isnad1 id=eq.0h0v.s5.f853658b45f3 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_04 :
    branchClaimRootValidB 0 4 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (4, 22).
@isnad1 id=eq.0h0v.s5.547c65fcd89d from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_22 :
    branchClaimRootValidB 4 22 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 17).
@isnad1 id=eq.0h0v.s5.da894743b160 from=translated src=- shape=e9e0773c vocab=b8c2db5c
-/
theorem coverageBranchRoot_1_17 :
    branchClaimRootValidB 1 17 (.search branchClaims1Row17) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 18).
@isnad1 id=eq.0h0v.s5.86a59a0c9ee9 from=translated src=- shape=e9e0773c vocab=30976c42
-/
theorem coverageBranchRoot_1_18 :
    branchClaimRootValidB 1 18 (.search branchClaims1Row18) = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 17), starting at 0.
@isnad1 id=eq.0h0v.s3.930bd432b29c from=translated src=- shape=6f582f20 vocab=763d2da1
-/
theorem coverageBranchNodes_1_17_00000 :
    nodeClaimChunkValidB branchClaims1Row17 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 17), starting at 64.
@isnad1 id=eq.0h0v.s3.049ff0f3f750 from=translated src=- shape=6f582f20 vocab=763d2da1
-/
theorem coverageBranchNodes_1_17_00064 :
    nodeClaimChunkValidB branchClaims1Row17 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 17), starting at 128.
@isnad1 id=eq.0h0v.s3.22da10660f67 from=translated src=- shape=6f582f20 vocab=763d2da1
-/
theorem coverageBranchNodes_1_17_00128 :
    nodeClaimChunkValidB branchClaims1Row17 128 10 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 18), starting at 0.
@isnad1 id=eq.0h0v.s3.463a3c95929c from=translated src=- shape=6f582f20 vocab=fe9b8a3f
-/
theorem coverageBranchNodes_1_18_00000 :
    nodeClaimChunkValidB branchClaims1Row18 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
