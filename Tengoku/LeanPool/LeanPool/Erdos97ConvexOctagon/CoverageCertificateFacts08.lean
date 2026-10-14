/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData01
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 8).
@isnad1 id=eq.0h0v.s5.099122c243a3 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_08 :
    branchClaimRootValidB 0 8 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (4, 26).
@isnad1 id=eq.0h0v.s5.0e24c5ca56a4 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_26 :
    branchClaimRootValidB 4 26 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 30).
@isnad1 id=eq.0h0v.s5.eb45bc715f50 from=translated src=- shape=e9e0773c vocab=07ffc5c5
-/
theorem coverageBranchRoot_1_30 :
    branchClaimRootValidB 1 30 (.search branchClaims1Row30) = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 29), starting at 64.
@isnad1 id=eq.0h0v.s3.cd197ea42f56 from=translated src=- shape=6f582f20 vocab=1c6706f0
-/
theorem coverageBranchNodes_1_29_00064 :
    nodeClaimChunkValidB branchClaims1Row29 64 3 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 30), starting at 0.
@isnad1 id=eq.0h0v.s3.d6afdb11842f from=translated src=- shape=6f582f20 vocab=606d8a49
-/
theorem coverageBranchNodes_1_30_00000 :
    nodeClaimChunkValidB branchClaims1Row30 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 30), starting at 64.
@isnad1 id=eq.0h0v.s3.b737f0a33317 from=translated src=- shape=6f582f20 vocab=606d8a49
-/
theorem coverageBranchNodes_1_30_00064 :
    nodeClaimChunkValidB branchClaims1Row30 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 30), starting at 128.
@isnad1 id=eq.0h0v.s3.d7b982a444e6 from=translated src=- shape=6f582f20 vocab=606d8a49
-/
theorem coverageBranchNodes_1_30_00128 :
    nodeClaimChunkValidB branchClaims1Row30 128 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
