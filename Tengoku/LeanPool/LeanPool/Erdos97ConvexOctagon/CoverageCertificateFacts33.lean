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

/-- Root audit for fixed branch (0, 33).
@isnad1 id=eq.0h0v.s5.a4b3236c6a36 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_33 :
    branchClaimRootValidB 0 33 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 29).
@isnad1 id=eq.0h0v.s5.bf9e08669365 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_6_29 :
    branchClaimRootValidB 6 29 (.patternThree 6) = true := by
  decide +kernel

/-- Root audit for fixed branch (3, 11).
@isnad1 id=eq.0h0v.s5.05228d1cd20c from=translated src=- shape=e9e0773c vocab=6ca82166
-/
theorem coverageBranchRoot_3_11 :
    branchClaimRootValidB 3 11 (.search branchClaims3Row11) = true := by
  decide +kernel

/-- Root audit for fixed branch (3, 12).
@isnad1 id=eq.0h0v.s5.e14a0dc1133c from=translated src=- shape=e9e0773c vocab=5d586ea4
-/
theorem coverageBranchRoot_3_12 :
    branchClaimRootValidB 3 12 (.search branchClaims3Row12) = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 11), starting at 0.
@isnad1 id=eq.0h0v.s3.14b6f9249bd9 from=translated src=- shape=6f582f20 vocab=b8276532
-/
theorem coverageBranchNodes_3_11_00000 :
    nodeClaimChunkValidB branchClaims3Row11 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 11), starting at 64.
@isnad1 id=eq.0h0v.s3.5e7c31d57923 from=translated src=- shape=6f582f20 vocab=b8276532
-/
theorem coverageBranchNodes_3_11_00064 :
    nodeClaimChunkValidB branchClaims3Row11 64 49 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 12), starting at 0.
@isnad1 id=eq.0h0v.s3.7803af217eb1 from=translated src=- shape=6f582f20 vocab=72dcdf73
-/
theorem coverageBranchNodes_3_12_00000 :
    nodeClaimChunkValidB branchClaims3Row12 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 12), starting at 64.
@isnad1 id=eq.0h0v.s3.2f2e4c218074 from=translated src=- shape=6f582f20 vocab=72dcdf73
-/
theorem coverageBranchNodes_3_12_00064 :
    nodeClaimChunkValidB branchClaims3Row12 64 43 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
