/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData03
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 24).
@isnad1 id=eq.0h0v.s5.2344706016e9 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_24 :
    branchClaimRootValidB 0 24 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 22).
@isnad1 id=eq.0h0v.s5.a073571aad3c from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_5_22 :
    branchClaimRootValidB 5 22 (.patternThree 1) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 29).
@isnad1 id=eq.0h0v.s5.05b8c0b9a32d from=translated src=- shape=e9e0773c vocab=87b9965e
-/
theorem coverageBranchRoot_2_29 :
    branchClaimRootValidB 2 29 (.search branchClaims2Row29) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 30).
@isnad1 id=eq.0h0v.s5.8b39ed3787a6 from=translated src=- shape=e9e0773c vocab=3ea8f158
-/
theorem coverageBranchRoot_2_30 :
    branchClaimRootValidB 2 30 (.search branchClaims2Row30) = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 28), starting at 64.
@isnad1 id=eq.0h0v.s3.cc890215eba1 from=translated src=- shape=6f582f20 vocab=7368fc0c
-/
theorem coverageBranchNodes_2_28_00064 :
    nodeClaimChunkValidB branchClaims2Row28 64 32 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 29), starting at 0.
@isnad1 id=eq.0h0v.s3.9d2567c07d64 from=translated src=- shape=6f582f20 vocab=3d488bbc
-/
theorem coverageBranchNodes_2_29_00000 :
    nodeClaimChunkValidB branchClaims2Row29 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 29), starting at 64.
@isnad1 id=eq.0h0v.s3.098db83c5d16 from=translated src=- shape=6f582f20 vocab=3d488bbc
-/
theorem coverageBranchNodes_2_29_00064 :
    nodeClaimChunkValidB branchClaims2Row29 64 39 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 30), starting at 0.
@isnad1 id=eq.0h0v.s3.b47fb3007895 from=translated src=- shape=6f582f20 vocab=aa47b7e8
-/
theorem coverageBranchNodes_2_30_00000 :
    nodeClaimChunkValidB branchClaims2Row30 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
