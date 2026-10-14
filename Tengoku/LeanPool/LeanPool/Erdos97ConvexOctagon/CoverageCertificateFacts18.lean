/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData02
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 18).
@isnad1 id=eq.0h0v.s5.2d7a1fef5c1e from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_18 :
    branchClaimRootValidB 0 18 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 1).
@isnad1 id=eq.0h0v.s5.ac577c54807b from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_5_01 :
    branchClaimRootValidB 5 1 (.patternThree 180) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 11).
@isnad1 id=eq.0h0v.s5.38c6a3836aa9 from=translated src=- shape=e9e0773c vocab=6c347e52
-/
theorem coverageBranchRoot_2_11 :
    branchClaimRootValidB 2 11 (.search branchClaims2Row11) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 12).
@isnad1 id=eq.0h0v.s5.27e8057f6e21 from=translated src=- shape=e9e0773c vocab=ad0f81fe
-/
theorem coverageBranchRoot_2_12 :
    branchClaimRootValidB 2 12 (.search branchClaims2Row12) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 14).
@isnad1 id=eq.0h0v.s5.f7629e427ba3 from=translated src=- shape=e9e0773c vocab=8a5d6489
-/
theorem coverageBranchRoot_2_14 :
    branchClaimRootValidB 2 14 (.search branchClaims2Row14) = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 11), starting at 0.
@isnad1 id=eq.0h0v.s3.7bc421662613 from=translated src=- shape=6f582f20 vocab=730f8ff3
-/
theorem coverageBranchNodes_2_11_00000 :
    nodeClaimChunkValidB branchClaims2Row11 0 15 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 12), starting at 0.
@isnad1 id=eq.0h0v.s3.46225afb6369 from=translated src=- shape=6f582f20 vocab=e54321c4
-/
theorem coverageBranchNodes_2_12_00000 :
    nodeClaimChunkValidB branchClaims2Row12 0 28 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 14), starting at 0.
@isnad1 id=eq.0h0v.s3.47a42df76fca from=translated src=- shape=6f582f20 vocab=6680e157
-/
theorem coverageBranchNodes_2_14_00000 :
    nodeClaimChunkValidB branchClaims2Row14 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 14), starting at 64.
@isnad1 id=eq.0h0v.s3.46af1044ef3c from=translated src=- shape=6f582f20 vocab=6680e157
-/
theorem coverageBranchNodes_2_14_00064 :
    nodeClaimChunkValidB branchClaims2Row14 64 56 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
