/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData04
public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData05
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 31).
@isnad1 id=eq.0h0v.s5.52c8ca7304d9 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_31 :
    branchClaimRootValidB 0 31 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 21).
@isnad1 id=eq.0h0v.s5.52acf8de1345 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_6_21 :
    branchClaimRootValidB 6 21 (.patternThree 1) = true := by
  decide +kernel

/-- Root audit for fixed branch (3, 5).
@isnad1 id=eq.0h0v.s5.ca933eb09bcf from=translated src=- shape=e9e0773c vocab=bed6444f
-/
theorem coverageBranchRoot_3_05 :
    branchClaimRootValidB 3 5 (.search branchClaims3Row5) = true := by
  decide +kernel

/-- Root audit for fixed branch (3, 6).
@isnad1 id=eq.0h0v.s5.b34b81551e3c from=translated src=- shape=e9e0773c vocab=4b473f3b
-/
theorem coverageBranchRoot_3_06 :
    branchClaimRootValidB 3 6 (.search branchClaims3Row6) = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 4), starting at 64.
@isnad1 id=eq.0h0v.s3.4a41a517dfc9 from=translated src=- shape=6f582f20 vocab=4d741516
-/
theorem coverageBranchNodes_3_04_00064 :
    nodeClaimChunkValidB branchClaims3Row4 64 50 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 5), starting at 0.
@isnad1 id=eq.0h0v.s3.144856e75bef from=translated src=- shape=6f582f20 vocab=5f335ad8
-/
theorem coverageBranchNodes_3_05_00000 :
    nodeClaimChunkValidB branchClaims3Row5 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 5), starting at 64.
@isnad1 id=eq.0h0v.s3.e25e08b8b549 from=translated src=- shape=6f582f20 vocab=5f335ad8
-/
theorem coverageBranchNodes_3_05_00064 :
    nodeClaimChunkValidB branchClaims3Row5 64 52 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 6), starting at 0.
@isnad1 id=eq.0h0v.s3.9c7419050ccb from=translated src=- shape=6f582f20 vocab=0fbd34af
-/
theorem coverageBranchNodes_3_06_00000 :
    nodeClaimChunkValidB branchClaims3Row6 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
