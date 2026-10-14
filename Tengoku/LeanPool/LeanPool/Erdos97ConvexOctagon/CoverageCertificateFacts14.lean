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

/-- Root audit for fixed branch (0, 14).
@isnad1 id=eq.0h0v.s5.36ccda64dbb7 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_14 :
    branchClaimRootValidB 0 14 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (4, 32).
@isnad1 id=eq.0h0v.s5.9deeeda58f49 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_32 :
    branchClaimRootValidB 4 32 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 3).
@isnad1 id=eq.0h0v.s5.11fa5da0ddf2 from=translated src=- shape=e9e0773c vocab=e909b4c9
-/
theorem coverageBranchRoot_2_03 :
    branchClaimRootValidB 2 3 (.search branchClaims2Row3) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 4).
@isnad1 id=eq.0h0v.s5.8752c1d31d21 from=translated src=- shape=e9e0773c vocab=f86791c3
-/
theorem coverageBranchRoot_2_04 :
    branchClaimRootValidB 2 4 (.search branchClaims2Row4) = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 2), starting at 64.
@isnad1 id=eq.0h0v.s3.0bcfeba56c4f from=translated src=- shape=6f582f20 vocab=5298d63b
-/
theorem coverageBranchNodes_2_02_00064 :
    nodeClaimChunkValidB branchClaims2Row2 64 51 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 3), starting at 0.
@isnad1 id=eq.0h0v.s3.2f85563128bc from=translated src=- shape=6f582f20 vocab=aab33d78
-/
theorem coverageBranchNodes_2_03_00000 :
    nodeClaimChunkValidB branchClaims2Row3 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 3), starting at 64.
@isnad1 id=eq.0h0v.s3.60d60c761fe9 from=translated src=- shape=6f582f20 vocab=aab33d78
-/
theorem coverageBranchNodes_2_03_00064 :
    nodeClaimChunkValidB branchClaims2Row3 64 48 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 4), starting at 0.
@isnad1 id=eq.0h0v.s3.0ee7e50b09d9 from=translated src=- shape=6f582f20 vocab=354d6409
-/
theorem coverageBranchNodes_2_04_00000 :
    nodeClaimChunkValidB branchClaims2Row4 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
