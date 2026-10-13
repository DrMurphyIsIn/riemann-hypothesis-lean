/-
  ArchS1_Guard -- axiom guard for stage S1 (the exact u-space Weil identity).
  Required output for every line: [propext, Classical.choice, Quot.sound].
  Run:  lake build ArchS1_Identity && lake env lean ArchS1_Guard.lean
-/
import ArchS1_Identity

-- the kernel k and its closed form
#print axioms ArchS1.hasSum_archK
#print axioms ArchS1.tsum_expK_kb
#print axioms ArchS1.tendsto_kTrunc
#print axioms ArchS1.archK_eq_tau
-- the limit machinery
#print axioms ArchS1.tendsto_phiN
#print axioms ArchS1.tendsto_cN
#print axioms ArchS1.truncated_identity
#print axioms ArchS1.integrable_dirichlet
-- the identity
#print axioms ArchS1.arch_integral_dirichlet
#print axioms ArchS1.archSide_autocorr_dirichlet_identity
#print axioms ArchS1.archSide_autocorr_dirichlet_identity'
#print axioms ArchS1.archSide_autocorr_dirichlet_identity_poleFree
#print axioms ArchS1.weilForm_autocorr_dirichlet_identity
