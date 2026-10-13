/-
  ArchS9_Guard -- axiom guard of archimedean stage S9 (certified prolate engine), 2026-10-11.
  Every line must print exactly [propext, Classical.choice, Quot.sound]
  (`lake env lean ArchS9_Guard.lean`).  conjecture1_proved = False.
-/
import ArchS9_Bridge

-- pi enclosure
#print axioms ArchS9.pi_gt_d45
#print axioms ArchS9.pi_lt_d45
-- analytic core
#print axioms ArchS9.ip_sq_le
#print axioms ArchS9.L1_sq_le
#print axioms ArchS9.sqrt_ip_add_le
#print axioms ArchS9.T_sub_le
#print axioms ArchS9.Td_sub_le
#print axioms ArchS9.hasDerivAt_T
#print axioms ArchS9.continuous_T
-- generic frame
#print axioms ArchS9.ip_psi_psi
#print axioms ArchS9.rankJ_identity
#print axioms ArchS9.abs_errF_le
#print axioms ArchS9.abs_errdF_le
#print axioms ArchS9.P1
#print axioms ArchS9.P2
#print axioms ArchS9.P3
#print axioms ArchS9.hasDerivAt_eig
#print axioms ArchS9.round_step
#print axioms ArchS9.localize
#print axioms ArchS9.value_bound
#print axioms ArchS9.ip_ne_zero_of_overlap
-- kernel certificates
#print axioms ArchS9.Data.gram_rows_1
#print axioms ArchS9.Data.gram_rows_2
#print axioms ArchS9.Data.gram_rows_3
#print axioms ArchS9.Data.gram_rows_4
#print axioms ArchS9.Data.e_rows_1
#print axioms ArchS9.Data.e_rows_2
#print axioms ArchS9.Data.lc_ok
#print axioms ArchS9.Data.const_ok
#print axioms ArchS9.Data.windows_ok
#print axioms ArchS9.Data.loc_ok
#print axioms ArchS9.Data.window_negative_control
-- soundness and the certified prolate data
#print axioms ArchS9.gram_sound
#print axioms ArchS9.Em_eq
#print axioms ArchS9.dA_sound
#print axioms ArchS9.errF_le_one
#print axioms ArchS9.errF_le_two
#print axioms ArchS9.errdF_le_two
#print axioms ArchS9.prolate_localization
#print axioms ArchS9.prolate_window
#print axioms ArchS9.prolate_simple
-- interface with S6-S10
#print axioms ArchS9.Data.res_ok
#print axioms ArchS9.continuous_T_of_integrable
#print axioms ArchS9.continuous_representative
#print axioms ArchS9.T_symm
#print axioms ArchS9.psi_residual
#print axioms ArchS9.bessel_finite
#print axioms ArchS9.prolate_window_occupied
#print axioms ArchS9.prolate_spectrum_complete
#print axioms ArchS9.Data.lam_ok
#print axioms ArchS9.prolate_S8_fields
#print axioms ArchS9.prolate_phi_values
