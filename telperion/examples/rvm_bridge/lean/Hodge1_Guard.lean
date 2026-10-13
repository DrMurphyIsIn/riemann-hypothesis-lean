/-
  Hodge1_Guard -- axiom guard for the HODGE-1 Phase 1 modules (Hodge1_Strip, Hodge1_Reduction) and the
  Phase 1b-A strip certificate (Hodge1_KPen ... Hodge1_Window45) and the Phase 1b-B direct pole-free
  certificate (Hodge1_PoleFreeWindow ... Hodge1_Window5493, with its three negative controls).
  Run: lake env lean Hodge1_Guard.lean.  Expected for every line: [propext, Classical.choice, Quot.sound].
  NOTE for replay audits: the Phase 1b-B kernel-evaluation declarations (Hodge1_Rows5493E/O, the row blocks
  of Hodge1_Cert5493E/O/N/Q/W) carry `set_option maxHeartbeats 0`, because the kernel enforces the
  heartbeat budget on `decide +kernel` and these evaluations exceed the default.  It lifts a resource
  limit only; the kernel still checks every reduction step, and no axiom is added.
-/
import Hodge1_Reduction
import Hodge1_Window45
import Hodge1_Window5493
import Hodge1_Ldl5493N
import Hodge1_Ldl5493Q
import Hodge1_Ldl5493W
import Hodge1_RHReduction
import Hodge1_RegWindow45
import Hodge1_RegWindow5493
import Hodge1_RegRH

#print axioms Hodge1.re_autocorr_pair_le_stripEnergy
#print axioms Hodge1.primeSide_autocorr_eq_two
#print axioms Hodge1.re_weilForm_eq_archW_sub_prime
#print axioms Hodge1.weilForm_ge_archW_sub_strip
#print axioms Hodge1.weil_positivity_pole_free_of_arch
#print axioms Hodge1.paperFT_I_half
#print axioms Hodge1.paperFT_neg_I_half
#print axioms Hodge1.weil_positivity_pole_free2_of_arch
#print axioms Hodge1.weil_positivity_poleFree2_of_arch

-- Phase 1b-A: the archimedean strip certificate at l = 9/20.
#print axioms Hodge1.head_floorP
#print axioms Hodge1.RbP_floor
#print axioms Hodge1.RbP_le_archW
#print axioms Hodge1.archW_decomp
#print axioms Hodge1.archW_ge_of_sectors
#print axioms Hodge1.stripSet_le_SformC
#print axioms Hodge1.certE45
#print axioms Hodge1.certO45
#print axioms Hodge1.certE45_negative_control_lam
#print axioms Hodge1.certE45_negative_control_w2
#print axioms Hodge1.certO45_negative_control_lam
#print axioms Hodge1.evenStrip45
#print axioms Hodge1.oddStrip45
#print axioms Hodge1.arch_strip_window45
#print axioms Hodge1.hArch_window45
#print axioms Hodge1.weil_positivity_poleFree2_window45

-- Phase 1b-B: the direct pole-free certificate at L = 5493/10000.
#print axioms Hodge1.poleFree_sector_floor
#print axioms Hodge1.poleFree2_floor_of_sectors
#print axioms Hodge1.poleFree2_floor_of_cert
#print axioms Hodge1.certE5493
#print axioms Hodge1.certO5493
#print axioms Hodge1.certE5493_negative_control_lam
#print axioms Hodge1.certE5493_negative_control_q21
#print axioms Hodge1.certE5493_negative_control_w105
#print axioms Hodge1.twoL_le_log_three_5493
#print axioms Hodge1.poleFree2_floor5493
#print axioms Hodge1.weil_positivity_poleFree2_window5493
#print axioms Hodge1.poleFree2_iff_poleFree
#print axioms Hodge1.rh_iff_poleFree2_outside_window5493

-- Registry shapes (MMDefs vocabulary, root level) of the heavy mirrormere HODGE-1 nodes.
#print axioms weil_positivity_poleFree_window45
#print axioms weil_positivity_poleFree_window5493
#print axioms rh_iff_poleFree_outside_window5493
