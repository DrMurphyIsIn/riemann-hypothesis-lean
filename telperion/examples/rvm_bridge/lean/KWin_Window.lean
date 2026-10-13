/-
  KWin_Window -- THE PRIME-FREE WINDOW at 2L = log 2, on the goal node's full test class, with no
  Arb seam (rvm_bridge island, 2026-09-24).

  conjecture1_proved = False.  A finite-window Weil positivity statement is NOT RH.  PR #604
  recorded that the 1.3e-3 full-class margin at this window is zero content: on the window the
  Weil form IS the zero sum (explicit formula), and over the first 200 zero pairs that sum is
  0.001301 against a least eigenvalue of 0.001329, so certifying the margin says nothing new about
  the zeros.  Nor is this Connes-Consani (arXiv 2006.13771, Theorem 1) or Yoshida (1992): their
  theorem is for a POLE-FREE class (Theorem 1 imposes paperFT g (i/2) = 0 and paperFT g 0 = 0).
  Numerical margins at this window: 0.547 on the class paperFT g (±i/2) = 0
  (PRIME_FREE_WINDOW_PLAN_2026-09-23.md table), 0.0723 on the one-condition class
  paperFT g (i/2) = 0, which stays positive to L ~ 0.3716 (2026-10-11 numerics).  The statement
  below keeps the pole terms, i.e. it is the goal node's full class.

  PROVED HERE, hypothesis-free (every numeric fact kernel-checked; the guard prints only Lean's
  three standard foundations propext / Classical.choice / Quot.sound):
    * evenSectorFloor / oddSectorFloor: Zhu's sector floors EvenSectorFloor / OddSectorFloor at
      L0 = log 2 / 2 with lam = 9/10000;
    * windowFloor_L0: WeilWindow.WindowFloor (log 2 / 2) (9/10000), via Zhu Lemma 6.1
      (`windowFloor_of_sectors`, ZhuParity);
    * kwin_primeFreeWindow: the LITERAL body of RvMBridge31.PrimeFreeWindowPositivity
      (E6Bridge31, origin/main):  for all g L, IsWeilTest g -> tsupport g ⊆ Icc (-L) L ->
      2 L <= log 2 -> 0 <= Re weilForm (autocorr g);
    * kwin_primeFreeWindowArch: the literal body of RvMBridge31.PrimeFreeWindowArchPositivity
      (Stage 0 re-proved below: the prime side of the autocorrelation vanishes on the window).
  After origin/main (E6Bridge31) is merged into this branch the bridge is one line:
      theorem primeFreeWindowPositivity : RvMBridge31.PrimeFreeWindowPositivity :=
        KWin.kwin_primeFreeWindow
  (the bodies are syntactically identical; E6Bridge31 opens WeilExplicit).

  THE ROUTE (Q = Re weilForm (autocorr v), real v of parity eps, supported in [-L0, L0]):
    Q >= Rb v v                        KWin_Split  (Zhu eq. (2) + split at T = 20, beta0 = 1.107)
    Rb v v >= (9/10000) int v^2        KWin_Tail   (projection tail, N = 12 even / 10 odd modes)
      <- Rb h h >= lam int h^2         KWin_Head   (pi-scaled head matrix; minorant; moments)
      <- psdCert (headMat ...) = true  KWin_Cert   (decide +kernel: exact LDL^T, re-verified)
      <- w_i <= Psi on 7 pieces        KWin_Minorant (digamma series, geometric Lorentzian bounds)
  No `sorry`.
-/
import KWin_Split
import KWin_Tail

open Real MeasureTheory Set

noncomputable section

namespace KWin
open WeilExplicit RvMBridgeZhu

/-! ## A. The two sector floors at L0 = log 2 / 2. -/

lemma lamFloor_cast : ((lamFloor : ℚ) : ℝ) = 9 / 10000 := by unfold lamFloor; push_cast; norm_num

/-- A real sector test: the common core of both sector floors. -/
theorem sector_floor_core {par N : ℕ} (hpar : par = 0 ∨ par = 1) {lam : ℚ}
    (htail : tailCond par N lam = true) (hcert : psdCert (headMat par N lam) N = true)
    (hginv : ginvCheck par N = true) {f : ℝ → ℂ} (hf : IsWeilTest f) (hre : ∀ x, (f x).im = 0)
    (hpf : ∀ x, f (-x) = (epsR par : ℂ) * f x) (hs : tsupport f ⊆ Icc (-L0) L0) :
    (9 / 10000 : ℝ) * (∫ x : ℝ, ‖f x‖ ^ 2) ≤ (WeilForm.weilForm (WeilForm.autocorr f)).re := by
  set v : ℝ → ℝ := fun u => (f u).re with hvdef
  have hfv : f = fun u => (v u : ℂ) := by
    funext u; exact Complex.ext (by simp [hvdef]) (by simp [hvdef, hre u])
  rw [hfv] at hf hs ⊢
  have hev : ∀ u, v (-u) = epsR par * v u := by
    intro u
    have h := congrArg Complex.re (hpf u)
    rw [hfv] at h
    simpa [epsR] using h
  have hQ := Q_ge_Rb hpar hf hev hs
  have hR := Rb_floor hpar htail hcert hginv (continuous_v hf)
  have hip : ip ellR v v = ∫ x : ℝ, ‖(v x : ℂ)‖ ^ 2 := by
    unfold ip
    rw [← integral_eq_interval hs]
    congr 1; funext x
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]; ring
  rw [lamFloor_cast, hip] at hR
  linarith

theorem evenSectorFloor : WeilWindow.EvenSectorFloor L0 (9 / 10000) := by
  intro f hf hre hev hs
  exact sector_floor_core (par := 0) (N := 12) (Or.inl rfl) tail_even cert_even ginv_even hf hre
    (fun x => by rw [hev x]; simp [epsR]) hs

theorem oddSectorFloor : WeilWindow.OddSectorFloor L0 (9 / 10000) := by
  intro f hf hre hodd hs
  exact sector_floor_core (par := 1) (N := 10) (Or.inr rfl) tail_odd cert_odd ginv_odd hf hre
    (fun x => by rw [hodd x]; simp [epsR]) hs

/-! ## B. The window floor and the prime-free window. -/

/-- **Zhu's window floor at the edge of the prime-free window**: every smooth compactly supported
test `f` (complex, no parity) supported in `[-log 2 / 2, log 2 / 2]` has
`Re weilForm (autocorr f) >= (9/10000) ||f||_2^2`. -/
theorem windowFloor_L0 : WeilWindow.WindowFloor L0 (9 / 10000) :=
  windowFloor_of_sectors evenSectorFloor oddSectorFloor

/-- The literal body of `RvMBridge31.PrimeFreeWindowPositivity` (E6Bridge31). -/
def PrimeFreeWindowPositivityBody : Prop :=
  ∀ (g : ℝ → ℂ) (L : ℝ), IsWeilTest g → tsupport g ⊆ Set.Icc (-L) L → 2 * L ≤ Real.log 2 →
    0 ≤ (weilForm (autocorr g)).re

/-- The literal body of `RvMBridge31.PrimeFreeWindowArchPositivity` (E6Bridge31). -/
def PrimeFreeWindowArchPositivityBody : Prop :=
  ∀ (g : ℝ → ℂ) (L : ℝ), IsWeilTest g → tsupport g ⊆ Set.Icc (-L) L → 2 * L ≤ Real.log 2 →
    0 ≤ (archSide (autocorr g)).re

/-- **THE PRIME-FREE WINDOW, PROVED** (hypothesis-free, no Arb seam): Weil positivity on the goal
node's full test class for every support window with `2 L <= log 2`. -/
theorem kwin_primeFreeWindow : PrimeFreeWindowPositivityBody := by
  intro g L hg hs hL
  have hLL : L ≤ L0 := by unfold L0; linarith
  have hs' : tsupport g ⊆ Icc (-L0) L0 := hs.trans (Icc_subset_Icc (by linarith) hLL)
  have h := windowFloor_L0 g hg hs'
  have hm : 0 ≤ ∫ x : ℝ, ‖g x‖ ^ 2 := integral_nonneg fun x => by positivity
  have h2 : (0 : ℝ) ≤ (9 / 10000) * ∫ x : ℝ, ‖g x‖ ^ 2 := by positivity
  rw [weilForm_autocorr_eq] at h
  linarith

/-! ## C. Stage 0 (re-proved from E6Bridge31): the prime side vanishes on the window. -/

lemma eq_zero_of_tsupport_subset_Icc_right' {f : ℝ → ℂ} {a b : ℝ} (hf : Continuous f)
    (hs : tsupport f ⊆ Set.Icc a b) {x : ℝ} (hx : b ≤ x) : f x = 0 := by
  by_contra h
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hf.continuousAt.eventually_ne h)
  have hne : f (x + ε / 2) ≠ 0 := hball (by rw [Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
  have hmem : x + ε / 2 ∈ tsupport f := subset_tsupport f (Function.mem_support.mpr hne)
  have := (hs hmem).2
  linarith

lemma eq_zero_of_tsupport_subset_Icc_left' {f : ℝ → ℂ} {a b : ℝ} (hf : Continuous f)
    (hs : tsupport f ⊆ Set.Icc a b) {x : ℝ} (hx : x ≤ a) : f x = 0 := by
  by_contra h
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hf.continuousAt.eventually_ne h)
  have hne : f (x - ε / 2) ≠ 0 := hball (by rw [Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
  have hmem : x - ε / 2 ∈ tsupport f := subset_tsupport f (Function.mem_support.mpr hne)
  have := (hs hmem).1
  linarith

lemma tsupport_autocorr_subset' {g : ℝ → ℂ} {L : ℝ} (hg : tsupport g ⊆ Set.Icc (-L) L) :
    tsupport (autocorr g) ⊆ Set.Icc (-(2 * L)) (2 * L) := by
  rw [RvMBridge5.autocorr_eq_weilTest]
  have h : tsupport g ⊆ Set.Icc (-((2 * L) / 2)) ((2 * L) / 2) := by
    rwa [show (2 * L) / 2 = L by ring]
  exact Zeta23.EF.tsupport_weilTest_subset h h

theorem primeSide_autocorr_eq_zero' {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) (hL : 2 * L ≤ Real.log 2) :
    primeSide (autocorr g) = 0 := by
  have hf : Continuous (autocorr g) := (RvMBridge5.isWeilTest_autocorr hg).1.continuous
  have hts := tsupport_autocorr_subset' hsupp
  unfold primeSide
  have hz : (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (autocorr g (Real.log n) + autocorr g (-Real.log n))) = fun _ => 0 := by
    funext n
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · simp
      · simp [ArithmeticFunction.vonMangoldt_apply_one]
    · have hlog : Real.log 2 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      have h1 : autocorr g (Real.log n) = 0 :=
        eq_zero_of_tsupport_subset_Icc_right' hf hts (by linarith)
      have h2 : autocorr g (-Real.log n) = 0 :=
        eq_zero_of_tsupport_subset_Icc_left' hf hts (by linarith)
      rw [h1, h2]
      simp
  rw [hz, tsum_zero]

/-- The archimedean form of the prime-free window (the literal body of
`RvMBridge31.PrimeFreeWindowArchPositivity`). -/
theorem kwin_primeFreeWindowArch : PrimeFreeWindowArchPositivityBody := by
  intro g L hg hs hL
  have h := kwin_primeFreeWindow g L hg hs hL
  have e : weilForm (autocorr g) = archSide (autocorr g) := by
    unfold weilForm
    rw [primeSide_autocorr_eq_zero' hg hs hL, sub_zero]
  rwa [e] at h

end KWin

end
