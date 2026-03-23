import Vegas.PureStrategic
import Vegas.Strategic

/-!
# PMF Behavioral Strategic Semantics

This file mirrors `Vegas.Strategic` and `Vegas.PureStrategic` but uses `PMF`
(Mathlib's probability mass functions) instead of `FDist` (rational Finsupp
distributions). The PMF layer is needed because the MAID Kuhn theorem produces
real-valued behavioral strategies, which are naturally PMF-valued.

Key definitions:
* `ProgramBehavioralKernelPMF` — PMF-valued behavioral kernel (no normalization
  witness needed since PMF is inherently normalized)
* `ProgramBehavioralStrategyPMF` — per-player PMF behavioral strategy
* `ProgramBehavioralProfilePMF` — joint PMF behavioral profile
* `outcomeDistBehavioralPMF` — PMF-valued outcome distribution

Key conversions:
* `ProgramBehavioralKernelPMF.ofPure` — pure kernel → PMF kernel (via `PMF.pure`)
* `ProgramBehavioralKernelPMF.ofFDist` — FDist kernel → PMF kernel (via `toPMF`)
* `ProgramPureProfile.toBehavioralPMF` — pure profile → PMF behavioral profile
* `ProgramBehavioralProfile.toPMFProfile` — FDist behavioral → PMF behavioral

Key agreement theorems:
* `outcomeDistBehavioralPMF_toBehavioralPMF_eq` — pure lift through PMF layer
  agrees with `outcomeDistPure.toPMF`
* `outcomeDistBehavioralPMF_toPMFProfile_eq` — FDist behavioral converted to
  PMF agrees with `outcomeDistBehavioral.toPMF`
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-! ## PMF behavioral kernel -/

/-- A PMF behavioral choice rule for one fixed commit site. Unlike
`ProgramBehavioralKernel` (FDist-valued), no explicit normalization witness
is needed because PMF is inherently normalized. -/
structure ProgramBehavioralKernelPMF
    (who : P) (Γ : VCtx P L) (b : L.Ty) where
  run : ViewEnv (P := P) (L := L) who Γ → PMF (L.Val b)

namespace ProgramBehavioralKernelPMF

/-- Turn a deterministic local rule into a PMF behavioral local rule. -/
noncomputable def ofPure
    {who : P} {Γ : VCtx P L} {b : L.Ty}
    (κ : PureKernel (P := P) (L := L) who Γ b) :
    ProgramBehavioralKernelPMF (P := P) (L := L) who Γ b :=
  { run := fun view => PMF.pure (κ view) }

@[simp] theorem run_ofPure
    {who : P} {Γ : VCtx P L} {b : L.Ty}
    (κ : PureKernel (P := P) (L := L) who Γ b)
    (view : ViewEnv (P := P) (L := L) who Γ) :
    (ofPure (P := P) (L := L) κ).run view = PMF.pure (κ view) := rfl

/-- Convert an FDist behavioral kernel to a PMF behavioral kernel. -/
noncomputable def ofFDist
    {who : P} {Γ : VCtx P L} {b : L.Ty}
    (κ : ProgramBehavioralKernel (P := P) (L := L) who Γ b) :
    ProgramBehavioralKernelPMF (P := P) (L := L) who Γ b :=
  { run := fun view => (κ.run view).toPMF (κ.normalized view) }

@[simp] theorem run_ofFDist
    {who : P} {Γ : VCtx P L} {b : L.Ty}
    (κ : ProgramBehavioralKernel (P := P) (L := L) who Γ b)
    (view : ViewEnv (P := P) (L := L) who Γ) :
    (ofFDist (P := P) (L := L) κ).run view =
      (κ.run view).toPMF (κ.normalized view) := rfl

end ProgramBehavioralKernelPMF

/-! ## PMF behavioral strategy and profile -/

/-- Player-`who` PMF behavioral strategies for the fixed program `p`: one
PMF choice rule for each commit site of `p` owned by `who`. -/
def ProgramBehavioralStrategyPMF (who : P) :
    {Γ : VCtx P L} → VegasCore P L Γ → Type
  | _, .ret _ => PUnit
  | _, .letExpr _ _ k => ProgramBehavioralStrategyPMF who k
  | _, .sample _ _ _ _ k => ProgramBehavioralStrategyPMF who k
  | Γ, .commit _ owner (b := b) _ k =>
      if owner = who then
        ProgramBehavioralKernelPMF (P := P) (L := L) who Γ b ×
          ProgramBehavioralStrategyPMF who k
      else
        ProgramBehavioralStrategyPMF who k
  | _, .reveal _ _ _ _ k => ProgramBehavioralStrategyPMF who k

/-- Joint PMF behavioral strategy profile for the fixed program `p`. -/
abbrev ProgramBehavioralProfilePMF {Γ : VCtx P L} (p : VegasCore P L Γ) : Type :=
  ∀ who, ProgramBehavioralStrategyPMF (P := P) (L := L) who p

namespace ProgramBehavioralStrategyPMF

/-- Extract the current player's PMF behavioral rule at the head commit site. -/
def headKernel
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramBehavioralStrategyPMF (P := P) (L := L) who (.commit x who R k)) :
    ViewEnv (P := P) (L := L) who Γ → PMF (L.Val b) := by
  let σ' : ProgramBehavioralKernelPMF (P := P) (L := L) who Γ b ×
      ProgramBehavioralStrategyPMF (P := P) (L := L) who k := by
    simpa [ProgramBehavioralStrategyPMF] using σ
  exact σ'.1.run

/-- Drop the head commit-site choice rule from the acting player's strategy. -/
def tailOwn
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramBehavioralStrategyPMF (P := P) (L := L) who (.commit x who R k)) :
    ProgramBehavioralStrategyPMF (P := P) (L := L) who k := by
  let σ' : ProgramBehavioralKernelPMF (P := P) (L := L) who Γ b ×
      ProgramBehavioralStrategyPMF (P := P) (L := L) who k := by
    simpa [ProgramBehavioralStrategyPMF] using σ
  exact σ'.2

end ProgramBehavioralStrategyPMF

namespace ProgramBehavioralProfilePMF

/-- Drop the head commit site from a PMF behavioral profile. -/
def tail
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramBehavioralProfilePMF (P := P) (L := L) (.commit x who R k)) :
    ProgramBehavioralProfilePMF (P := P) (L := L) k :=
  fun i =>
    by
      by_cases h : who = i
      · subst h
        exact ProgramBehavioralStrategyPMF.tailOwn (P := P) (L := L) (σ who)
      · simpa [ProgramBehavioralStrategyPMF, h] using σ i

end ProgramBehavioralProfilePMF

/-! ## PMF behavioral outcome distribution -/

/-- Evaluate a fixed-program PMF behavioral profile directly, threading the
continuation profile through the program structure. At sample nodes, the FDist
from nature is converted to a PMF via `NormalizedDists`. -/
noncomputable def outcomeDistBehavioralPMF :
    {Γ : VCtx P L} →
      (p : VegasCore P L Γ) →
      NormalizedDists p →
      ProgramBehavioralProfilePMF (P := P) (L := L) p →
      VEnv (Player := P) L Γ →
      PMF (Outcome P)
  | _, .ret payoffs, _, _, env =>
      PMF.pure (evalPayoffs payoffs env)
  | _, .letExpr x e k, hd, σ, env =>
      outcomeDistBehavioralPMF k hd σ <|
        VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
          (L.eval e (VEnv.erasePubEnv env)) env
  | _, .sample x τ m D' k, hd, σ, env =>
      ((L.evalDist D' (VEnv.eraseDistEnv τ m env)).toPMF (hd.1 env)).bind
        (fun v =>
          outcomeDistBehavioralPMF k hd.2 σ
            (VEnv.cons (Player := P) (L := L) (x := x) (τ := τ) v env))
  | _, .commit x who (b := b) _ k, hd, σ, env =>
      (ProgramBehavioralStrategyPMF.headKernel (P := P) (L := L) (σ who)
        (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env))).bind
        (fun v =>
          outcomeDistBehavioralPMF k hd
            (ProgramBehavioralProfilePMF.tail (P := P) (L := L) σ)
            (VEnv.cons (Player := P) (L := L) (x := x)
              (τ := .hidden who b) v env))
  | _, .reveal y _who _x (b := b) hx k, hd, σ, env =>
      let v : L.Val b := VEnv.get (Player := P) (L := L) env hx
      outcomeDistBehavioralPMF k hd σ
        (VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub b) v env)

/-! ## Pure → PMF behavioral lift -/

namespace ProgramPureProfile

/-- Lift a fixed-program pure profile to a PMF behavioral profile. -/
noncomputable def toBehavioralPMF :
    {Γ : VCtx P L} →
      (p : VegasCore P L Γ) →
      ProgramPureProfile (P := P) (L := L) p →
      ProgramBehavioralProfilePMF (P := P) (L := L) p
  | _, .ret _, _ => fun _ => PUnit.unit
  | _, .letExpr _ _ k, σ => toBehavioralPMF k σ
  | _, .sample _ _ _ _ k, σ => toBehavioralPMF k σ
  | _, .commit _ who R k, σ =>
      fun i =>
        by
          by_cases h : who = i
          · subst h
            simpa [ProgramBehavioralStrategyPMF] using
              (ProgramBehavioralKernelPMF.ofPure (P := P) (L := L)
                (ProgramPureStrategy.headKernel (P := P) (L := L) (σ who)),
               toBehavioralPMF k (tail (P := P) (L := L) σ) who)
          · simpa [ProgramBehavioralStrategyPMF, h] using
              toBehavioralPMF k (tail (P := P) (L := L) σ) i
  | _, .reveal _ _ _ _ k, σ => toBehavioralPMF k σ

@[simp] theorem tail_toBehavioralPMF
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramPureProfile (P := P) (L := L) (.commit x who R k)) :
    ProgramBehavioralProfilePMF.tail (P := P) (L := L)
      (toBehavioralPMF (.commit x who R k) σ) =
      toBehavioralPMF k (tail (P := P) (L := L) σ) := by
  funext i
  by_cases h : who = i
  · subst h
    simp [toBehavioralPMF, ProgramBehavioralProfilePMF.tail,
      ProgramBehavioralStrategyPMF.tailOwn]
  · simp [toBehavioralPMF, ProgramBehavioralProfilePMF.tail, h]

end ProgramPureProfile

/-! ## FDist behavioral → PMF behavioral conversion -/

namespace ProgramBehavioralProfile

/-- Convert an FDist behavioral profile to a PMF behavioral profile. -/
noncomputable def toPMFProfile :
    {Γ : VCtx P L} →
      (p : VegasCore P L Γ) →
      ProgramBehavioralProfile (P := P) (L := L) p →
      ProgramBehavioralProfilePMF (P := P) (L := L) p
  | _, .ret _, _ => fun _ => PUnit.unit
  | _, .letExpr _ _ k, σ => toPMFProfile k σ
  | _, .sample _ _ _ _ k, σ => toPMFProfile k σ
  | _, .commit _ who R k, σ =>
      fun i =>
        by
          by_cases h : who = i
          · subst h
            -- Extract the FDist kernel and convert to PMF
            let σ_who := σ who
            let σ_pair : ProgramBehavioralKernel (P := P) (L := L) who _ _ ×
                ProgramBehavioralStrategy (P := P) (L := L) who k := by
              simpa [ProgramBehavioralStrategy] using σ_who
            simpa [ProgramBehavioralStrategyPMF] using
              (ProgramBehavioralKernelPMF.ofFDist (P := P) (L := L) σ_pair.1,
               toPMFProfile k (ProgramBehavioralProfile.tail (P := P) (L := L) σ) who)
          · simpa [ProgramBehavioralStrategyPMF, h] using
              toPMFProfile k (ProgramBehavioralProfile.tail (P := P) (L := L) σ) i
  | _, .reveal _ _ _ _ k, σ => toPMFProfile k σ

@[simp] theorem tail_toPMFProfile
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramBehavioralProfile (P := P) (L := L) (.commit x who R k)) :
    ProgramBehavioralProfilePMF.tail (P := P) (L := L) (toPMFProfile (.commit x who R k) σ) =
      toPMFProfile k (ProgramBehavioralProfile.tail (P := P) (L := L) σ) := by
  funext i
  by_cases h : who = i
  · subst h
    simp [toPMFProfile, ProgramBehavioralProfilePMF.tail,
      ProgramBehavioralStrategyPMF.tailOwn]
  · simp [toPMFProfile, ProgramBehavioralProfilePMF.tail, h]

end ProgramBehavioralProfile

/-! ## Agreement: pure lift through PMF = outcomeDistPure.toPMF -/

/-- Running the PMF behavioral lift of a pure profile yields the same outcome
distribution as `outcomeDistPure.toPMF`. -/
theorem outcomeDistBehavioralPMF_toBehavioralPMF_eq
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (σ : ProgramPureProfile (P := P) (L := L) p)
    (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p) :
    outcomeDistBehavioralPMF p hd
      (ProgramPureProfile.toBehavioralPMF (P := P) (L := L) p σ) env =
      (outcomeDistPure p σ env).toPMF
        (outcomeDistPure_totalWeight_eq_one hd) := by
  induction p with
  | ret u =>
      simp [outcomeDistBehavioralPMF, outcomeDistPure, FDist.toPMF_pure]
  | letExpr x e k ih =>
      simpa [outcomeDistBehavioralPMF, outcomeDistPure,
        ProgramPureProfile.toBehavioralPMF] using ih σ _ hd
  | sample x τ m D' k ih =>
      simp only [outcomeDistBehavioralPMF, outcomeDistPure]
      rw [FDist.toPMF_bind (L.evalDist D' (VEnv.eraseDistEnv τ m env))
        (fun v => outcomeDistPure k σ (VEnv.cons (Player := P) (L := L)
          (x := x) (τ := τ) v env))
        (hd.1 env)
        (fun v => outcomeDistPure_totalWeight_eq_one hd.2)]
      congr 1; funext v
      exact ih σ _ hd.2
  | commit x who R k ih =>
      simp only [outcomeDistBehavioralPMF, outcomeDistPure]
      have hhead :
          ProgramBehavioralStrategyPMF.headKernel (P := P) (L := L)
            ((ProgramPureProfile.toBehavioralPMF
              (P := P) (L := L) (.commit x who R k) σ) who)
            (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env)) =
          PMF.pure
            ((ProgramPureStrategy.headKernel (P := P) (L := L) (σ who))
              (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env))) := by
        simp [ProgramPureProfile.toBehavioralPMF, ProgramBehavioralStrategyPMF.headKernel,
          ProgramBehavioralKernelPMF.ofPure, ProgramPureStrategy.headKernel]
      rw [hhead, PMF.pure_bind]
      rw [ProgramPureProfile.tail_toBehavioralPMF]
      exact ih (ProgramPureProfile.tail (P := P) (L := L) σ)
        (VEnv.cons (Player := P) (L := L) (x := x) (τ := .hidden who _)
          ((ProgramPureStrategy.headKernel (P := P) (L := L) (σ who))
            (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env))) env) hd
  | reveal y who x hx k ih =>
      simpa [outcomeDistBehavioralPMF, outcomeDistPure,
        ProgramPureProfile.toBehavioralPMF] using ih σ _ hd

/-! ## Agreement: FDist behavioral converted to PMF = outcomeDistBehavioral.toPMF -/

/-- Running the PMF conversion of an FDist behavioral profile yields the same
outcome distribution as `outcomeDistBehavioral.toPMF`. -/
theorem outcomeDistBehavioralPMF_toPMFProfile_eq
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (σ : ProgramBehavioralProfile (P := P) (L := L) p)
    (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p) :
    outcomeDistBehavioralPMF p hd
      (ProgramBehavioralProfile.toPMFProfile (P := P) (L := L) p σ) env =
      (outcomeDistBehavioral p σ env).toPMF
        (outcomeDistBehavioral_totalWeight_eq_one hd) := by
  induction p with
  | ret u =>
      simp [outcomeDistBehavioralPMF, outcomeDistBehavioral, FDist.toPMF_pure]
  | letExpr x e k ih =>
      simpa [outcomeDistBehavioralPMF, outcomeDistBehavioral,
        ProgramBehavioralProfile.toPMFProfile] using ih σ _ hd
  | sample x τ m D' k ih =>
      simp only [outcomeDistBehavioralPMF, outcomeDistBehavioral]
      rw [FDist.toPMF_bind (L.evalDist D' (VEnv.eraseDistEnv τ m env))
        (fun v => outcomeDistBehavioral k σ (VEnv.cons (Player := P) (L := L)
          (x := x) (τ := τ) v env))
        (hd.1 env)
        (fun v => outcomeDistBehavioral_totalWeight_eq_one hd.2)]
      congr 1; funext v
      exact ih σ _ hd.2
  | commit x who R k ih =>
      simp only [outcomeDistBehavioralPMF, outcomeDistBehavioral]
      -- The head kernel of the PMF profile is toPMF of the FDist head kernel
      have hhead :
          ProgramBehavioralStrategyPMF.headKernel (P := P) (L := L)
            ((ProgramBehavioralProfile.toPMFProfile
              (P := P) (L := L) (.commit x who R k) σ) who)
            (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env)) =
          (ProgramBehavioralStrategy.headKernel (P := P) (L := L) (σ who)
            (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env))).toPMF
          (ProgramBehavioralStrategy.headKernel_normalized (P := P) (L := L) (σ who)
            (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env))) := by
        simp [ProgramBehavioralProfile.toPMFProfile,
          ProgramBehavioralStrategyPMF.headKernel,
          ProgramBehavioralKernelPMF.ofFDist,
          ProgramBehavioralStrategy.headKernel]
      rw [hhead]
      rw [FDist.toPMF_bind
        (ProgramBehavioralStrategy.headKernel (P := P) (L := L) (σ who)
          (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env)))
        (fun v => outcomeDistBehavioral k
          (ProgramBehavioralProfile.tail (P := P) (L := L) σ)
          (VEnv.cons (Player := P) (L := L) (x := x) (τ := .hidden who _) v env))
        (ProgramBehavioralStrategy.headKernel_normalized (P := P) (L := L) (σ who)
          (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env)))
        (fun v => outcomeDistBehavioral_totalWeight_eq_one
          (σ := ProgramBehavioralProfile.tail (P := P) (L := L) σ) hd)]
      congr 1; funext v
      rw [ProgramBehavioralProfile.tail_toPMFProfile]
      exact ih (ProgramBehavioralProfile.tail (P := P) (L := L) σ) _ hd
  | reveal y who x hx k ih =>
      simpa [outcomeDistBehavioralPMF, outcomeDistBehavioral,
        ProgramBehavioralProfile.toPMFProfile] using ih σ _ hd

end Vegas
