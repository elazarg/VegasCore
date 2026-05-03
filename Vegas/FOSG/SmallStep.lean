import Vegas.FOSG.Observed.Kernel
import Vegas.SmallStep

/-!
# FOSG bridge for checked small-step semantics

The raw small-step layer uses `FDist` and omniscient full-state kernels. The
FOSG bridge uses checked worlds and legal, view-indexed PMF behavioral
profiles. This file exposes the existing checked one-step PMF kernel under the
FOSG small-step bridge namespace and records the bridge lemmas. It lives under `FOSG`
because the dependency direction is from the game-theoretic view to the
neutral small-step semantics, not the reverse.
-/

namespace Vegas
namespace FOSGBridge
namespace SmallStep
namespace Checked

open Observed

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Checked PMF one-step kernel induced by a legal Vegas behavioral profile.
This is an alias for the kernel already used by the observed-program FOSG
proof. -/
noncomputable abbrev stepPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (w : CheckedWorld g hctx) : PMF (CheckedWorld g hctx) :=
  checkedProfileStepPMF g hctx σ w

/-- Checked PMF continuation outcome value. -/
noncomputable abbrev outcomeValuePMF
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (σ : LegalProgramBehavioralProfilePMF g)
    (w : CheckedWorld g hctx) : PMF (Outcome P) :=
  checkedVegasOutcomeKernelPMF σ w

/-- One checked PMF step preserves the Vegas continuation outcome value. -/
theorem stepPMF_bind_outcomeValuePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (w : CheckedWorld g hctx) :
    (stepPMF g hctx σ w).bind (outcomeValuePMF σ) =
      outcomeValuePMF σ w := by
  exact checkedProfileStepPMF_bind_checkedVegasOutcomeKernelPMF g hctx σ w

/-- The FOSG legal action law followed by the FOSG transition collapses to the
checked PMF small-step kernel after forgetting cursor keys. -/
theorem legalActionLaw_bind_transition_eq_stepPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P, Fintype (Option (ProgramAction g.prog who))]
    (σ : LegalProgramBehavioralProfilePMF g)
    (h : (observedProgramFOSG g hctx).History)
    (hterm : ¬ (observedProgramFOSG g hctx).terminal h.lastState) :
    ((observedProgramFOSG g hctx).legalActionLaw
        (toObservedProgramLegalBehavioralProfilePMF g hctx σ) h hterm).bind
      (fun a =>
        PMF.map (CheckedWorld.ofCursorChecked (hctx := hctx))
          ((observedProgramFOSG g hctx).transition h.lastState a)) =
      stepPMF g hctx σ
        (CheckedWorld.ofCursorChecked (hctx := hctx) h.lastState) := by
  exact observedProgramLegalActionLawPMF_bind_checkedTransition_eq_checkedProfileStepPMF
    g hctx σ h hterm

/-- Running the observed-program FOSG and projecting terminal histories to
Vegas outcomes gives the checked small-step continuation value at the initial
checked world. -/
theorem mappedRunDist_eq_initialOutcomeValuePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfilePMF g) :
    PMF.map (observedProgramHistoryOutcome g hctx)
        (observedProgramRunDist g hctx LF
          (toObservedProgramLegalBehavioralProfilePMF g hctx σ)) =
      outcomeValuePMF σ (CheckedWorld.initial g hctx) := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  let R := observedProgramOutcomeValuePMF g hctx σ
  have hclosure :=
    R.map_observe_runDist_eq_value
      (syntaxSteps g.prog)
      (observedProgramFOSG_initial_remainingSyntaxSteps_le g hctx)
  simpa [R, observedProgramOutcomeValuePMF, observedProgramRunDist,
    outcomeValuePMF, CheckedWorld.initial] using hclosure

/-- Checked/FOSG outcome bridge in the existing strategic PMF game API. -/
theorem mappedRunDist_eq_toKernelGamePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfilePMF g) :
    PMF.map (observedProgramHistoryOutcome g hctx)
        (observedProgramRunDist g hctx LF
          (toObservedProgramLegalBehavioralProfilePMF g hctx σ)) =
      (toKernelGamePMF g).outcomeKernel σ := by
  exact observedProgramOutcomeKernelPMF_eq_toKernelGamePMF g hctx LF σ

/-! ## Raw `FDist` / checked `PMF` bridge -/

/-- Raw initial small-step evaluation is normalized when its omniscient profile
extends a normalized legal FDist behavioral profile. -/
theorem runInitialSmallStep_totalWeight_eq_one_of_extends
    (g : WFProgram P L)
    (β : LegalProgramBehavioralProfile g)
    (σ : OmniscientOperationalProfile P L)
    (hσ : σ.ExtendsBehavioralProfile g.prog (fun i => (β i).val)) :
    (Vegas.SmallStep.runInitialSmallStep σ g).totalWeight = 1 := by
  rw [Vegas.SmallStep.runInitialSmallStep_eq_outcomeDist]
  rw [outcomeDist_eq_outcomeDistBehavioral_of_extends
    (p := g.prog) (σ := σ) (β := fun i => (β i).val)
    (env := g.env) hσ]
  exact outcomeDistBehavioral_totalWeight_eq_one
    (p := g.prog) (σ := fun i => (β i).val)
    (env := g.env) g.normalized

/-- Raw small-step and checked PMF semantics agree for an FDist behavioral
profile converted to PMF.

The hypothesis `hσ` is the "omniscient unfolding" condition: every raw
full-state commit kernel used by `σ` agrees with the fixed-program behavioral
kernel after projecting the full environment to the active player's view.

There is no general converse bridge from arbitrary `PMF` behavioral profiles
back to raw `FDist` profiles: `FDist` has finite rational weights, while `PMF`
may carry real-valued probabilities. -/
theorem runInitialSmallStep_toPMF_eq_outcomeValuePMF_toPMFProfile
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (β : LegalProgramBehavioralProfile g)
    (σ : OmniscientOperationalProfile P L)
    (hσ : σ.ExtendsBehavioralProfile g.prog (fun i => (β i).val)) :
    (Vegas.SmallStep.runInitialSmallStep σ g).toPMF
        (runInitialSmallStep_totalWeight_eq_one_of_extends g β σ hσ) =
      outcomeValuePMF (LegalProgramBehavioralProfile.toPMFProfile β)
        (CheckedWorld.initial g hctx) := by
  let raw : ProgramBehavioralProfile g.prog := fun i => (β i).val
  have hrun :
      Vegas.SmallStep.runInitialSmallStep σ g =
        outcomeDistBehavioral g.prog raw g.env := by
    rw [Vegas.SmallStep.runInitialSmallStep_eq_outcomeDist]
    exact outcomeDist_eq_outcomeDistBehavioral_of_extends
      (p := g.prog) (σ := σ) (β := raw) (env := g.env) (by simpa [raw] using hσ)
  have hpmf :
      outcomeDistBehavioralPMF g.prog g.normalized
          (ProgramBehavioralProfile.toPMFProfile g.prog raw) g.env =
        (outcomeDistBehavioral g.prog raw g.env).toPMF
          (outcomeDistBehavioral_totalWeight_eq_one
            (p := g.prog) (σ := raw) (env := g.env) g.normalized) :=
    outcomeDistBehavioralPMF_toPMFProfile_eq
      (p := g.prog) (σ := raw) (env := g.env) (hd := g.normalized)
  ext oc
  have hchecked :
      outcomeValuePMF (LegalProgramBehavioralProfile.toPMFProfile β)
          (CheckedWorld.initial g hctx) oc =
        ((outcomeDistBehavioral g.prog raw g.env).toPMF
          (outcomeDistBehavioral_totalWeight_eq_one
            (p := g.prog) (σ := raw) (env := g.env) g.normalized)) oc := by
    simpa [outcomeValuePMF, checkedVegasOutcomeKernelPMF,
      CheckedWorld.initial, ProgramSuffix.behavioralProfilePMF,
      LegalProgramBehavioralProfile.toPMFProfile, raw]
      using congrArg (fun μ : PMF (Outcome P) => μ oc) hpmf
  calc
    ((Vegas.SmallStep.runInitialSmallStep σ g).toPMF
        (runInitialSmallStep_totalWeight_eq_one_of_extends g β σ hσ)) oc
        = (NNRat.toNNReal ((Vegas.SmallStep.runInitialSmallStep σ g) oc) :
            ENNReal) := by
          rw [FDist.toPMF_apply]
    _ = (NNRat.toNNReal ((outcomeDistBehavioral g.prog raw g.env) oc) :
            ENNReal) := by
          rw [hrun]
    _ = ((outcomeDistBehavioral g.prog raw g.env).toPMF
          (outcomeDistBehavioral_totalWeight_eq_one
            (p := g.prog) (σ := raw) (env := g.env) g.normalized)) oc := by
          rw [FDist.toPMF_apply]
    _ = outcomeValuePMF (LegalProgramBehavioralProfile.toPMFProfile β)
          (CheckedWorld.initial g hctx) oc := hchecked.symm

end Checked
end SmallStep
end FOSGBridge
end Vegas
