import GameTheory.Languages.FOSG.OutcomeClosure
import Vegas.FOSG.Observed.Kernel

namespace Vegas
namespace FOSGBridge

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace Observed

/-!
# Outcome-value refinement for the observed-program FOSG

This file instantiates the generic FOSG outcome-closure theorem with the Vegas
semantic continuation value.  The proof avoids identifying the whole FOSG run
with `checkedProfileRunPMF`; it only proves that one FOSG step preserves the
remaining Vegas outcome distribution.
-/

/-- The Vegas PMF continuation value on observed-program histories. -/
noncomputable def observedProgramOutcomeValuePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P, Fintype (Option (ProgramAction g.prog who))]
    (σ : LegalProgramBehavioralProfilePMF g) :
    GameTheory.FOSG.History.OutcomeValue
      (G := observedProgramFOSG g hctx)
      (toObservedProgramLegalBehavioralProfilePMF g hctx σ)
      (Outcome P) where
  rank := fun h => h.lastState.remainingSyntaxSteps
  observe := observedProgramHistoryOutcome g hctx
  value := fun h =>
    checkedVegasOutcomeKernelPMF (hctx := hctx) σ
      (CheckedWorld.ofCursorChecked (hctx := hctx) h.lastState)
  terminal_of_rank_zero := by
    intro h hrank
    exact (CursorCheckedWorld.terminal_iff_remainingSyntaxSteps_eq_zero
      (g := g) (w := h.lastState)).2 hrank
  terminal_value := by
    intro h hterm
    have hchecked :
        checkedTerminal
          (CheckedWorld.ofCursorChecked (hctx := hctx) h.lastState) := by
      exact (checkedTerminal_observedProgramHistoryCheckedWorld
        g hctx h).2 hterm
    simpa [observedProgramHistoryOutcome] using
      checkedVegasOutcomeKernelPMF_terminal
        (hctx := hctx) σ
        (CheckedWorld.ofCursorChecked (hctx := hctx) h.lastState)
        hchecked
  step_value := by
    intro h hterm
    let G := observedProgramFOSG g hctx
    let β := toObservedProgramLegalBehavioralProfilePMF g hctx σ
    let project : CursorCheckedWorld g → CheckedWorld g hctx :=
      CheckedWorld.ofCursorChecked (hctx := hctx)
    let valueChecked : CheckedWorld g hctx → PMF (Outcome P) :=
      checkedVegasOutcomeKernelPMF (hctx := hctx) σ
    have hproject :
        (G.legalActionLaw β h hterm).bind
            (fun a =>
              (G.transition h.lastState a).bind
                (fun dst =>
                  valueChecked
                    (project (h.extendByOutcome a dst).lastState))) =
          (G.legalActionLaw β h hterm).bind
            (fun a =>
              (G.transition h.lastState a).bind
                (fun dst => valueChecked (project dst))) := by
      refine Math.ProbabilityMassFunction.bind_congr_on_support
        (G.legalActionLaw β h hterm) _ _ ?_
      intro a _ha
      refine Math.ProbabilityMassFunction.bind_congr_on_support
        (G.transition h.lastState a) _ _ ?_
      intro dst hdst
      have hsupp : G.transition h.lastState a dst ≠ 0 := by
        simpa [PMF.mem_support_iff] using hdst
      change
        valueChecked
            (observedProgramHistoryCheckedWorld g hctx
              (h.extendByOutcome a dst)) =
          valueChecked (CheckedWorld.ofCursorChecked (hctx := hctx) dst)
      rw [observedProgramHistoryCheckedWorld_extendByOutcome_of_support
        g hctx h a dst hsupp]
    have hstep :
        (G.legalActionLaw β h hterm).bind
            (fun a => PMF.map project (G.transition h.lastState a)) =
          checkedProfileStepPMF g hctx σ
            (CheckedWorld.ofCursorChecked (hctx := hctx) h.lastState) := by
      simpa [G, β, project] using
        observedProgramLegalActionLawPMF_bind_checkedTransition_eq_checkedProfileStepPMF
          g hctx σ h hterm
    calc
      (G.legalActionLaw β h hterm).bind
          (fun a =>
            (G.transition h.lastState a).bind
              (fun dst =>
                valueChecked
                  (project (h.extendByOutcome a dst).lastState))) =
        (G.legalActionLaw β h hterm).bind
          (fun a =>
            (G.transition h.lastState a).bind
              (fun dst => valueChecked (project dst))) := hproject
      _ =
        ((G.legalActionLaw β h hterm).bind
          (fun a => PMF.map project (G.transition h.lastState a))).bind
          valueChecked := by
            rw [PMF.bind_bind]
            congr 1
            funext a
            simp [PMF.map, PMF.bind_bind]
      _ =
        (checkedProfileStepPMF g hctx σ
          (CheckedWorld.ofCursorChecked (hctx := hctx) h.lastState)).bind
          valueChecked := by
            rw [hstep]
      _ =
        checkedVegasOutcomeKernelPMF (hctx := hctx) σ
          (CheckedWorld.ofCursorChecked (hctx := hctx) h.lastState) := by
            exact checkedProfileStepPMF_bind_checkedVegasOutcomeKernelPMF
              g hctx σ
              (CheckedWorld.ofCursorChecked (hctx := hctx) h.lastState)
  step_rank := by
    intro h hterm a dst hsupp
    have hcursor :
        dst.remainingSyntaxSteps + 1 =
          h.lastState.remainingSyntaxSteps := by
      simpa [observedProgramFOSG] using
        cursorProgramTransition_remainingSyntaxSteps
          (g := g) h.lastState a dst hsupp
    rw [GameTheory.FOSG.History.extendByOutcome_of_support
      (h := h) (a := a) (dst := dst) hsupp]
    simpa using hcursor

/-- Outcome preservation for the observed-program FOSG, proved by the
continuation-value closure theorem rather than by a global run-distribution
simulation. -/
theorem observedProgramOutcomeKernelPMF_eq_toKernelGamePMF_by_value
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfilePMF g) :
    observedProgramOutcomeKernelPMF g hctx LF σ =
      (toKernelGamePMF g).outcomeKernel σ := by
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
      (by
        change
          (observedProgramFOSG g hctx).init.remainingSyntaxSteps ≤
            syntaxSteps g.prog
        change
          syntaxSteps ((ProgramCursor.here : ProgramCursor g.prog).prog) ≤
            syntaxSteps g.prog
        change syntaxSteps g.prog ≤ syntaxSteps g.prog
        exact Nat.le_refl (syntaxSteps g.prog))
  simpa [R, observedProgramOutcomeValuePMF, observedProgramOutcomeKernelPMF]
    using hclosure

end Observed

end FOSGBridge
end Vegas
