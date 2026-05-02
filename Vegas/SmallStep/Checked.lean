import Vegas.FOSG.Observed.Kernel

/-!
# Checked PMF bridge for small-step semantics

The raw small-step layer uses `FDist` and omniscient full-state kernels. The
FOSG bridge uses checked worlds and legal, view-indexed PMF behavioral
profiles. This file exposes the existing checked one-step PMF kernel under the
small-step namespace and records the first bridge lemmas.
-/

namespace Vegas
namespace SmallStep
namespace Checked

open FOSGBridge
open FOSGBridge.Observed

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

end Checked
end SmallStep
end Vegas
