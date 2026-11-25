module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Source.BehavioralStateKernel
public import Vegas.Game.SourceContinuation

@[expose] public section

/-! # State kernel for the initialized source protocol -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace Setup

variable (setup : Setup (Player := Player) (L := L))
  (admission : CommitmentInterface setup.program)

/-- The actual initial protocol step samples setup once, irrespective of the
strategic profile. Correlations in the setup law are retained. -/
theorem behavioralStateStep_none
    (profile : Profile (setup.informationModel admission).behavioralSignature) :
    setup.behavioralStateStep admission profile none =
      setup.initialLaw.map (fun initial =>
        some (ProtocolState.entry setup.program (Config.initial initial))) := by
  simp [behavioralStateStep, protocolStep, PMF.bind_const]

/-- Encoding the syntactic policies gives exactly their action-marginal
kernel after setup, with only the existing `some` state embedding. -/
theorem behavioralStateStep_encoded_some
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program admission)
    (state : SourceProgram.ProtocolState setup.program) :
    setup.behavioralStateStep admission
        (fun who => setup.toProtocolBehavioralPolicy admission who (profile who) (permitted who))
        (some state) =
      (ProtocolState.behavioralStateStep setup.program profile state).map some := by
  classical
  by_cases stopped : ProtocolState.terminal setup.program state
  · simp [behavioralStateStep, ProtocolState.behavioralStateStep, stopped, PMF.pure_map]
  · simp only [behavioralStateStep, Option.elim_some, stopped, ite_false, protocolStep,
      ProtocolState.behavioralStateStep, PMF.map_bind]
    let choices who := setup.toProtocolBehavioralPolicy admission who
      (profile who) (permitted who) (setup.protocolObserve who (some state))
    have factors :
        independentProduct (fun who => (profile who).protocolAction setup.program
          (ProtocolState.observe who setup.program state)) =
        (independentProduct choices).map (fun selected who => (selected who).1) := by
      rw [independentProduct_map]
      congr 1
      funext who
      exact (setup.toProtocolBehavioralPolicy_map_val admission who (profile who)
        (permitted who) (some (ProtocolState.observe who setup.program state))).symm
    rw [factors, PMF.bind_map]
    rfl

end Setup

end Vegas.SourceProgram
