/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CompilerCorrectness
import Vegas.Game.SourceProtocolNash
import Vegas.Examples.ProgramPaymentsRuntimeService

/-! # Failed binding and withholding on the actual bounded runtime

The clients execute every Boolean binding result and disclosure choice in the
same checked payment service. The exact typed readout includes the original
binding even when no value is published, and the payout is observed jointly.
-/

noncomputable section

namespace VegasTests.CompilerCorrectness

open Vegas Vegas.SourceProgram Vegas.EventGraphRuntime Interaction
  GameTheory GameTheory.Protocol GameTheory.Math.Probability
open Vegas.Examples.ProgramPayments
open Vegas.Examples.ProgramPaymentsRuntime

private def chosenProfile (bonus : Int) (binding : PublicationResult Bool) (disclose : Bool) :
    BehavioralProfile (program bonus) := fun _ =>
  (fun _ _ => PMF.pure binding, (fun _ _ => PMF.pure disclose, PUnit.unit))

private def fullAdmission (bonus : Int) : CommitmentInterface (program bonus) :=
  CommitmentInterface.forfeiture (program bonus)

private theorem permitted (bonus : Int) (binding : PublicationResult Bool) (disclose : Bool)
    (who : Player) :
    (chosenProfile bonus binding disclose who).Admitted (program bonus) (fullAdmission bonus) := by
  constructor
  · intro _ _ selected _
    cases selected <;> trivial
  · trivial

private def terminal (bonus : Int) (binding : PublicationResult Bool) (disclose : Bool) :
    State simpleExpr (program bonus).terminalCtx :=
  Env.cons (if disclose then binding else .failure) (Env.cons binding initial)

/-- Includes successful bindings, irrevocable failure, and voluntary withholding,
with their full typed output and executable payout on the bounded raw interface. -/
example (bonus : Int) (binding : PublicationResult Bool) (disclose : Bool) :
    let source := (setup bonus).encodeBehavioralProfile (fullAdmission bonus)
      (chosenProfile bonus binding disclose) (permitted bonus binding disclose)
    ((service bonus).rawMenu.information (serviceInitialLaw (setup bonus) .sequential)
      (service bonus).horizon (service bonus).scheduler).runBehavioral
      ((service bonus).clientProfile (fullAdmission bonus) (service bonus).rawMenu
        (firstTurnTiming (setup bonus) 1 .sequential) source)
      (2 * (service bonus).horizon + 1) |>.map
        (fun history => (serviceSourceReadout (setup bonus) .sequential
          (service bonus).deadline (leaks bonus) history.state).map fun output =>
            (output, (program bonus).evaluatePayoffs output)) =
      PMF.pure (some (terminal bonus binding disclose,
        (program bonus).evaluatePayoffs (terminal bonus binding disclose))) := by
  dsimp only
  have law := (service bonus).firstTurnClientProfile_outcome_law (fullAdmission bonus)
    (setup bonus).eventGraph.sequentialize_barrierOrdered 1
    ((setup bonus).encodeBehavioralProfile (fullAdmission bonus)
      (chosenProfile bonus binding disclose) (permitted bonus binding disclose))
    (fun output => (output, (program bonus).evaluatePayoffs output))
  change _ = ((setup bonus).run ((setup bonus).decodeBehavioralProfile (fullAdmission bonus)
    ((setup bonus).encodeBehavioralProfile (fullAdmission bonus)
      (chosenProfile bonus binding disclose) (permitted bonus binding disclose)))).map
      (fun output => some (output, (program bonus).evaluatePayoffs output)) at law
  rw [Setup.decodeBehavioralProfile_encodeBehavioralProfile] at law
  have run : (setup bonus).run (chosenProfile bonus binding disclose) =
      PMF.pure (terminal bonus binding disclose) := by
    simp only [Setup.run, setup, PMF.pure_bind, SourceProgram.run, program,
      chosenProfile, runWith, commitKernel, revealKernel, afterCommit]
    cases binding with
    | failure => cases disclose <;> rfl
    | success value => cases value <;> cases disclose <;> rfl
  rw [run, PMF.pure_map] at law
  exact law

end VegasTests.CompilerCorrectness
