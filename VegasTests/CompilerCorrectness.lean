/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CompilerCorrectness
import Vegas.Game.SourceProtocolNash
import Vegas.Examples.ProgramPaymentsRuntimeService

/-! # Failed binding and withholding on the actual bounded runtime

The clients execute omission, opaque admission, Boolean value bindings and
disclosure choices in the same checked payment service. The exact readout
retains typed cells, public default timing and executable payouts jointly.
-/

noncomputable section

namespace VegasTests.CompilerCorrectness

open Vegas Vegas.SourceProgram Vegas.EventGraphRuntime Interaction
  GameTheory GameTheory.Protocol GameTheory.Math.Probability
open Vegas.Examples.ProgramPayments
open Vegas.Examples.ProgramPaymentsRuntime

private def chosenProfile (bonus : Int) (binding : Option (PublicationResult Bool))
    (disclose : Bool) :
    BehavioralProfile (program bonus) := fun _ =>
  (fun _ _ _ => PMF.pure binding, (fun _ _ _ => PMF.pure disclose, PUnit.unit))

private def fullAdmission (bonus : Int) : CommitmentInterface (program bonus) :=
  CommitmentInterface.forfeiture (program bonus)

private theorem permitted (bonus : Int) (binding : Option (PublicationResult Bool))
    (disclose : Bool)
    (who : Player) :
    (chosenProfile bonus binding disclose who).Admitted (program bonus) (fullAdmission bonus) := by
  constructor
  · intro _ _ _ selected _
    cases selected with
    | none => trivial
    | some result => cases result <;> trivial
  · trivial

private def terminal (bonus : Int) (binding : Option (PublicationResult Bool)) (disclose : Bool) :
    State simpleExpr (program bonus).terminalCtx × DefaultHistory Player :=
  (Env.cons (if disclose then binding.getD .failure else .failure)
      (Env.cons (binding.getD .failure) initial),
    ⟨[if binding.isNone then none else
        if disclose && (binding.getD .failure).isSuccess then none else some .alice,
      if binding.isNone then some .alice else none]⟩)

/-- Includes successful bindings, omission, opaque admission, and voluntary withholding,
with their full typed output and executable payout on the bounded raw interface. -/
example (bonus : Int) (binding : Option (PublicationResult Bool)) (disclose : Bool) :
    let source := (setup bonus).encodeBehavioralProfile (fullAdmission bonus)
      (chosenProfile bonus binding disclose) (permitted bonus binding disclose)
    ((service bonus).rawMenu.information (serviceInitialLaw (setup bonus) .sequential)
      (service bonus).horizon (service bonus).scheduler).runBehavioral
      ((service bonus).clientProfile (fullAdmission bonus) (service bonus).rawMenu
        (firstTurnTiming (setup bonus) 1 .sequential) source)
      (2 * (service bonus).horizon + 1) |>.map
        (fun history => (serviceSourceReadout (setup bonus) .sequential
          (service bonus).deadline (leaks bonus) history.state).map fun output =>
            ((output.state, output.defaults), (program bonus).evaluatePayoffs output.state)) =
      PMF.pure (some (terminal bonus binding disclose,
        (program bonus).evaluatePayoffs (terminal bonus binding disclose).1)) := by
  dsimp only
  have law := (service bonus).firstTurnClientProfile_outcome_law (fullAdmission bonus)
    (setup bonus).eventGraph.sequentialize_barrierOrdered 1
    ((setup bonus).encodeBehavioralProfile (fullAdmission bonus)
      (chosenProfile bonus binding disclose) (permitted bonus binding disclose))
    (fun output => (output, (program bonus).evaluatePayoffs output.1))
  change _ = ((setup bonus).run ((setup bonus).decodeBehavioralProfile (fullAdmission bonus)
    ((setup bonus).encodeBehavioralProfile (fullAdmission bonus)
      (chosenProfile bonus binding disclose) (permitted bonus binding disclose)))).map
      (fun output => some ((output.state, output.defaults),
        (program bonus).evaluatePayoffs output.state)) at law
  rw [Setup.decodeBehavioralProfile_encodeBehavioralProfile] at law
  have run : ((setup bonus).run (chosenProfile bonus binding disclose)).map
      (fun final => (final.state, final.defaults)) =
        PMF.pure (terminal bonus binding disclose) := by
    change ((PMF.pure initial).bind _).map _ = _
    rw [PMF.pure_bind]
    change ((PMF.pure binding).bind _).map _ = _
    rw [PMF.pure_bind]
    cases binding with
    | none =>
        change ((PMF.pure false).bind _).map _ = _
        rw [PMF.pure_bind]
        change (PMF.pure _).map _ = _
        rw [PMF.pure_map]
        cases disclose <;> rfl
    | some result =>
        change ((PMF.pure disclose).bind _).map _ = _
        rw [PMF.pure_bind]
        change (PMF.pure _).map _ = _
        rw [PMF.pure_map]
        cases result with
        | failure => cases disclose <;> rfl
        | success value => cases value <;> cases disclose <;> rfl
  have projected := congrArg (PMF.map (fun output =>
    some (output, (program bonus).evaluatePayoffs output.1))) run
  simp only [PMF.map_comp, Function.comp_def, PMF.pure_map] at projected
  rw [projected] at law
  exact law

end VegasTests.CompilerCorrectness
