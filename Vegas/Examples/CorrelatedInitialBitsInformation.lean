/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.CorrelatedInitialBits
import Vegas.Game.IntendedPreservation

/-! # Remembered common-bit components at actual source information sets -/

noncomputable section

namespace Vegas.Examples.CorrelatedInitialBits

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

private theorem observed_state {state : setup.ProtocolState}
    (trace : setup.intendedProtocol.Trace state) (who : Player) :
    setup.intendedModel.infoOf who trace = setup.protocolObserve who state := by
  simp only [Setup.intendedModel, InformationModel.restrictMenu_infoOf]
  exact setup.protocol_info (CommitmentInterface.values program) who
    (restrictAvailable.trace trace)

/-- Equality of actual decision views retains equality of the common initial
signal. It uses the existing initial-cell observation theorem. -/
theorem signal_eq_of_information (who : Player) (view : setup.ProtocolView who)
    (first second : setup.intendedModel.InformationHistory who view)
    (firstPoint secondPoint : SourceProgram.ProtocolState program)
    (firstAt : first.1.state = some firstPoint) (secondAt : second.1.state = some secondPoint) :
    signal (ProtocolState.base program firstPoint) =
      signal (ProtocolState.base program secondPoint) := by
  have same := (observed_state first.1.trace who).symm.trans
    (first.2.trans second.2.symm) |>.trans (observed_state second.1.trace who)
  rw [firstAt, secondAt] at same
  have current : ProtocolState.observe who program firstPoint =
      ProtocolState.observe who program secondPoint := Option.some.inj same
  exact signal_eq_of_initial_observe_eq who
    (setup.intended_trace_initialSupport first.1.trace firstPoint firstAt)
    (setup.intended_trace_initialSupport second.1.trace secondPoint secondAt)
    (ProtocolState.sourceObserve_base_eq_of_observe_eq who program firstPoint secondPoint current)

/-- Every actual source information fiber of a conditional component
determines that component. The signal is obtained from each player's private
initial copy and retained source observation, without public disclosure. -/
theorem informationFiber_component (bit : Bool) (who : Player)
    (site : (setup.conditionInitial signal bit).intendedModel.InformationSite who) :
    ∀ history : setup.intendedModel.InformationHistory who site.1,
      setup.initialComponent signal bit history.1.state := by
  obtain ⟨anchor, _running, _action, _permitted⟩ := site.2
  have notRoot : anchor.1.state ≠ none := by
    intro root
    have active := InformationModel.InformationSite.active
      (M := (setup.conditionInitial signal bit).intendedModel) site anchor
    rw [root] at active
    exact active
  cases anchorAt : anchor.1.state with
  | none => exact False.elim (notRoot anchorAt)
  | some anchorPoint =>
      have baseMember := (setup.conditionInitial signal bit).intended_trace_initialSupport
        anchor.1.trace anchorPoint anchorAt
      have anchorSignal := (GameTheory.Math.Probability.mem_support_fiberPosterior
        (signal_supported bit) baseMember).1
      let original := setup.conditionInitial_informationHistory signal bit (signal_supported bit)
        who site.1 anchor
      intro history
      cases historyAt : history.1.state with
      | none => trivial
      | some point =>
          have same := signal_eq_of_information who site.1 original history anchorPoint point
            anchorAt historyAt
          exact same.symm.trans anchorSignal

/-- The exact proportional Bayes adapter applies to this correlated source,
with its information-fiber premise proved from the actual private views. -/
theorem conditional_bayesBelief (bit : Bool)
    (policies : ∀ who, setup.intendedModel.BehavioralPolicy who) (who : Player)
    (site : (setup.conditionInitial signal bit).intendedModel.InformationSite who)
    (conditionalPositive : 0 < (setup.conditionInitial signal bit).intendedModel.informationMass
      (fun who => setup.conditionInitial_policy signal bit who (policies who)) who site)
    (globalPositive : 0 < setup.intendedModel.informationMass policies who
      (setup.conditionInitial_informationSite signal bit (signal_supported bit) site)) :
    ((setup.conditionInitial signal bit).intendedModel.bayesBelief
      (fun who => setup.conditionInitial_policy signal bit who (policies who)) who site
        ((setup.conditionInitial signal bit).intended_decision_antichain who site)
        conditionalPositive).map
          (setup.conditionInitial_informationHistory signal bit (signal_supported bit) who site.1) =
      setup.intendedModel.bayesBelief policies who
        (setup.conditionInitial_informationSite signal bit (signal_supported bit) site)
          (setup.intended_decision_antichain who _) globalPositive :=
  setup.conditionInitial_bayesBelief signal bit (signal_supported bit) policies site
    (informationFiber_component bit who site) _ _ conditionalPositive globalPositive

end Vegas.Examples.CorrelatedInitialBits
