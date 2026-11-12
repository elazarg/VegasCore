module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketDirectedRepairHistory
public import Vegas.Game.OnePacketDirectedRepairPrefixSuccess
public import Vegas.Game.OnePacketAcceptedPrefix
public import Vegas.Game.OnePacketBindingRepairCounterparts
public import Vegas.Game.SourceDebtObservation

@[expose] public section

/-! # Actual binding repair from an intended witness -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

/-- A debt-free intended witness discharges every original-prefix guard of the
actual whole-history repair. No repaired-history constructor is assumed. -/
theorem repair_binding_history_of_intended_witness
    (wellFormed : setup.WellFormed) (covered : bounds.CoversOutputValues)
    {focal owner : Player} (other : owner ≠ focal)
    {site : (onePacketInformation setup timeouts leaks bounds horizon scheduler).InformationSite
      focal}
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView}
    (decision : site.1 = some (past, view))
    (forced : forcedAgent (timeouts := timeouts) (bounds.onePacketMenu timeouts leaks) (initialLaw
      setup)
      horizon scheduler focal site.1)
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? focal = some event)
    (history witness :
      (onePacketInformation setup timeouts leaks bounds horizon scheduler).InformationHistory
        focal (some (past, view)))
    {current witnessControl : (application setup timeouts leaks).Control}
    (historyState : history.1.state = some current)
    (witnessState : witness.1.state = some witnessControl)
    {target : ProtocolState setup.program}
    (witnessDecoded : decodedPoint setup witnessControl.execution.application.config = some target)
    (free : ∀ player, ¬ ProtocolState.OwesFailure player setup.program target) :
    Nonempty (BindingRepairHistory (timeouts := timeouts) owner history.1.trace current) := by
  classical
  obtain ⟨found, foundState, currentView⟩ := state_of_decision (timeouts := timeouts)
    (site := site) ⟨history.1, history.2.trans decision.symm⟩ decision
  rw [historyState, Option.some.injEq] at foundState
  subst found
  obtain ⟨found, foundState, witnessView⟩ := state_of_decision (timeouts := timeouts)
    (site := site) ⟨witness.1, witness.2.trans decision.symm⟩ decision
  rw [witnessState, Option.some.injEq] at foundState
  subst found
  have record := publicRecord_of_forced_information (timeouts := timeouts) decision forced
    ⟨history.1, history.2.trans decision.symm⟩ historyState
  obtain ⟨⟨state, trace⟩, seen⟩ := history
  change state = some current at historyState
  subst historyState
  obtain ⟨⟨state, witnessTrace⟩, witnessSeen⟩ := witness
  change state = some witnessControl at witnessState
  subst witnessState
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (timeouts := timeouts) (failureProfile
    setup.program)
    (bounds.onePacketMenu timeouts leaks) horizon scheduler trace current rfl
  have decoded := decodedPoint_eq residual
  have sameSource := (sourceViewOf_eq_decodedPoint (timeouts := timeouts) focal trace).symm.trans
    ((congrArg (sourceViewOf setup timeouts leaks focal) (currentView.trans witnessView.symm)).trans
      (sourceViewOf_eq_decodedPoint (timeouts := timeouts) focal witnessTrace))
  rw [decoded, witnessDecoded] at sameSource
  have sameView := Option.some.inj sameSource
  have witnessFree : ∀ point, decodedPoint setup witnessControl.execution.application.config =
      some point → ∀ player, ¬ ProtocolState.OwesFailure player setup.program point := by
    intro point read player
    rw [witnessDecoded, Option.some.injEq] at read
    subst read
    exact free player
  obtain ⟨second, secondReplay⟩ := intendedHistory?_isSome_of_debtFree (timeouts := timeouts)
    wellFormed witnessTrace
    witnessControl rfl witnessFree
  have secondState : second.state = some target :=
    (intendedHistory?_state (timeouts := timeouts) witnessTrace secondReplay).trans witnessDecoded
  have witnessClear : witnessControl.execution.application.config.defaulted = ∅ :=
    defaulted_eq_empty_of_decodedIntended witnessDecoded
      (intended_of_history wellFormed second.trace target secondState)
  have sameDefaults : current.execution.application.config.defaulted =
      witnessControl.execution.application.config.defaulted :=
    congrArg (fun observed : (application setup timeouts leaks).PlayerView =>
      observed.application.publicView.observation.defaulted)
        (currentView.trans witnessView.symm)
  have endpointClear : current.execution.application.config.defaulted = ∅ :=
    sameDefaults.trans witnessClear
  have currentTurn : current.execution.application.publicView.ownTurn? focal = some event := by
    rw [← currentView] at turn
    exact turn
  have readyOwn := readyOwn_of_ownTurn current.execution.application currentTurn
  have notOwed : ∀ point, nativeDecodedState setup timeouts leaks (some current) = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point := by
    intro point read owes
    change decodedPoint setup current.execution.application.config = some point at read
    rw [decoded, Option.some.injEq] at read
    subst read
    exact free focal ((owesFailure_iff_of_infoOf (timeouts := timeouts)
      (menu := bounds.onePacketMenu timeouts leaks) (horizon := horizon)
      (scheduler := scheduler) ⟨⟨some current, trace⟩, seen⟩
      ⟨⟨some witnessControl, witnessTrace⟩, witnessSeen⟩ decoded witnessDecoded).mp owes)
  apply repair_binding_history (timeouts := timeouts) covered focal owner other forced decision
    ⟨⟨some current, trace⟩, seen.trans decision.symm⟩ current rfl endpointClear
  · intro before prior isPrefix event actor payload binding checks outputEq codeEq node ready
    exact binding_success_of_tracePrefix wellFormed secondState focal sameView trace decoded
      (decodedPoint_staticAt witnessDecoded) readyOwn prior isPrefix ready binding checks
      outputEq codeEq node
  · intro before prior isPrefix event actor payload outputEq completed
    exact completedBinding_accepted_at_tracePrefix (timeouts := timeouts) prior isPrefix record
      notOwed event actor
      payload outputEq completed

/-- Actual finite private-binding repairs give a regular counterpart throughout
a forced decision fiber, preserving the complete operational record. -/
theorem counterpart_of_intended_witness_repairs
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    {assessment : setup.intendedModel.BehavioralAssessment} (mixed : assessment.IsFullyMixed)
    {focal : Player}
    {site : (onePacketInformation setup timeouts leaks bounds horizon scheduler).InformationSite
      focal}
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView}
    (decision : site.1 = some (past, view))
    (forced : forcedAgent (timeouts := timeouts) (bounds.onePacketMenu timeouts leaks) (initialLaw
      setup)
      horizon scheduler focal site.1)
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? focal = some event)
    (history witness :
      (onePacketInformation setup timeouts leaks bounds horizon scheduler).InformationHistory
        focal (some (past, view)))
    {current witnessControl : (application setup timeouts leaks).Control}
    (historyState : history.1.state = some current)
    (witnessState : witness.1.state = some witnessControl)
    {target : ProtocolState setup.program}
    (witnessDecoded : decodedPoint setup witnessControl.execution.application.config = some target)
    (free : ∀ player, ¬ ProtocolState.OwesFailure player setup.program target)
    (covered : BindingFieldsCovered bounds) :
    ∃ counterpart : (onePacketInformation setup timeouts leaks bounds horizon
      scheduler).InformationHistory
        focal (some (past, view)),
      RegularTrace setup timeouts leaks bounds horizon scheduler assessment focal
        counterpart.1.trace ∧
      operationalRecord setup timeouts leaks bounds horizon scheduler counterpart.1.trace =
        operationalRecord setup timeouts leaks bounds horizon scheduler history.1.trace := by
  apply counterpart_of_owner_repairs (timeouts := timeouts) wellFormed mixed decision forced turn
    history witness
    historyState witnessState witnessDecoded free covered
  intro owner other control trace seen
  obtain ⟨image⟩ := repair_binding_history_of_intended_witness (timeouts := timeouts) wellFormed
    covers other
    decision forced turn ⟨⟨some control, trace⟩, seen⟩ witness rfl witnessState witnessDecoded free
  exact ⟨⟨control.remaining, control.actor, image.execution⟩, image.trace, image.memory,
    rfl, rfl, image.frame, image.records, image.recorded⟩

end Vegas
