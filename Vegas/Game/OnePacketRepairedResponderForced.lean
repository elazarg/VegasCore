/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketBindingRepairWitness
import Vegas.Game.OnePacketRecallPrefix
import Vegas.Game.SourceDebtObservation

/-! # Forced responder inputs from responder-preserving repairs

The original responder's recorded decision persists in its final private
recall. A repair that retains this recall carries that same decision into an
actual history whose responder splice forces every prefix input.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

variable {Public : Type*} {signal : State L setup.context → Public}

/-- Every actual foreign responder input along a forced focal history is
forced once the concrete single-owner repair constructor is available.
Responder-preserving repair may retain that responder's own failed bindings. -/
theorem forcedAgent_of_responder_preserving_repair (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal) (covered : BindingFieldsCovered bounds)
    {focal responder : Player} (different : responder ≠ focal)
    {site : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationSite
      focal}
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView}
    (decision : site.1 = some (past, view))
    (forced : forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks) (initialLaw
      setup)
      horizon scheduler focal site.1)
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? focal = some event)
    (history witness :
      (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationHistory
        focal (some (past, view)))
    {original witnessControl : (application setup runtime leaks).Control}
    (historyState : history.1.state = some original)
    (witnessState : witness.1.state = some witnessControl)
    {target : ProtocolState setup.program}
    (witnessDecoded : decodedPoint setup witnessControl.execution.application.config = some target)
    (free : ∀ player, ¬ ProtocolState.OwesFailure player setup.program target)
    (repair : ∀ owner, owner ≠ focal → ∀ current
      (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some
        current)),
      (onePacketInformation setup runtime leaks bounds horizon scheduler).infoOf focal trace =
        some (past, view) →
      ∃ repaired : (application setup runtime leaks).Control,
        ∃ image : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some
          repaired),
        ∃ memory : BindingMemory runtime leaks,
          repaired.remaining = current.remaining ∧ repaired.actor = current.actor ∧
          DirectedBindingFrame (runtime := runtime) memory owner current.execution
            repaired.execution ∧
          operationalRecord setup runtime leaks bounds horizon scheduler trace =
            operationalRecord setup runtime leaks bounds horizon scheduler image ∧
          memory.RecordsSubmittedBindings runtime leaks owner
            current.execution repaired.execution)
    {control : (application setup runtime leaks).Control}
    (prior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control))
    (joint : Player → Option (application setup runtime leaks).Action)
    (legal : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Legal (some control)
      joint)
    {after : (application setup runtime leaks).ProtocolState}
    (realized : after ∈ ((onePacketProtocol setup runtime leaks bounds horizon scheduler).step
      (some control) ⟨joint, legal⟩).support)
    (isPrefix : TracePrefix (prior.extend joint legal realized) history.1.trace)
    (acting : control.actor = some responder) :
    forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks) (initialLaw setup)
      horizon scheduler
      responder ((application setup runtime leaks).observe responder (some control)) := by
  classical
  obtain ⟨repaired, image, imageSeen, _, sameInput, _, point, decoded, succeed⟩ :=
    exists_bindingRepairs_preserving_responder (runtime := runtime) (responder := responder)
      wellFormed decision forced
      history witness historyState witnessState witnessDecoded free repair
  obtain ⟨⟨state, trace⟩, seen⟩ := history
  change state = some original at historyState
  subst historyState
  have sameOwnPlay :
      (onePacketInformation setup runtime leaks bounds horizon scheduler).ownPlay responder trace =
        (onePacketInformation setup runtime leaks bounds horizon scheduler).ownPlay responder
          image := by
    rw [onePacket_ownPlay_recall, onePacket_ownPlay_recall]
    change (application setup runtime leaks).recallOwnPlay (original.execution.recall responder) =
      (application setup runtime leaks).recallOwnPlay (repaired.execution.recall responder)
    exact congrArg _ (congrArg Prod.fst sameInput)
  have active : (onePacketProtocol setup runtime leaks bounds horizon scheduler).active (some
    control)
      responder := acting
  obtain ⟨response, selected⟩ := LegalOption.exists_eq_some_of_active (joint responder)
    ((onePacketProtocol setup runtime leaks bounds horizon scheduler).legalOption_of_legal legal
      responder)
    active
  let recorded :=
    ((onePacketInformation setup runtime leaks bounds horizon scheduler).infoOf responder prior,
      response)
  have head : recorded ∈ (onePacketInformation setup runtime leaks bounds horizon scheduler).ownPlay
      responder (prior.extend joint legal realized) := by
    rw [InfoSignals.ownPlay_extend, selected]
    exact List.mem_cons_self
  have originalMember : recorded ∈
      (onePacketInformation setup runtime leaks bounds horizon scheduler).ownPlay responder trace
        := by
    have retain : ∀ {state}
        (last : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace state),
        TracePrefix (prior.extend joint legal realized) last → recorded ∈
          (onePacketInformation setup runtime leaks bounds horizon scheduler).ownPlay responder
            last := by
      intro state last path
      induction path with
      | refl => exact head
      | extend earlier choices permitted reached ih =>
          rw [InfoSignals.ownPlay_extend]
          cases chosen : choices responder with
          | none => simpa only [chosen] using ih
          | some action => simpa only [chosen] using List.mem_cons_of_mem _ ih
    exact retain trace isPrefix
  have imageMember : recorded ∈
      (onePacketInformation setup runtime leaks bounds horizon scheduler).ownPlay responder image
        := by
    rw [← sameOwnPlay]
    exact originalMember
  obtain ⟨found, foundState, imageView⟩ := state_of_decision (runtime := runtime) (site := site)
    ⟨⟨some repaired, image⟩, imageSeen.trans decision.symm⟩ decision
  rw [Option.some.injEq] at foundState
  subst found
  obtain ⟨found, foundState, witnessView⟩ := state_of_decision (runtime := runtime) (site := site)
    ⟨witness.1, witness.2.trans decision.symm⟩ decision
  rw [witnessState, Option.some.injEq] at foundState
  subst found
  obtain ⟨⟨witnessStateRaw, witnessTrace⟩, witnessSeen⟩ := witness
  change witnessStateRaw = some witnessControl at witnessState
  subst witnessState
  have sameSource := (sourceViewOf_eq_decodedPoint (runtime := runtime) focal image).symm.trans
    ((congrArg (sourceViewOf setup runtime leaks focal) (imageView.trans witnessView.symm)).trans
      (sourceViewOf_eq_decodedPoint (runtime := runtime) focal witnessTrace))
  rw [decoded, witnessDecoded] at sameSource
  have sameView := Option.some.inj sameSource
  have freeWitness : ∀ point,
      decodedPoint setup witnessControl.execution.application.config = some point →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program point := by
    intro point decoded player
    rw [witnessDecoded, Option.some.injEq] at decoded
    subst decoded
    exact free player
  obtain ⟨second, replay⟩ := intendedHistory?_isSome_of_debtFree (runtime := runtime) wellFormed
    witnessTrace
    witnessControl rfl freeWitness
  have secondState : second.state = some target :=
    (intendedHistory?_state (runtime := runtime) witnessTrace replay).trans witnessDecoded
  have repairedTurn : repaired.execution.application.publicView.ownTurn? focal = some event := by
    rw [← imageView] at turn
    exact turn
  have readyOwn := readyOwn_of_ownTurn repaired.execution.application repairedTurn
  have forcedPrefixes : ∀ (current : (application setup runtime leaks).Control)
      (priorTrace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some
        current)),
      TracePrefix priorTrace image → forcedAgent (runtime := runtime) (bounds.onePacketMenu
        runtime leaks)
        (initialLaw setup) horizon scheduler responder
          ((application setup runtime leaks).observe responder (some current)) := by
    intro current priorTrace prefixOf
    exact forcedAgent_of_splice (runtime := runtime) wellFormed independent observable covered
      image decoded
      secondState sameView
      (decodedPoint_staticAt witnessDecoded) readyOwn succeed priorTrace prefixOf different
  have forcedRecord := forcedAgent_of_recorded_decision (runtime := runtime) image responder
    forcedPrefixes imageMember
  change forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks) (initialLaw setup)
    horizon
    scheduler responder
      ((onePacketInformation setup runtime leaks bounds horizon scheduler).infoOf
        responder prior) at forcedRecord
  rw [onePacket_infoOf] at forcedRecord
  exact forcedRecord


/-- Actual witness-guided binding repairs make every foreign responder's
recorded decision input forced, including decisions after its own failed binding. -/
theorem forcedAgent_of_intended_witness_repairs (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal) (covers : bounds.CoversOutputValues)
    (covered : BindingFieldsCovered bounds)
    {focal responder : Player} (different : responder ≠ focal)
    {site : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationSite
      focal}
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView}
    (decision : site.1 = some (past, view))
    (forced : forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks) (initialLaw
      setup)
      horizon scheduler focal site.1)
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? focal = some event)
    (history witness :
      (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationHistory
        focal (some (past, view)))
    {original witnessControl : (application setup runtime leaks).Control}
    (historyState : history.1.state = some original)
    (witnessState : witness.1.state = some witnessControl)
    {target : ProtocolState setup.program}
    (witnessDecoded : decodedPoint setup witnessControl.execution.application.config = some target)
    (free : ∀ player, ¬ ProtocolState.OwesFailure player setup.program target)
    {control : (application setup runtime leaks).Control}
    (prior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control))
    (joint : Player → Option (application setup runtime leaks).Action)
    (legal : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Legal (some control)
      joint)
    {after : (application setup runtime leaks).ProtocolState}
    (realized : after ∈ ((onePacketProtocol setup runtime leaks bounds horizon scheduler).step
      (some control) ⟨joint, legal⟩).support)
    (isPrefix : TracePrefix (prior.extend joint legal realized) history.1.trace)
    (acting : control.actor = some responder) :
    forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks) (initialLaw setup)
      horizon scheduler
      responder ((application setup runtime leaks).observe responder (some control)) := by
  refine forcedAgent_of_responder_preserving_repair (runtime := runtime) wellFormed independent
    observable covered
    different
    decision forced turn history witness historyState witnessState witnessDecoded free ?_
    prior joint legal realized isPrefix acting
  intro owner other current sourceTrace seen
  obtain ⟨image⟩ := repair_binding_history_of_intended_witness (runtime := runtime) wellFormed
    covers other
    decision forced turn ⟨⟨some current, sourceTrace⟩, seen⟩ witness rfl witnessState
      witnessDecoded free
  exact ⟨⟨current.remaining, current.actor, image.execution⟩, image.trace, image.memory,
    rfl, rfl, image.frame, image.records, image.recorded⟩

end Vegas
