/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketBindingRepairIteration
import Vegas.Game.OnePacketDirectedRepairGuard
import Vegas.Game.OnePacketOwnerSettled

/-! # Counterparts from finite actual hidden-binding repairs

The single-owner implementation constructor remains explicit. Finite repair
of all foreign owners supplies a regular counterpart; leaving one responder
unrepaired preserves its full input while making its forced splice admissible.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- An actual single-owner repair constructor at a forced focal information
set yields a regular counterpart after finitely many foreign-owner repairs.
The constructor remains the explicit implementation dependency. -/
theorem counterpart_of_owner_repairs (wellFormed : setup.WellFormed)
    {assessment : setup.intendedModel.BehavioralAssessment} (mixed : assessment.IsFullyMixed)
    {focal : Player}
    {site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite focal}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    (decision : site.1 = some (past, view))
    (forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup)
      horizon scheduler focal site.1)
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? focal = some event)
    (history witness :
      (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory
        focal (some (past, view)))
    {original witnessControl : (application setup leaks).Control}
    (historyState : history.1.state = some original)
    (witnessState : witness.1.state = some witnessControl)
    {target : ProtocolState setup.program}
    (witnessDecoded : decodedPoint setup witnessControl.execution.application.config = some target)
    (free : ∀ player, ¬ ProtocolState.OwesFailure player setup.program target)
    (covered : BindingFieldsCovered bounds)
    (repair : ∀ owner, owner ≠ focal → ∀ current
      (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some current)),
      (onePacketInformation setup leaks bounds horizon scheduler).infoOf focal trace =
        some (past, view) →
      ∃ repaired : (application setup leaks).Control,
        ∃ image : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some repaired),
        ∃ memory : BindingMemory (runtime setup) leaks,
          repaired.remaining = current.remaining ∧ repaired.actor = current.actor ∧
          DirectedBindingFrame memory owner current.execution repaired.execution ∧
          operationalRecord setup leaks bounds horizon scheduler trace =
            operationalRecord setup leaks bounds horizon scheduler image ∧
          memory.RecordsSubmittedBindings (runtime setup) leaks owner
            current.execution repaired.execution) :
    ∃ counterpart : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory
        focal (some (past, view)),
      RegularTrace setup leaks bounds horizon scheduler assessment focal counterpart.1.trace ∧
      operationalRecord setup leaks bounds horizon scheduler counterpart.1.trace =
        operationalRecord setup leaks bounds horizon scheduler history.1.trace := by
  classical
  obtain ⟨⟨state, trace⟩, seen⟩ := history
  change state = some original at historyState
  subst historyState
  have record : ∀ current
      (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some current)),
      (onePacketInformation setup leaks bounds horizon scheduler).infoOf focal trace =
        some (past, view) → PublicRecord setup focal current := by
    intro current trace seen
    exact publicRecord_of_forced_information decision forced
      ⟨⟨some current, trace⟩, seen.trans decision.symm⟩ rfl
  obtain ⟨repaired, image, imageSeen, _, _, sameRecord, _, _, successful⟩ :=
    exists_bindingRepairs_for_owners focal (some (past, view)) original trace seen record
      (Finset.univ.erase focal) (by simp)
      (fun owner member => repair owner (by simpa using member))
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
    (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler image repaired rfl
  obtain ⟨counterpart, regular, counterpartRecord⟩ :=
    counterpart_of_successful_foreign_bindings wellFormed mixed turn
      ⟨⟨some repaired, image⟩, imageSeen⟩ witness rfl witnessState (decodedPoint_eq residual)
      witnessDecoded free
      (fun event owner payload layoutEq foreign completed =>
        not_storeEventFailed_of_outputSucceeded
          (successful owner (by simpa using foreign) event payload layoutEq completed)) covered
  exact ⟨counterpart, regular, counterpartRecord.trans sameRecord.symm⟩


/-- Repairing all owners except the focal player and one responder retains the
responder's full final input and gives exactly the compatibility needed for
its forced splice. The responder's own failed bindings may remain unchanged. -/
theorem exists_bindingRepairs_preserving_responder [DecidableEq (CellTy Player L)]
    (wellFormed : setup.WellFormed)
    {focal responder : Player}
    {site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite focal}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    (decision : site.1 = some (past, view))
    (forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup)
      horizon scheduler focal site.1)
    (history witness :
      (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory
        focal (some (past, view)))
    {original witnessControl : (application setup leaks).Control}
    (historyState : history.1.state = some original)
    (witnessState : witness.1.state = some witnessControl)
    {target : ProtocolState setup.program}
    (witnessDecoded : decodedPoint setup witnessControl.execution.application.config = some target)
    (free : ∀ player, ¬ ProtocolState.OwesFailure player setup.program target)
    (repair : ∀ owner, owner ≠ focal → ∀ current
      (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some current)),
      (onePacketInformation setup leaks bounds horizon scheduler).infoOf focal trace =
        some (past, view) →
      ∃ repaired : (application setup leaks).Control,
        ∃ image : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some repaired),
        ∃ memory : BindingMemory (runtime setup) leaks,
          repaired.remaining = current.remaining ∧ repaired.actor = current.actor ∧
          DirectedBindingFrame memory owner current.execution repaired.execution ∧
          operationalRecord setup leaks bounds horizon scheduler trace =
            operationalRecord setup leaks bounds horizon scheduler image ∧
          memory.RecordsSubmittedBindings (runtime setup) leaks owner
            current.execution repaired.execution) :
    ∃ repaired : (application setup leaks).Control,
      ∃ image : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some repaired),
        (onePacketInformation setup leaks bounds horizon scheduler).infoOf focal image =
          some (past, view) ∧
        operationalRecord setup leaks bounds horizon scheduler history.1.trace =
          operationalRecord setup leaks bounds horizon scheduler image ∧
        (original.execution.recall responder,
          original.execution.observe (application setup leaks) responder) =
        (repaired.execution.recall responder,
          repaired.execution.observe (application setup leaks) responder) ∧
        original.execution.application.config.store.BindingRefines
          repaired.execution.application.config.store ∧
        ∃ point : ProtocolState setup.program,
          decodedPoint setup repaired.execution.application.config = some point ∧
          CommitmentCellsSucceed setup point
            (ProtocolState.splicePoint setup.program responder point target) := by
  have intended : ProtocolState.Intended setup.program target := by
    obtain ⟨⟨state, trace⟩, seen⟩ := witness
    change state = some witnessControl at witnessState
    subst witnessState
    have freeWitness : ∀ point,
        decodedPoint setup witnessControl.execution.application.config = some point →
        ∀ player, ¬ ProtocolState.OwesFailure player setup.program point := by
      intro point decoded player
      rw [witnessDecoded, Option.some.injEq] at decoded
      subst decoded
      exact free player
    obtain ⟨source, replay⟩ := intendedHistory?_isSome_of_debtFree wellFormed trace
      witnessControl rfl freeWitness
    exact intended_of_history wellFormed source.trace target
      ((intendedHistory?_state trace replay).trans witnessDecoded)
  have witnessNative : nativeDecodedState setup leaks witness.1.state = some target := by
    rw [witnessState]
    exact witnessDecoded
  obtain ⟨⟨state, trace⟩, seen⟩ := history
  change state = some original at historyState
  subst historyState
  have record : ∀ current
      (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some current)),
      (onePacketInformation setup leaks bounds horizon scheduler).infoOf focal trace =
        some (past, view) → PublicRecord setup focal current := by
    intro current trace seen
    exact publicRecord_of_forced_information decision forced
      ⟨⟨some current, trace⟩, seen.trans decision.symm⟩ rfl
  let owners := Finset.univ.filter (fun owner => owner ≠ focal ∧ owner ≠ responder)
  obtain ⟨repaired, image, imageSeen, _, _, sameRecord, outside, preserved, successful⟩ :=
    exists_bindingRepairs_for_owners focal (some (past, view)) original trace seen record
      owners (by simp [owners])
      (fun owner member => repair owner (Finset.mem_filter.mp member).2.1)
  have ownDebtFree : ∀ point, nativeDecodedState setup leaks (some repaired) = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point := by
    intro point decoded owes
    exact free focal ((owesFailure_iff_of_infoOf
      ⟨⟨some repaired, image⟩, imageSeen⟩ witness decoded witnessNative).mp owes)
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
    (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler image repaired rfl
  refine ⟨repaired, image, imageSeen, sameRecord, outside responder (by simp [owners]),
    preserved, _, decodedPoint_eq residual, ?_⟩
  apply commitmentCellsSucceed_splicePoint_of_foreign_bindings
    (decodedPoint_eq residual) intended
  apply foreignBinding_reads_not_failure wellFormed image
  intro event owner payload layoutEq foreign completed
  by_cases own : owner = focal
  · subst owner
    rintro ⟨value, stored, failed⟩
    exact noFailure_of_debtFree image ownDebtFree (.inr event)
      (privateTo_of_binding layoutEq) value stored failed
  · exact not_storeEventFailed_of_outputSucceeded
      (successful owner (by simp [owners, own, foreign]) event payload layoutEq completed)

end Vegas
