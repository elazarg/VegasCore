/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketMainActivation
import Vegas.Game.OnePacketForeignActivation
import Vegas.Game.OnePacketMainResponseSafety
import Vegas.Game.OnePacketCountedService
import Vegas.Game.OnePacketForeignSubmission
import Vegas.Game.OnePacketCompletionOrigin
import Vegas.Game.OnePacketFilteredPrefix

/-! # First foreign failures under native counted pointwise service

Every service input concerns an actual clear counted prefix. Failing exits
identify a genuine future non-main foreign response without a recovery-wide
or unrestricted native raw service contract.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}

/-- A first foreign public failure before focal debt remembers an actual
non-main foreign first response after the comparison's focal source turn.
Both expiry and consumed opening traffic are attributed from actual execution. -/
theorem foreign_nonmain_prefix_of_firstFailure
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal owner : Player)
    (different : owner ≠ focal)
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup leaks).Control,
      (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      OpportunityAt (runtime setup) leaks control.execution delay)
    (inclusion : ∀ control : (application setup leaks).Control,
      (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      ProtectedInclusionAt (runtime setup) leaks control.execution bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (start : (application setup leaks).Control)
    (startTrace : (onePacketProtocol setup leaks bounds horizon
      scheduler).Trace (some start))
    (remaining : Nat) (execution : (application setup leaks).Execution)
    (trace : (onePacketProtocol setup leaks bounds horizon
      scheduler).Trace
        (some ⟨remaining + 1, none, execution⟩))
    (startPrefix : TracePrefix startTrace trace)
    (current event : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup leaks bounds horizon
      scheduler source focal trace)
    (notOwed : ∀ point, decodedPoint setup execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (owned : (graph setup).actor? event = some owner)
    (command : (application setup leaks).Command) (next : (application setup leaks).Execution)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    (target : (onePacketProtocol setup leaks bounds horizon
      scheduler).Trace
        (some ⟨remaining, command.actor? (application setup leaks), next⟩))
    (tracePrefix : TracePrefix trace target) (failed : next.application.PublicFailure event) :
    ∃ (before : (application setup leaks).Control)
      (prior : (onePacketProtocol setup leaks bounds horizon
        scheduler).Trace (some before))
      (response : (application setup leaks).Action)
      (joint : Player → Option (application setup leaks).Action)
      (legal : (onePacketProtocol setup leaks bounds horizon
        scheduler).Legal
          (some before) joint)
      (realized : some ⟨before.remaining, none,
        before.execution.respond (application setup leaks) owner response⟩ ∈
        ((onePacketProtocol setup leaks bounds horizon
          scheduler).step
            (some before) ⟨joint, legal⟩).support),
      TracePrefix startTrace prior ∧ TracePrefix (prior.extend joint legal realized) target ∧
      before.actor = some owner ∧ joint owner = some response ∧
      pendingEvent setup leaks owner (some (before.execution.recall owner,
        before.execution.observe (application setup leaks) owner)) = some event ∧
      (∀ previous ∈ before.execution.recall owner,
        ¬ ActivatedAt setup leaks owner event previous) ∧
      responseChoice setup leaks bounds (initialLaw setup) horizon
        scheduler owner
        (some (before.execution.recall owner,
          before.execution.observe (application setup leaks) owner)) response ∉
        (honestChoice setup leaks bounds (initialLaw setup) horizon
          scheduler source owner
          (some (before.execution.recall owner,
            before.execution.observe (application setup leaks) owner))).support := by
  have origin := firstPublicFailure_pending_or_due execution next command reached clear event owner
    owned failed
  have extracted : ∃ (before : (application setup leaks).Control)
      (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some before))
      (response : (application setup leaks).Action)
      (joint : Player → Option (application setup leaks).Action)
      (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal
        (some before) joint)
      (realized : some ⟨before.remaining, none,
        before.execution.respond (application setup leaks) owner response⟩ ∈
        ((onePacketProtocol setup leaks bounds horizon scheduler).step
          (some before) ⟨joint, legal⟩).support),
      TracePrefix startTrace prior ∧ TracePrefix (prior.extend joint legal realized) trace ∧
      before.actor = some owner ∧ joint owner = some response ∧
      pendingEvent setup leaks owner (some (before.execution.recall owner,
        before.execution.observe (application setup leaks) owner)) = some event ∧
      ∀ previous ∈ before.execution.recall owner,
        ¬ ActivatedAt setup leaks owner event previous := by
    rcases origin.2 with ⟨message, member, sender, named⟩ | ⟨_, entered, activated, due⟩
    · have recorded := eventRecorded_of_pending trace owner event message member sender named
      exact foreign_firstActivation_prefix_of_recorded wellFormed source focal owner different
        start ⟨remaining + 1, none, execution⟩ startTrace trace startPrefix current event turn clear
        regular notOwed owned origin.1 recorded
    · exact foreign_firstActivation_prefix_of_due wellFormed source focal owner different timely
        start ⟨remaining + 1, none, execution⟩ startTrace trace
        (opportunity ⟨remaining + 1, none, execution⟩ trace clear) startPrefix current event turn
        clear regular notOwed rfl owned origin.1 entered activated due
  obtain ⟨before, prior, response, joint, legal, realized, future, afterPrefix, acting, chosen,
    pending, never⟩ := extracted
  have priorPrefix : TracePrefix prior trace :=
    (TracePrefix.extend .refl joint legal realized).trans afterPrefix
  obtain ⟨earlierClear, earlierRegular, earlierNotOwed⟩ := clear_regular_notOwes_of_tracePrefix
    wellFormed source focal owner different prior trace priorPrefix clear regular notOwed
  have targetPrefix := afterPrefix.trans tracePrefix
  have localLegal := legal.2 owner
  rw [chosen] at localLegal
  have offered : response ∈ bounds.onePacketActions (runtime setup) leaks owner
      (before.execution.recall owner) (before.execution.observe (application setup leaks) owner) :=
    localLegal.2
  have selected : (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler
      owner (some (before.execution.recall owner,
        before.execution.observe (application setup leaks) owner)) response).1 = some response := by
    simp only [responseChoice, dite_eq_left offered]
  have notMain : responseChoice setup leaks bounds (initialLaw setup) horizon scheduler owner
      (some (before.execution.recall owner,
        before.execution.observe (application setup leaks) owner)) response ∉
      (honestChoice setup leaks bounds (initialLaw setup) horizon scheduler source owner
        (some (before.execution.recall owner,
          before.execution.observe (application setup leaks) owner))).support := by
    rcases before with ⟨responsesLeft, actor, earlierExecution⟩
    dsimp only at acting
    subst actor
    have fits := firstActivation_inclusionFits_of_counted_opportunity setup leaks bounds horizon
      scheduler delay bound opportunity timely prior rfl earlierClear event
      (pendingEvent_spec pending).1 never
    have settles := settlesFreshCalls_counted_clear_environment setup leaks bounds horizon scheduler
      bound inclusion owner event owned remaining execution trace clear command next reached
    exact firstResponse_not_main_of_publicFailure_of_settles bounds wellFormed covers capacity
      source
      focal horizon scheduler bound prior earlierClear earlierRegular earlierNotOwed event pending
      fits _ response selected (prior.extend joint legal realized) next settles _ rfl target
      targetPrefix failed
  exact ⟨before, prior, response, joint, legal, realized, future, targetPrefix, acting, chosen,
    pending, never, notMain⟩

/-- A first foreign failure violates the future first-activation main condition. -/
theorem firstForeignFailure_not_mainActivationTraceAfter
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal owner : Player)
    (different : owner ≠ focal)
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup leaks).Control,
      (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      OpportunityAt (runtime setup) leaks control.execution delay)
    (inclusion : ∀ control : (application setup leaks).Control,
      (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      ProtectedInclusionAt (runtime setup) leaks control.execution bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (start : (application setup leaks).Control)
    (startTrace : (onePacketProtocol setup leaks bounds horizon
      scheduler).Trace (some start))
    (remaining : Nat) (execution : (application setup leaks).Execution)
    (trace : (onePacketProtocol setup leaks bounds horizon
      scheduler).Trace
        (some ⟨remaining + 1, none, execution⟩))
    (startPrefix : TracePrefix startTrace trace)
    (current event : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup leaks bounds horizon
      scheduler source focal trace)
    (notOwed : ∀ point, decodedPoint setup execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (owned : (graph setup).actor? event = some owner)
    (command : (application setup leaks).Command) (next : (application setup leaks).Execution)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    (target : (onePacketProtocol setup leaks bounds horizon
      scheduler).Trace
        (some ⟨remaining, command.actor? (application setup leaks), next⟩))
    (tracePrefix : TracePrefix trace target) (failed : next.application.PublicFailure event) :
    ¬ MainActivationTraceAfter setup leaks bounds horizon
      scheduler source focal
      startTrace.length target := by
  intro main
  obtain ⟨before, prior, response, joint, legal, realized, future, afterPrefix, acting, chosen,
    pending, never, outside⟩ :=
    foreign_nonmain_prefix_of_firstFailure wellFormed covers
      capacity source focal owner different opportunity inclusion timely start
      startTrace remaining execution trace startPrefix current event turn clear regular notOwed
      owned
      command next reached target tracePrefix failed
  have supported := mainActivationStep_of_tracePrefix source focal startTrace.length prior joint
    legal realized afterPrefix main future.length_le
  apply outside
  have first : FirstActivation setup leaks owner (some (before.execution.recall owner,
      before.execution.observe (application setup leaks) owner)) :=
    ⟨before.execution.recall owner, before.execution.observe (application setup leaks) owner, event,
      rfl, pending, never⟩
  have selected := supported owner acting different first
  simpa only [chosen, Option.getD_some] using selected


end Vegas
