/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryForeignActivation
import Vegas.Game.OnePacketForeignSubmission
import Vegas.Game.OnePacketCompletionOrigin
import Vegas.Game.OnePacketFilteredPrefix
import Vegas.Game.RecoveryMainResponseSafety

/-! # First foreign failures identify a future non-main response -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

/-- A foreign response at a first activation uses source-main support. No
condition is imposed on focal responses, scheduler moves, or later activations. -/
def MainActivationStep (source : setup.intendedModel.BehavioralAssessment) (focal : Player) :
    (application setup leaks).ProtocolState →
      (Player → Option (application setup leaks).Action) → Prop
  | none, _ => True
  | some before, joint => ∀ owner, before.actor = some owner → owner ≠ focal →
      FirstActivation setup leaks owner (some (before.execution.recall owner,
        before.execution.observe (application setup leaks) owner)) →
      responseChoice setup leaks bounds (initialLaw setup) horizon scheduler owner
        (some (before.execution.recall owner,
          before.execution.observe (application setup leaks) owner))
        ((joint owner).getD ⟨none⟩) ∈
        (honestChoice setup leaks bounds (initialLaw setup) horizon scheduler source owner
          (some (before.execution.recall owner,
            before.execution.observe (application setup leaks) owner))).support

/-- Every foreign first activation at or beyond a specified trace length uses
source-main support. Earlier play is retained without imposing this condition. -/
def MainActivationTraceAfter (source : setup.intendedModel.BehavioralAssessment) (focal : Player)
    (cutoff : Nat) :
    ∀ {state}, (onePacketProtocol setup leaks bounds horizon scheduler).Trace state → Prop
  | _, .start => True
  | _, .extend (source := before) prior joint _ _ =>
      MainActivationTraceAfter source focal cutoff prior ∧
        (cutoff ≤ prior.length → MainActivationStep setup leaks bounds horizon scheduler source
          focal before joint)

variable {setup leaks bounds horizon scheduler}

/-- No response in a trace precedes a boundary at least its own length. -/
theorem mainActivationTraceAfter_of_length_le
    (source : setup.intendedModel.BehavioralAssessment) (focal : Player)
    {state : (onePacketProtocol setup leaks bounds horizon scheduler).State}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state)
    (cutoff : Nat) (length : trace.length ≤ cutoff) :
    MainActivationTraceAfter setup leaks bounds horizon scheduler source focal cutoff trace := by
  induction trace with
  | start => trivial
  | extend prior joint legal realized ih =>
      refine ⟨ih (Nat.le_trans (Nat.le_succ prior.length) length), ?_⟩
      intro later
      simp only [Trace.length] at length
      omega

/-- The future-main condition at an actual endpoint holds at every prefix. -/
theorem mainActivationTraceAfter_of_tracePrefix
    (source : setup.intendedModel.BehavioralAssessment) (focal : Player) (cutoff : Nat)
    {first final : (onePacketProtocol setup leaks bounds horizon scheduler).State}
    {prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace first}
    {top : (onePacketProtocol setup leaks bounds horizon scheduler).Trace final}
    (isPrefix : TracePrefix prior top)
    (main : MainActivationTraceAfter setup leaks bounds horizon scheduler source focal cutoff top) :
    MainActivationTraceAfter setup leaks bounds horizon scheduler source focal cutoff prior := by
  induction isPrefix with
  | refl => exact main
  | extend _ _ _ _ ih => exact ih main.1

/-- The future-main condition reads back the actual supported response step at
any prefix whose source is beyond the comparison boundary. -/
theorem mainActivationStep_of_tracePrefix
    (source : setup.intendedModel.BehavioralAssessment) (focal : Player) (cutoff : Nat)
    {first final : (onePacketProtocol setup leaks bounds horizon scheduler).State}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace first)
    (joint : Player → Option (application setup leaks).Action)
    (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal first joint)
    {next : (onePacketProtocol setup leaks bounds horizon scheduler).State}
    (realized : next ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step first
      ⟨joint, legal⟩).support)
    {top : (onePacketProtocol setup leaks bounds horizon scheduler).Trace final}
    (isPrefix : TracePrefix (prior.extend joint legal realized) top)
    (main : MainActivationTraceAfter setup leaks bounds horizon scheduler source focal cutoff top)
    (later : cutoff ≤ prior.length) :
    MainActivationStep setup leaks bounds horizon scheduler source focal first joint :=
  (mainActivationTraceAfter_of_tracePrefix source focal cutoff isPrefix main).2 later

end Vegas

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
theorem recovery_foreign_nonmain_prefix_of_firstFailure
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal owner : Player)
    (different : owner ≠ focal)
    {initial : PMF (RecoveryState (graph setup))}
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
    (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
    {horizon : Nat} {scheduler : ((runtime setup).recoveryApplication leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (start : (application setup leaks).Control)
    (startTrace : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace (some start))
    (remaining : Nat) (execution : (application setup leaks).Execution)
    (trace : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace
        (some ⟨remaining + 1, none, execution⟩))
    (startPrefix : TracePrefix startTrace trace)
    (current event : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : PublicExclusionRecord
      (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source focal trace)
    (notOwed : ∀ point, decodedPoint setup execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (owned : (graph setup).actor? event = some owner)
    (command : (application setup leaks).Command) (next : (application setup leaks).Execution)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    (target : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace
        (some ⟨remaining, command.actor? (application setup leaks), next⟩))
    (tracePrefix : TracePrefix trace target) (failed : next.application.PublicFailure event) :
    ∃ (before : (application setup leaks).Control)
      (prior : (onePacketProtocol setup leaks bounds horizon
        (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace (some before))
      (response : (application setup leaks).Action)
      (joint : Player → Option (application setup leaks).Action)
      (legal : (onePacketProtocol setup leaks bounds horizon
        (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Legal
          (some before) joint)
      (realized : some ⟨before.remaining, none,
        before.execution.respond (application setup leaks) owner response⟩ ∈
        ((onePacketProtocol setup leaks bounds horizon
          (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).step
            (some before) ⟨joint, legal⟩).support),
      TracePrefix startTrace prior ∧ TracePrefix (prior.extend joint legal realized) target ∧
      before.actor = some owner ∧ joint owner = some response ∧
      pendingEvent setup leaks owner (some (before.execution.recall owner,
        before.execution.observe (application setup leaks) owner)) = some event ∧
      (∀ previous ∈ before.execution.recall owner,
        ¬ ActivatedAt setup leaks owner event previous) ∧
      responseChoice setup leaks bounds (initialLaw setup) horizon
        (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) owner
        (some (before.execution.recall owner,
          before.execution.observe (application setup leaks) owner)) response ∉
        (honestChoice setup leaks bounds (initialLaw setup) horizon
          (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source owner
          (some (before.execution.recall owner,
            before.execution.observe (application setup leaks) owner))).support := by
  let nativeScheduler := RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler
  have origin := firstPublicFailure_pending_or_due execution next command reached clear event owner
    owned failed
  have extracted : ∃ (before : (application setup leaks).Control)
      (prior : (onePacketProtocol setup leaks bounds horizon nativeScheduler).Trace (some before))
      (response : (application setup leaks).Action)
      (joint : Player → Option (application setup leaks).Action)
      (legal : (onePacketProtocol setup leaks bounds horizon nativeScheduler).Legal
        (some before) joint)
      (realized : some ⟨before.remaining, none,
        before.execution.respond (application setup leaks) owner response⟩ ∈
        ((onePacketProtocol setup leaks bounds horizon nativeScheduler).step
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
    · exact recovery_foreign_firstActivation_prefix_of_due wellFormed source focal owner different
        initialized nativeLaw opportunity timely start ⟨remaining + 1, none, execution⟩ startTrace
        trace startPrefix current event turn clear regular notOwed rfl owned origin.1 entered
        activated due
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
  have selected : (responseChoice setup leaks bounds (initialLaw setup) horizon nativeScheduler
      owner (some (before.execution.recall owner,
        before.execution.observe (application setup leaks) owner)) response).1 = some response := by
    simp only [responseChoice, dite_eq_left offered]
  have notMain : responseChoice setup leaks bounds (initialLaw setup) horizon nativeScheduler owner
      (some (before.execution.recall owner,
        before.execution.observe (application setup leaks) owner)) response ∉
      (honestChoice setup leaks bounds (initialLaw setup) horizon nativeScheduler source owner
        (some (before.execution.recall owner,
          before.execution.observe (application setup leaks) owner))).support := by
    rcases before with ⟨responsesLeft, actor, earlierExecution⟩
    dsimp only at acting
    subst actor
    exact recovery_firstActivation_not_main_of_publicFailure bounds wellFormed covers capacity
      source focal initialized nativeLaw opportunity inclusion timely prior earlierClear
      earlierRegular earlierNotOwed event pending never _ response selected
      (prior.extend joint legal realized) remaining execution
      ((bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
        nativeScheduler trace) clear command next reached _ rfl target targetPrefix failed
  exact ⟨before, prior, response, joint, legal, realized, future, targetPrefix, acting, chosen,
    pending, never, notMain⟩

/-- A first foreign failure violates the future first-activation main condition. -/
theorem recovery_firstForeignFailure_not_mainActivationTraceAfter
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal owner : Player)
    (different : owner ≠ focal)
    {initial : PMF (RecoveryState (graph setup))}
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
    (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
    {horizon : Nat} {scheduler : ((runtime setup).recoveryApplication leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (start : (application setup leaks).Control)
    (startTrace : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace (some start))
    (remaining : Nat) (execution : (application setup leaks).Execution)
    (trace : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace
        (some ⟨remaining + 1, none, execution⟩))
    (startPrefix : TracePrefix startTrace trace)
    (current event : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : PublicExclusionRecord
      (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source focal trace)
    (notOwed : ∀ point, decodedPoint setup execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (owned : (graph setup).actor? event = some owner)
    (command : (application setup leaks).Command) (next : (application setup leaks).Execution)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    (target : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace
        (some ⟨remaining, command.actor? (application setup leaks), next⟩))
    (tracePrefix : TracePrefix trace target) (failed : next.application.PublicFailure event) :
    ¬ MainActivationTraceAfter setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source focal
      startTrace.length target := by
  intro main
  obtain ⟨before, prior, response, joint, legal, realized, future, afterPrefix, acting, chosen,
    pending, never, outside⟩ :=
    recovery_foreign_nonmain_prefix_of_firstFailure wellFormed covers
      capacity source focal owner different initialized nativeLaw opportunity inclusion timely start
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
