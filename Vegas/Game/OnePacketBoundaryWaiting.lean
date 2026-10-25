/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketForeignSubmission
import Vegas.Game.AnchoredOpeningClients
import Vegas.Game.OnePacketCompletionOrigin
import Vegas.Pending.ReactiveOwnerActivationRecall
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryInvariant

/-! # Waiting for the first owner callback under counted native service -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable [Fintype Player]
  {bounds : MessageBounds (graph setup)}
  {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
  {delay bound : (graph setup).EventId → Nat}
  (opportunity : ∀ control : (application setup leaks).Control,
    (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control) →
    ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
    OpportunityAt (runtime setup) leaks control.execution delay)
  (timely : (runtime setup).AsyncTimely delay bound)

local notation "Menu" => bounds.onePacketMenu (runtime setup) leaks

include opportunity timely in
/-- Before the owner's first ready callback, a scheduler command cannot complete
its event. A pending authentic packet would record an earlier ready callback;
a due expiry would require one under pointwise opportunity.
The application therefore keeps both its source configuration and public clarity. -/
theorem counted_waiting_environment
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (trace : ((Menu).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk execution.application ∅))
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    (never : ∀ entry ∈ execution.recall owner, ¬ ActivatedAt setup leaks owner event entry)
    (command : (application setup leaks).Command) (next : (application setup leaks).Execution)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support) :
    next.application.config = execution.application.config ∧
      ExclusionEvidence 0 ∅ (RecoveryState.mk next.application ∅) := by
  have same : next.application.config = execution.application.config := by
    rcases environmentStep_configStep setup leaks execution next command reached with
      same | ⟨other, otherReady, action, member⟩
    · exact same
    · have which := ready_unique (setup := setup) execution.application.config.cut otherReady ready
      subst other
      rcases completion_pending_or_due execution next command reached ready action member owned with
        packet | ⟨_, entered, activated, due⟩
      · obtain ⟨message, pending, sender, named⟩ := packet
        have recorded := eventRecorded_of_pending trace owner event message pending sender named
        obtain ⟨entry, remembered, submitted⟩ :=
          ((runtime setup).eventRecorded_iff leaks (execution.recall owner) event).mp recorded
        have submissions := onePacket_ownSubmissionsAtTurn bounds trace ordered point decoded
          intendedPoint
          owner
        exact (never entry remembered (submissions entry remembered event submitted)).elim
      · have actual := opportunity _ trace clear
        have rawTrace := (Menu).toRawTrace (initialLaw setup) horizon scheduler trace
        obtain ⟨entry, remembered, activatedAt⟩ := due_owner_recalled_turn_of_opportunity
          (runtime setup) leaks timely (serviceGraph_revealRelaxedOrdered setup .sequential)
          _ rawTrace rfl actual event owner owned ready entered activated due
        exact (never entry remembered activatedAt).elim
  exact ⟨same, clear.completionStep_sameConfig
    ((reactiveApplication_completionStep (runtime setup) leaks).environmentStep
      execution next command reached) same⟩

include opportunity timely in
private theorem counted_waiting_transition
    {control : (application setup leaks).Control}
    (trace : ((Menu).protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅))
    {rank : Nat} (ordered : control.execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank control.execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (ready : control.execution.application.config.cut.Ready event)
    (never : ∀ entry ∈ control.execution.recall owner,
      ¬ ActivatedAt setup leaks owner event entry)
    (going : control.actor ≠ some owner)
    (joint : Player → Option (application setup leaks).Action)
    (target : (application setup leaks).ProtocolState)
    (realized : target ∈ ((application setup leaks).transition (initialLaw setup) horizon
      scheduler (some control) joint).support) :
    ∃ next, target = some next ∧
      next.execution.application.config = control.execution.application.config ∧
      ExclusionEvidence 0 ∅ (RecoveryState.mk next.execution.application ∅) ∧
      next.execution.recall owner = control.execution.recall owner := by
  let app := application setup leaks
  rcases control with ⟨remaining, active, execution⟩
  cases active with
  | some responder =>
      have different : owner ≠ responder := by
        intro same
        exact going (congrArg some same.symm)
      change target ∈ (PMF.pure
        (some (⟨remaining, none, execution.respond app responder ((joint responder).getD ⟨none⟩)⟩ :
          app.Control))).support at realized
      cases (PMF.mem_support_pure_iff _ _).mp realized
      refine ⟨_, rfl, ((runtime setup).reactive_respond_application leaks execution responder _).1,
        ?_, app.respond_recall_other execution responder owner different _⟩
      rcases responseEq : (joint responder).getD ⟨none⟩ with ⟨transmission⟩
      cases transmission with
      | none => exact clear
      | some submission => exact clear.submit responder submission
  | none =>
      cases remaining with
      | zero =>
          cases (PMF.mem_support_pure_iff _ _).mp realized
          exact ⟨_, rfl, rfl, clear, rfl⟩
      | succ remaining =>
          obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ realized)
          obtain ⟨next, reached, nextEq⟩ := PMF.support_map .. ▸ moved
          cases nextEq
          obtain ⟨same, nextClear⟩ := counted_waiting_environment opportunity
            timely trace clear ordered decoded intendedPoint owner event owned ready never command
            next reached
          exact ⟨_, rfl, same, nextClear,
            congrFun (app.environmentStep_recall execution next command reached) owner⟩

include opportunity timely in
/-- From an actual clear scheduler boundary with an untouched owned event,
the stopped behavioral run reaches its owner's first callback. Configuration,
source point, public clarity and the owner's complete recall are unchanged
through the waiting phase. All players' continuation policies are arbitrary. -/
theorem counted_waiting_until_firstActivation
    (completes : ∀ control : (application setup leaks).Control,
      (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
      (application setup leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (certificate : ((Menu).protocol (initialLaw setup) horizon
      scheduler).WellFoundedHistories)
    (players : ∀ player, ((Menu).information (initialLaw setup) horizon
      scheduler).BehavioralPolicy player)
    (start : ((Menu).protocol (initialLaw setup) horizon scheduler).History)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (current : start.state = some ⟨remaining, none, execution⟩)
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk execution.application ∅))
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    (never : ∀ entry ∈ execution.recall owner, ¬ ActivatedAt setup leaks owner event entry) :
    ∀ stopped ∈ (((Menu).information (initialLaw setup) horizon
      scheduler).runBehavioralUntil certificate players
        (fun history => (application setup leaks).actor history.state = some owner) start).support,
      ∃ control, stopped.state = some control ∧ control.actor = some owner ∧
        control.execution.application.config = execution.application.config ∧
        ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) ∧
        control.execution.recall owner = execution.recall owner := by
  classical
  let model := (Menu).information (initialLaw setup) horizon scheduler
  let protocol := (Menu).protocol (initialLaw setup) horizon scheduler
  let stopped := fun history : protocol.History =>
    (application setup leaks).actor history.state = some owner
  let property := fun history : protocol.History =>
    ∃ control, history.state = some control ∧
      control.execution.application.config = execution.application.config ∧
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) ∧
      control.execution.recall owner = execution.recall owner
  have initialProperty : property start := ⟨_, current, rfl, clear, rfl⟩
  have preserved : ∀ history, ¬ stopped history → ¬ protocol.terminal history.state →
      property history → ∀ next ∈ (model.runBehavioralFrom players 1 history).support,
        property next := by
    intro history going running valid next supported
    obtain ⟨control, state, same, controlClear, recalledEq⟩ := valid
    obtain ⟨⟨joint, _legal, realized⟩, _⟩ :=
      model.mem_support_runBehavioralFrom_one players running supported
    have controlGoing : control.actor ≠ some owner := by
      intro active
      apply going
      change (application setup leaks).actor history.state = some owner
      rw [state]
      exact active
    have trace : protocol.Trace (some control) := state ▸ history.trace
    have nextStep : next.state ∈ ((application setup leaks).transition (initialLaw setup) horizon
        scheduler (some control) joint).support := by
      rw [← state]
      exact realized
    obtain ⟨target, targetState, configEq, targetClear, targetRecall⟩ :=
      counted_waiting_transition opportunity timely trace controlClear
        (same ▸ ordered) (same ▸ decoded) intendedPoint owner event owned (same ▸ ready)
        (by rw [recalledEq]; exact never) controlGoing joint next.state nextStep
    exact ⟨target, targetState, configEq.trans same, targetClear, targetRecall.trans recalledEq⟩
  intro final supported
  obtain ⟨control, state, same, finalClear, recalledEq⟩ :=
    model.runBehavioralUntil_support_history_closed certificate players stopped property
      preserved start initialProperty final supported
  have active : control.actor = some owner := by
    rcases model.mem_support_runBehavioralUntil certificate players stopped start final supported
        with
      activated | terminal
    · change (application setup leaks).actor final.state = some owner at activated
      rw [state] at activated
      exact activated
    · have complete := completes control (state ▸ final.trace) finalClear (state ▸ terminal)
      have completed : event ∈ control.execution.application.config.cut.completed := by
        rw [complete]
        exact Finset.mem_univ _
      rw [same] at completed
      exact (ready.1 completed).elim
  exact ⟨control, state, active, same, finalClear, recalledEq⟩


include opportunity timely in
/-- A genuine source boundary reaches a pending first owner callback under
arbitrary play. Its source configuration is unchanged and its complete owner
recall still equals the boundary recall. -/
theorem counted_boundary_firstActivation
    (completes : ∀ control : (application setup leaks).Control,
      (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
      (application setup leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (certificate : ((Menu).protocol (initialLaw setup) horizon
      scheduler).WellFoundedHistories)
    (players : ∀ player, ((Menu).information (initialLaw setup) horizon
      scheduler).BehavioralPolicy player)
    (start : ((Menu).protocol (initialLaw setup) horizon scheduler).History)
    {rank : Nat} {execution : (application setup leaks).Execution}
    (current : start.state =
      some ⟨horizon - execution.environmentRecall.length, none, execution⟩)
    (boundary : ReachedBoundary setup leaks horizon scheduler rank execution)
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk execution.application ∅))
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (owner : Player) (event : (graph setup).EventId) (atRank : event.val = rank)
    (owned : (graph setup).actor? event = some owner) :
    ∀ stopped ∈ (((Menu).information (initialLaw setup) horizon
      scheduler).runBehavioralUntil certificate players
        (fun history => (application setup leaks).actor history.state = some owner) start).support,
      ∃ (remaining : Nat) (anchor : (application setup leaks).Execution),
        stopped.state = some ⟨remaining, some owner, anchor⟩ ∧
        anchor.application.config = execution.application.config ∧
        ExclusionEvidence 0 ∅ (RecoveryState.mk anchor.application ∅) ∧
        anchor.recall owner = execution.recall owner ∧
        pendingEvent setup leaks owner
          (some (anchor.recall owner,
            anchor.observe (application setup leaks) owner)) = some event ∧
        ∀ entry ∈ anchor.recall owner, ¬ ActivatedAt setup leaks owner event entry := by
  have ready := (ready_iff_rank setup _ rank boundary.ordered event).mpr atRank
  have never : ∀ entry ∈ execution.recall owner, ¬ ActivatedAt setup leaks owner event entry := by
    intro entry remembered activated
    exact boundary.untouched event (by omega) owner entry remembered
      (PublicView.ownTurn?_spec _ owner event activated).1
  intro stopped supported
  obtain ⟨control, state, active, same, finalClear, recalledEq⟩ :=
    counted_waiting_until_firstActivation opportunity timely completes
      certificate players start current clear boundary.ordered decoded intendedPoint owner event
      owned ready never stopped supported
  rcases control with ⟨remaining, actor, anchor⟩
  dsimp only at active
  subst actor
  have trace : ((Menu).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some owner, anchor⟩) := state ▸ stopped.trace
  have turn : anchor.application.publicView.ownTurn? owner = some event := by
    apply PublicView.ownTurn?_of_ownTurn
    exact State.ownTurn_of_ready _ (serviceGraph_revealRelaxedOrdered setup .sequential) owner event
      ((anchor.application.publicView_eventReady event).mpr (same ▸ ready)) owned
  have finalNever : ∀ entry ∈ anchor.recall owner,
      ¬ ActivatedAt setup leaks owner event entry := by
    rw [recalledEq]
    exact never
  have unrecorded : (runtime setup).eventRecorded leaks (anchor.recall owner) event = false := by
    cases recorded : (runtime setup).eventRecorded leaks (anchor.recall owner) event with
    | false => rfl
    | true =>
        obtain ⟨entry, remembered, submitted⟩ :=
          ((runtime setup).eventRecorded_iff leaks (anchor.recall owner) event).mp recorded
        have submissions := onePacket_ownSubmissionsAtTurn bounds trace (same ▸ boundary.ordered)
          point (same ▸ decoded) intendedPoint owner
        exact (finalNever entry remembered (submissions entry remembered event submitted)).elim
  exact ⟨remaining, anchor, state, same, finalClear, recalledEq,
    pendingEvent_of_spec turn unrecorded, finalNever⟩


end Vegas
