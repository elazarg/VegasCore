/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketPendingPool
import Vegas.Game.SourceServiceTimedCompletion

/-! # How an owned event completes

When a scheduler command completes an owned event of the default runtime,
either an included packet naming that event was accepted, sent by its actor,
or the event completed by expiry, with its expiry action
(`Vegas.owned_completion_cause`). A binding that expires decodes to a failed
binding, so the decoded point after it is not a point of the intended game
(`Vegas.SourceProgram.ProtocolState.not_intended_of_decode_failure`).
-/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem intended_entry_config {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ)
    (intended : Intended program (entry program config)) : ∃ unresolved,
      config.Intended unresolved := by
  cases program with
  | ret => exact ⟨_, intended⟩
  | sample => exact ⟨_, intended.1⟩
  | commit => exact ⟨_, intended.1⟩
  | reveal => exact ⟨_, intended.1⟩

/-- **A failed binding leaves the intended game.** At a point decoded after
`count` events, stepping with the decoded failed binding of the event at index
`count`, a binding event, reaches no point of the intended game. -/
theorem not_intended_of_decode_failure {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    ∀ (count : Nat) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (state : ProtocolState program) (bound : count < eventCount program) {owner : Player}
      {payload : L.Ty}
      (outputEq : outputLayout program ⟨count, bound⟩ = .binding owner payload)
      (target : ProtocolState program),
      decodeSourcePrefix? program refs registry revelations outputs count store history =
          some state →
      target ∈ (step program state (fun _ => decodeEventAction program ⟨count, bound⟩
        (cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (PublicationResult.failure : PublicationResult (L.Val payload))))).support →
      ¬ Intended program target := by
  induction program with
  | ret _ =>
      intro count _ _ _ _ _ _ _ bound
      simp [eventCount] at bound
  | sample _ _ _ next ih =>
      intro count refs registry revelations outputs store history state bound owner payload
        outputEq target decoded reached
      cases count with
      | zero => cases outputEq
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) outputEq after
            read supported
  | commit name commitOwner fresh guard next ih =>
      intro count refs registry revelations outputs store history state bound owner payload
        outputEq target decoded reached
      cases count with
      | zero =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨cells, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have ownerEq : commitOwner = owner :=
            (EventGraph.EventField.binding.inj outputEq).1
          have payloadEq := (EventGraph.EventField.binding.inj outputEq).2
          subst ownerEq
          subst payloadEq
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst same
          intro intended
          obtain ⟨_, configIntended⟩ := intended_entry_config next _ (by exact intended)
          obtain ⟨value, bound⟩ := configIntended.bound .here
          simp [decodeEventAction, commitSuccessor, OwnAction.binding] at bound
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) outputEq after
            read supported
  | reveal published revealOwner name fresh source unresolved next ih =>
      intro count refs registry revelations outputs store history state bound owner payload
        outputEq target decoded reached
      cases count with
      | zero => cases outputEq
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact fun intended => ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound)
            outputEq after read supported intended.2

end Vegas.SourceProgram.ProtocolState

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- **How an owned event completes.** When an environment step completes a
ready owned event, either an included packet naming that event was accepted,
sent by the event's actor, or the event completed with its expiry action. -/
theorem owned_completion_cause (execution next : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    {event : (graph setup).EventId} {owner : Player}
    (owned : (graph setup).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    (action : (graph setup).Action event)
    (member : next.application.config ∈
      (execution.application.config.step event ready action).support) :
    (∃ message ∈ next.network.ledger, (message.id, true) ∈ next.receipts ∧
        message.payload.call.event? (graph setup) = some event ∧
        (graph setup).actor? event = some message.sender) ∨
      ExpiryAction event action := by
  have stutter : next.application.config = execution.application.config → False :=
    config_ne_of_step member
  cases command with
  | application command =>
      right
      obtain ⟨changed, _⟩ := applicationStep_facts execution next command reached
      cases command with
      | advanceClock =>
          exfalso
          apply stutter
          simp only [EventGraphRuntime.environmentStep, PMF.mem_support_pure_iff] at changed
          rw [changed]
      | executeSample sampled =>
          exfalso
          obtain ⟨_, effect⟩ := environmentStep_executeSample_config_activated (runtime setup)
            execution.application next.application sampled changed
          rcases effect with ⟨configEq, _⟩ | ⟨sampledReady, sampledAction, sampledMember, _⟩
          · exact stutter configEq
          · have same := step_completion_unique sampledMember member
            cases same
            rw [environmentStep_executeSample_of_nonsample (runtime setup) _ event ready
              (fun payload law outputEq codeEq sampledView => by
                have none := nodeView_sample_actor outputEq codeEq
                rw [owned] at none
                cases none), PMF.mem_support_pure_iff] at changed
            exact stutter (congrArg (fun state => state.config) changed)
      | expire expired =>
          obtain ⟨_, effect⟩ := environmentStep_expire_config_activated (runtime setup)
            execution.application next.application expired changed
          rcases effect with ⟨configEq, _⟩ | ⟨expiredReady, expiredAction, expiredMember, _⟩
          · exact (stutter configEq).elim
          · have same := step_completion_unique expiredMember member
            cases same
            obtain ⟨expiry, expiring⟩ := exists_expiryAction (setup := setup) owned
            have completes := (expire_completion (setup := setup) (mode := .sequential)
              (deadline := rankDeadline setup .sequential) execution.application next.application
              event ready changed (fun configEq => stutter configEq)).2 expiry expiring
            have unique := step_completion_unique member completes
            cases unique
            exact expiring
  | activate who =>
      exfalso
      apply stutter
      unfold ReactiveApplication.Execution.environmentStep at reached
      rw [PMF.support_map] at reached
      obtain ⟨updated, supported, rfl⟩ := reached
      rw [PMF.support_map] at supported
      obtain ⟨_, _, rfl⟩ := supported
      rfl
  | wait =>
      exfalso
      apply stutter
      unfold ReactiveApplication.Execution.environmentStep at reached
      rw [PMF.support_map] at reached
      obtain ⟨updated, supported, rfl⟩ := reached
      cases (PMF.mem_support_pure_iff _ _).mp supported
      rfl
  | «include» id =>
      let app := application setup leaks
      unfold ReactiveApplication.Execution.environmentStep at reached
      rw [PMF.support_map] at reached
      obtain ⟨updated, supported, rfl⟩ := reached
      cases (PMF.mem_support_pure_iff _ _).mp supported
      left
      change (execution.includePending app id).application.config ∈ _ at member
      change ∃ message ∈ (execution.includePending app id).network.ledger,
        (message.id, true) ∈ (execution.includePending app id).receipts ∧ _
      cases found : execution.network.lookup id with
      | none =>
          exact (config_ne_of_step member (by
            simp only [ReactiveApplication.Execution.includePending,
              MessageNetwork.includePending, found])).elim
      | some message =>
          obtain ⟨identified, _, ledgerEq⟩ := includePending_found execution.network
            id message found
          cases accepted : app.handle execution.application message with
          | none =>
              exact (config_ne_of_step member (by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.getD_none])).elim
          | some after =>
              have applicationEq : (execution.includePending app id).application = after := by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.getD_some]
              have receiptsEq : (execution.includePending app id).receipts =
                  execution.receipts ++ [(id, true)] := by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.isSome_some]
              have networkEq : (execution.includePending app id).network =
                  (execution.network.includePending id).2 := app.includePending_network execution id
              obtain ⟨_, namedEvent, named, namedReady, _, actor⟩ :=
                accepted_inclusion execution.application after message accepted
              obtain ⟨other, otherNamed, otherReady, otherAction, otherMember⟩ :=
                handle_config_mem_step (runtime setup) execution.application after _
                  (reactiveHandle_call accepted)
              have sameNamed : other = _ := Option.some.inj (otherNamed.symm.trans named)
              subst sameNamed
              rw [applicationEq] at member
              have same := step_completion_unique otherMember member
              cases same
              refine ⟨message, ?_, ?_, named, actor⟩
              · rw [networkEq, ledgerEq]
                exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
              · rw [receiptsEq, identified]
                exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

end Vegas
