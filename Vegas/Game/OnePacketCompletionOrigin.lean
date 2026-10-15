/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketCompletionCases
import Vegas.Pending.ExclusionPublicRecord

/-! # Operational origins of owned event completions -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Every scheduler move completing an owned event either consumes an actual
pending envelope of its owner or is a due expiry of that same event. -/
theorem completion_pending_or_due
    (execution next : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    {event : (graph setup).EventId} (ready : execution.application.config.cut.Ready event)
    (action : (graph setup).Action event)
    (member : next.application.config ∈
      (execution.application.config.step event ready action).support)
    {owner : Player} (owned : (graph setup).actor? event = some owner) :
    (∃ message ∈ execution.network.pending, message.sender = owner ∧
      message.payload.call.event? (graph setup) = some event) ∨
    (command = .application (.expire event) ∧
      ∃ entered, execution.application.activatedAt event = some entered ∧
        (runtime setup).deadline event ≤ execution.application.clock - entered) := by
  have stutter : next.application.config = execution.application.config → False :=
    config_ne_of_step member
  cases command with
  | activate who =>
      exfalso
      apply stutter
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨_, _, rfl⟩ := PMF.support_map .. ▸ supported
      rfl
  | wait =>
      exfalso
      apply stutter
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      cases (PMF.mem_support_pure_iff _ _).mp supported
      rfl
  | «include» id =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      cases (PMF.mem_support_pure_iff _ _).mp supported
      change (execution.includePending (application setup leaks) id).application.config ∈ _
        at member
      cases found : execution.network.lookup id with
      | none =>
          exact (config_ne_of_step member (by
            simp only [ReactiveApplication.Execution.includePending,
              MessageNetwork.includePending, found])).elim
      | some message =>
          cases accepted : (application setup leaks).handle execution.application message with
          | none =>
              exact (config_ne_of_step member (by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.getD_none])).elim
          | some after =>
              have applicationEq :
                  (execution.includePending (application setup leaks) id).application = after := by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.getD_some]
              obtain ⟨_, other, named, otherReady, _, acts⟩ :=
                accepted_inclusion execution.application after message accepted
              have call := reactiveHandle_call accepted
              obtain ⟨completed, namedAgain, completedReady, completedAction, completedMember⟩ :=
                handle_config_mem_step (runtime setup) execution.application after _ call
              have which : completed = other := Option.some.inj (namedAgain.symm.trans named)
              subst completed
              rw [applicationEq] at member
              cases step_completion_unique completedMember member
              exact Or.inl ⟨message, List.mem_of_find?_eq_some found,
                Option.some.inj (acts.symm.trans owned), named⟩
  | application command =>
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
          · cases step_completion_unique sampledMember member
            cases view : nodeView (graph setup) event with
            | sample _ _ outputEq codeEq =>
                rw [nodeView_sample_actor outputEq codeEq] at owned
                cases owned
            | bind _ _ _ _ | resolve _ _ _ _ _ _ =>
                rw [environmentStep_executeSample_of_nonsample (runtime setup) _ event ready
                  (fun _ _ _ _ same => by rw [view] at same; cases same),
                  PMF.mem_support_pure_iff] at changed
                exact stutter (congrArg (fun state => state.config) changed)
      | expire expired =>
          obtain ⟨_, effect⟩ := environmentStep_expire_config_activated (runtime setup)
            execution.application next.application expired changed
          rcases effect with ⟨configEq, _⟩ | ⟨expiredReady, expiredAction, expiredMember, _⟩
          · exact (stutter configEq).elim
          · cases step_completion_unique expiredMember member
            refine Or.inr ⟨rfl, ?_⟩
            cases activated : execution.application.activatedAt event with
            | none =>
                rw [environmentStep_expire_of_not_activated (runtime setup) _ event ready activated,
                  PMF.mem_support_pure_iff] at changed
                exact (stutter (congrArg (fun state => state.config) changed)).elim
            | some entered =>
                by_cases due : (runtime setup).deadline event ≤
                    execution.application.clock - entered
                · exact ⟨entered, rfl, due⟩
                · rw [environmentStep_expire_of_not_due (runtime setup) _ event ready entered
                    activated due, PMF.mem_support_pure_iff] at changed
                  exact (stutter (congrArg (fun state => state.config) changed)).elim

/-- A new public failure at an environment move from a clear state is at that
move's actual owned graph step, so its origin is pending traffic or due expiry. -/
theorem firstPublicFailure_pending_or_due
    (execution next : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    (clear : PublicExclusionRecord
      (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (failed : next.application.PublicFailure event) :
    execution.application.config.cut.Ready event ∧
      ((∃ message ∈ execution.network.pending, message.sender = owner ∧
        message.payload.call.event? (graph setup) = some event) ∨
      (command = .application (.expire event) ∧
        ∃ entered, execution.application.activatedAt event = some entered ∧
          (runtime setup).deadline event ≤ execution.application.clock - entered)) := by
  have notFailed : ¬ execution.application.PublicFailure event := by
    intro before
    have excluded := (clear.excluded owner).mpr ⟨event, owned, before⟩
    exact Finset.notMem_empty owner excluded
  have footprint := completionStep_reactive_environmentStep (runtime setup) leaks execution next
    command reached
  rcases footprint with ⟨same, accepted, _⟩ |
    ⟨completed, ready, action, member, _, acceptedOnly⟩
  · exfalso
    apply notFailed
    apply (State.PublicFailure.congr event (by rw [same]) (by rw [same]) ?_).mp failed
    rw [accepted]
  · have which : event = completed := by
      by_contra different
      apply notFailed
      exact (State.PublicFailure.of_step_of_ne member
        (fun field changed => (acceptedOnly field changed).2) different).mp failed
    subst completed
    exact ⟨ready, completion_pending_or_due execution next command reached ready action member
      owned⟩

end Vegas
