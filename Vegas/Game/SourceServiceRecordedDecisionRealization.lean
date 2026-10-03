/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRecordedDecisionCompletion

/-! # Completion through an actually recorded realizing packet

The owner's actual one-call invariant and fresh-identifier uniqueness identify
any accepted current-event packet with its original recorded packet. Expiry
would create a public miss, contradicted by protected inclusion. Every stopped
completed configuration consequently belongs to the original realizing action's
graph step, for any timing and arbitrary foreign policies.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem recorded_realization_complete_round {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy) (owner : Player)
    {turns : Nat} (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (follows : players owner =
      sourceServiceTurnPolicy setup leaks bound turns timing profile owner)
    (count : Nat) (within : count + 1 ≤ horizon)
    (execution next : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner)
    (config : (graph setup).Config) (same : execution.application.config = config)
    (ready : config.cut.Ready event) (action : (graph setup).Action event)
    (entry : (application setup leaks).PlayerEntry) (member : entry ∈ execution.recall owner)
    (message : Message Player (WitnessedPacket (graph setup)))
    (named : (runtime setup).submittedEvent? leaks entry.action = some event)
    (call : FreshCall setup leaks owner event bound entry message)
    (realized : RealizesAt leaks config execution.application event action entry message)
    (moved : next ∈ ((application setup leaks).round scheduler players execution).support)
    (changed : next.application.config ≠ config) :
    next.application.config ∈ (config.step event ready action).support := by
  let app := application setup leaks
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
    count (by omega) execution reached
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have readyNow : execution.application.config.cut.Ready event := by rw [same]; exact ready
  have sole (other : (graph setup).EventId)
      (otherReady : execution.application.config.cut.Ready other) : other = event :=
    (soleReady_of_ready setup execution.application readyNow).2 other
      ((execution.application.publicView_eventReady other).mpr otherReady)
  have nextReached : next ∈ (app.roundsFrom (initialLaw setup) scheduler players
      (count + 1)).support := by
    rw [app.roundsFrom_succ, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨execution, reached, moved⟩
  obtain ⟨command, _, middle, environment, cases⟩ := round_cases setup leaks moved
  have memberNext : entry ∈ next.recall owner := by
    have middleMember : entry ∈ middle.recall owner := by
      rw [app.environmentStep_recall execution middle command environment]
      exact member
    rcases cases with ⟨_, rfl⟩ | ⟨actor, _, response, _, rfl⟩
    · exact middleMember
    · exact app.respond_recall_mono middle actor owner response middleMember
  have clearNext := sourceServiceTurnPolicy_recorded_decision_no_miss contract players owner
    timing profile follows (count + 1) within next nextReached event owned
    (((runtime setup).eventRecorded_iff leaks _ event).mpr ⟨entry, memberNext, named⟩)
  have configNext : next.application.config = middle.application.config := by
    rcases cases with ⟨_, rfl⟩ | ⟨actor, _, response, _, rfl⟩
    · rfl
    · exact ((runtime setup).reactive_respond_application leaks middle actor response).1
  have markerNext : next.application.missedEvents = middle.application.missedEvents := by
    rcases cases with ⟨_, rfl⟩ | ⟨actor, _, response, _, rfl⟩
    · rfl
    · exact congrArg PublicView.missedEvents
        ((runtime setup).reactive_respond_application leaks middle actor response).2
  rw [markerNext] at clearNext
  rw [configNext] at changed ⊢
  rw [← same] at changed
  cases command with
  | activate actor =>
      rw [activation_application setup leaks execution middle actor environment] at changed
      exact (changed rfl).elim
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at environment
      cases (PMF.mem_support_pure_iff _ _).mp environment
      exact (changed rfl).elim
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at environment
      cases (PMF.mem_support_pure_iff _ _).mp environment
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
        at changed ⊢
      cases found : execution.network.lookup id with
      | none =>
          simp only [found] at changed
          exact (changed rfl).elim
      | some packet =>
          simp only [found] at changed ⊢
          cases accepted : app.handle execution.application packet with
          | none =>
              rw [accepted] at changed
              exact (changed rfl).elim
          | some state =>
              have handled := reactiveHandle_call accepted
              change state.config ∈ _
              obtain ⟨addressed, packetNamed, packetReady, _, _⟩ :=
                handle_config_mem_step (runtime setup) _ _ _ handled
              have addressedEq := sole addressed packetReady
              subst addressed
              have actor := handle_sender_actor (runtime setup) _ _ _ handled event packetNamed
              have sender : packet.sender = owner := Option.some.inj (actor.symm.trans owned)
              have pending : packet ∈ execution.network.pending := List.mem_of_find?_eq_some found
              obtain ⟨issuer, issuerMember, material, transmission, emitted, state', known,
                issued⟩ := facts.provenance.pending packet pending
              rw [sender] at issuerMember
              have issuerNamed : (runtime setup).submittedEvent? leaks issuer.action =
                  some event := by
                unfold EventGraphRuntime.submittedEvent?
                rw [transmission]
                change (app.packet state' packet.sender known material).call.event? (graph setup) =
                  some event
                rw [issued]
                exact packetNamed
              have once := (serialFacts_roundsFrom contract players owner timing profile follows
                count (by omega) execution reached).2.1
              have identifier := once issuer issuerMember entry member event packet message
                issuerNamed named emitted call.emitted
              have input : message ∈ execution.network.inputs := by
                have output : message ∈ app.outputs (execution.recall owner) :=
                  List.mem_filterMap.mpr ⟨entry, member, call.emitted⟩
                rw [← facts.inputs owner] at output
                exact (List.mem_filter.mp output).1
              have equal := (facts.unique.inputs message input).pending packet pending identifier
              subst packet
              exact include_realized execution facts.stable config same event ready
                (congrFun facts.remembered event) owner owned action entry member call.ready
                message call.authored realized state handled
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ environment
      obtain ⟨state, stepped, rfl⟩ := PMF.support_map .. ▸ supported
      change state.config ≠ execution.application.config at changed
      change state.config ∈ _
      change event ∉ state.missedEvents at clearNext
      change state ∈ (environmentStep (runtime setup) execution.application command).support
        at stepped
      cases command with
      | advanceClock =>
          simp only [environmentStep, PMF.mem_support_pure_iff] at stepped
          subst stepped
          exact (changed rfl).elim
      | executeSample other =>
          by_cases otherReady : execution.application.config.cut.Ready other
          · have equal := sole other otherReady
            subst other
            rw [environmentStep_executeSample_of_nonsample _ _ _ otherReady (by
              intro payload law outputEq codeEq _
              have none := nodeView_sample_actor outputEq codeEq
              rw [owned] at none
              cases none), PMF.mem_support_pure_iff] at stepped
            subst stepped
            exact (changed rfl).elim
          · rw [environmentStep_executeSample_of_not_ready _ _ _ otherReady,
              PMF.mem_support_pure_iff] at stepped
            subst stepped
            exact (changed rfl).elim
      | expire other =>
          by_cases otherReady : execution.application.config.cut.Ready other
          · have equal := sole other otherReady
            subst other
            obtain ⟨entered, activated, due⟩ := expiry_due _ _ event readyNow stepped changed
            apply (clearNext ?_).elim
            rw [environmentStep_expire_missedEvents _ _ _ event stepped,
              ite_eq_left ⟨readyNow, ⟨entered, activated, due⟩, by rw [owned]; simp⟩]
            exact Finset.mem_insert_self _ _
          · rw [environmentStep_expire_of_not_ready _ _ _ otherReady,
              PMF.mem_support_pure_iff] at stepped
            subst stepped
            exact (changed rfl).elim

private theorem recorded_realization_runUntil {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy) (owner : Player)
    {turns : Nat} (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (follows : players owner =
      sourceServiceTurnPolicy setup leaks bound turns timing profile owner)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner)
    (config : (graph setup).Config) (ready : config.cut.Ready event)
    (action : (graph setup).Action event)
    (entry : (application setup leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup)))
    (named : (runtime setup).submittedEvent? leaks entry.action = some event)
    (call : FreshCall setup leaks owner event bound entry message) :
    ∀ fuel count, count + fuel ≤ horizon → ∀ execution,
      execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler players
        count).support → entry ∈ execution.recall owner → execution.application.config = config →
      RealizesAt leaks config execution.application event action entry message →
      ∀ stopped ∈ ((application setup leaks).runUntil scheduler players
          (fun final => event ∈ final.application.config.cut.completed) fuel execution).support,
        stopped.application.config = config ∨
          stopped.application.config ∈ (config.step event ready action).support := by
  let app := application setup leaks
  intro fuel
  induction fuel with
  | zero =>
      intro count _ execution _ _ same _ stopped reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact Or.inl same
  | succ fuel ih =>
      intro count within execution reached member same realized stopped supported
      have running : event ∉ execution.application.config.cut.completed := by
        rw [same]
        exact ready.1
      simp only [ReactiveApplication.runUntil, running, ↓reduceIte] at supported
      obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      have middleReached : middle ∈ (app.roundsFrom (initialLaw setup) scheduler players
          (count + 1)).support := by
        rw [app.roundsFrom_succ, PMF.support_bind]
        exact Set.mem_iUnion₂.mpr ⟨execution, reached, moved⟩
      by_cases unchanged : middle.application.config = config
      · have retained : app.PolicyInvariant players
            (fun current => entry ∈ current.recall owner) := {
          respond := fun current actor response present _ =>
            app.respond_recall_mono current actor owner response present
          environment := fun current next command present changed => by
            rw [app.environmentStep_recall current next command changed]
            exact present }
        have one : middle ∈ (app.runRounds scheduler players 1 execution).support := by
          simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using moved
        exact ih (count + 1) (by omega) middle middleReached
          (retained.runRounds scheduler 1 execution middle member one) unchanged
          (realized.round moved) stopped rest
      · have complete := recorded_realization_complete_round contract players owner timing profile
          follows count (by omega) execution middle reached event owned config same ready action
          entry member message named call realized moved unchanged
        have finished : event ∈ middle.application.config.cut.completed := by
          rw [config.step_cut event ready action _ complete]
          exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)
        rw [app.runUntil_of_stop scheduler players _ fuel middle finished] at rest
        cases (PMF.mem_support_pure_iff _ _).mp rest
        exact Or.inr complete

/-- Complete play accepts only the originally recorded realizing action before
the current event's completion. The owner's timing is arbitrary. -/
theorem sourceServiceTurnPolicy_recorded_realization_completion {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy) (owner : Player)
    {turns : Nat} (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (follows : players owner =
      sourceServiceTurnPolicy setup leaks bound turns timing profile owner)
    (count : Nat) (within : count ≤ horizon) (start : (application setup leaks).Execution)
    (reached : start ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner)
    (ready : start.application.config.cut.Ready event) (action : (graph setup).Action event)
    (entry : (application setup leaks).PlayerEntry) (member : entry ∈ start.recall owner)
    (message : Message Player (WitnessedPacket (graph setup)))
    (named : (runtime setup).submittedEvent? leaks entry.action = some event)
    (call : FreshCall setup leaks owner event bound entry message)
    (realized : RealizesAt leaks start.application.config start.application event action entry
      message)
    (stopped : (application setup leaks).Execution)
    (supported : stopped ∈ ((application setup leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon start).support) :
    stopped.application.config ∈ (start.application.config.step event ready action).support := by
  let app := application setup leaks
  have length := app.roundsFrom_recall (initialLaw setup) scheduler players count start reached
  rcases recorded_realization_runUntil contract players owner timing profile follows event owned
      start.application.config ready action entry message named call
      (horizon - start.environmentRecall.length) count (by omega) start reached member rfl
      realized stopped supported with unchanged | completed
  · obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
      count within start reached
    rw [← length] at trace
    have complete := runUntilHorizon_completes contract.completes (by omega) trace stopped supported
    rw [unchanged] at complete
    exact (ready.1 complete).elim
  · exact completed

end Vegas
