/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRecordedDecisionRealization
import Vegas.Pending.ReactiveDecisionMiss

/-! # Actual completion after one timely canonical decision

A canonical owned decision can still be accepted outside its protected inclusion
window. After one actual transmission, the owner remains silent until the event
completes. Every completion then either makes the chosen effective typed step or
records the real public miss. Foreign responses and scheduler choices remain
arbitrary. No acceptance probability, source posterior or incentive is assumed.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Actual timeliness suffices to realize an effective canonical choice. The
inclusion bound of the asynchronous contract is not used in this local fact. -/
theorem sourceServiceCanonicalDecision_timely_realizes {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler} {owner : Player}
    {execution : (application setup leaks).Execution}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some owner, execution⟩))
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline (runtime setup) event)
    (action : (graph setup).Action event)
    (effective : EffectiveAction execution.application.config event action) :
    let app := application setup leaks
    let response := (runtime setup).canonicalServiceDecision leaks owner (execution.recall owner)
      (execution.observe app owner) event action
    ∃ material, response = ⟨some material⟩ ∧
      let message : Message Player (WitnessedPacket (graph setup)) :=
        ⟨(owner, execution.network.nextSerial owner), app.packet
          (app.submit execution.application owner material) owner
          (execution.network.known owner) material⟩
      let entry : app.PlayerEntry := ⟨execution.observe app owner, response, some message⟩
      message.sender = owner ∧ message.payload.call.event? (graph setup) = some event ∧
        entry.beforeView.application.publicView.EventReady event ∧
        RealizesAt leaks execution.application.config
          (execution.respond app owner response).application event action entry message := by
  intro app response
  cases activated : execution.application.activatedAt event with
  | none => simp only [State.WithinDeadline, activated] at timely
  | some entered =>
      have deadline : execution.application.clock - entered < (runtime setup).deadline event :=
        by simpa only [State.WithinDeadline, activated] using timely
      let delay : (graph setup).EventId → Nat := fun other =>
        if other = event then execution.application.clock - entered else 0
      have localTimely : AsyncTimely (runtime setup) delay (fun _ => 0) := by
        intro other _
        by_cases same : other = event
        · subst other
          simpa only [delay, ↓reduceIte, Nat.add_zero] using deadline
        · simp only [delay, same, ↓reduceIte, Nat.zero_add]
          exact runtime_deadline_pos setup other
      obtain ⟨material, responseEq, call, realized⟩ := firstTurn_freshCall localTimely trace
        event owned ready entered activated (by simp only [delay, ↓reduceIte]; omega)
          action effective
      exact ⟨material, responseEq, call.authored, call.addressed, call.ready, realized⟩

private def SoleDecisionPacket (execution : (application setup leaks).Execution)
    (owner : Player) (event : (graph setup).EventId)
    (message : Message Player (WitnessedPacket (graph setup))) : Prop :=
  ∀ entry ∈ execution.recall owner, ∀ packet,
    entry.emitted = some packet → packet.payload.call.event? (graph setup) = some event →
      packet = message

private theorem soleDecisionPacket_silent_invariant
    (players : Player → (application setup leaks).Policy) (owner : Player)
    (follows : players owner = (application setup leaks).silentPolicy)
    (event : (graph setup).EventId)
    (message : Message Player (WitnessedPacket (graph setup))) :
    (application setup leaks).PolicyInvariant players
      (fun execution => SoleDecisionPacket execution owner event message) where
  respond execution actor response valid chosen := by
    by_cases same : owner = actor
    · subst actor
      rw [follows] at chosen
      cases (application setup leaks).silentPolicy_cases _ _ response chosen
      intro entry member packet emitted named
      simp only [ReactiveApplication.Execution.respond, ↓reduceIte] at member
      rcases List.mem_append.mp member with before | last
      · exact valid entry before packet emitted named
      · cases List.mem_singleton.mp last
        cases emitted
    · intro entry member packet emitted named
      rw [ReactiveApplication.respond_recall_other (application setup leaks) execution actor owner
        same response] at member
      exact valid entry member packet emitted named
  environment execution next command valid moved := by
    unfold SoleDecisionPacket at valid ⊢
    rw [ReactiveApplication.environmentStep_recall (application setup leaks) execution next
      command moved]
    exact valid

private theorem realizingDecision_changed_round {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (players : Player → (application setup leaks).Policy) (owner : Player)
    {execution next : (application setup leaks).Execution}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner)
    (config : (graph setup).Config) (same : execution.application.config = config)
    (ready : config.cut.Ready event) (action : (graph setup).Action event)
    (entry : (application setup leaks).PlayerEntry) (member : entry ∈ execution.recall owner)
    (message : Message Player (WitnessedPacket (graph setup)))
    (authored : message.sender = owner)
    (seen : entry.beforeView.application.publicView.EventReady event)
    (solePacket : SoleDecisionPacket execution owner event message)
    (realized : RealizesAt leaks config execution.application event action entry message)
    (moved : next ∈ ((application setup leaks).round scheduler players execution).support)
    (changed : next.application.config ≠ config) :
    event ∈ next.application.missedEvents ∨
      next.application.config ∈ (config.step event ready action).support := by
  let app := application setup leaks
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have readyNow : execution.application.config.cut.Ready event := by rw [same]; exact ready
  have sole (other : (graph setup).EventId)
      (otherReady : execution.application.config.cut.Ready other) : other = event :=
    (soleReady_of_ready setup execution.application readyNow).2 other
      ((execution.application.publicView_eventReady other).mpr otherReady)
  obtain ⟨command, _, middle, environment, cases⟩ := round_cases setup leaks moved
  have configNext : next.application.config = middle.application.config := by
    rcases cases with ⟨_, rfl⟩ | ⟨actor, _, response, _, rfl⟩
    · rfl
    · exact ((runtime setup).reactive_respond_application leaks middle actor response).1
  have markerNext : next.application.missedEvents = middle.application.missedEvents := by
    rcases cases with ⟨_, rfl⟩ | ⟨actor, _, response, _, rfl⟩
    · rfl
    · exact congrArg PublicView.missedEvents
        ((runtime setup).reactive_respond_application leaks middle actor response).2
  rw [configNext] at changed ⊢
  rw [markerNext]
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
              right
              change state.config ∈ _
              obtain ⟨addressed, packetNamed, packetReady, _, _⟩ :=
                handle_config_mem_step (runtime setup) _ _ _ handled
              have addressedEq := sole addressed packetReady
              subst addressed
              have actor := handle_sender_actor (runtime setup) _ _ _ handled event packetNamed
              have sender : packet.sender = owner := Option.some.inj (actor.symm.trans owned)
              have pending : packet ∈ execution.network.pending := List.mem_of_find?_eq_some found
              obtain ⟨issuer, issuerMember, _material, _transmission, emitted, _state, _known,
                _issued⟩ := facts.provenance.pending packet pending
              rw [sender] at issuerMember
              have equal := solePacket issuer issuerMember packet emitted packetNamed
              subst packet
              exact include_realized execution facts.stable config same event ready
                (congrFun facts.remembered event) owner owned action entry member seen message
                  authored realized state handled
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ environment
      obtain ⟨state, stepped, rfl⟩ := PMF.support_map .. ▸ supported
      change state.config ≠ execution.application.config at changed
      change event ∈ state.missedEvents ∨ state.config ∈ _
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
            left
            rw [environmentStep_expire_missedEvents _ _ _ event stepped,
              ite_eq_left ⟨readyNow, ⟨entered, activated, due⟩, by rw [owned]; simp⟩]
            exact Finset.mem_insert_self _ _
          · rw [environmentStep_expire_of_not_ready _ _ _ otherReady,
              PMF.mem_support_pure_iff] at stepped
            subst stepped
            exact (changed rfl).elim

private theorem markedDecision_completed {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {execution : (application setup leaks).Execution}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, none, execution⟩))
    (event : (graph setup).EventId) (marked : event ∈ execution.application.missedEvents) :
    event ∈ execution.application.config.cut.completed := by
  rw [initialLaw_eq_inputs] at trace
  exact ((runtime setup).missedEvents_history leaks _ horizon scheduler trace event marked).1

private theorem realizingDecision_runUntil {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (players : Player → (application setup leaks).Policy) (owner : Player)
    (follows : players owner = (application setup leaks).silentPolicy)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner)
    (config : (graph setup).Config) (ready : config.cut.Ready event)
    (action : (graph setup).Action event) (entry : (application setup leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup)))
    (authored : message.sender = owner)
    (seen : entry.beforeView.application.publicView.EventReady event) :
    ∀ fuel remaining (execution : (application setup leaks).Execution),
      ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨remaining + fuel, none, execution⟩) →
      entry ∈ execution.recall owner → execution.application.config = config →
      SoleDecisionPacket execution owner event message →
      RealizesAt leaks config execution.application event action entry message →
      ∀ stopped ∈ ((application setup leaks).runUntil scheduler players
          (fun final => event ∈ final.application.config.cut.completed) fuel execution).support,
        stopped.application.config = config ∨ event ∈ stopped.application.missedEvents ∨
          stopped.application.config ∈ (config.step event ready action).support := by
  let app := application setup leaks
  intro fuel
  induction fuel with
  | zero =>
      intro remaining execution _ _ same _ _ stopped reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact Or.inl same
  | succ fuel ih =>
      intro remaining execution trace member same solePacket realized stopped reached
      have running : event ∉ execution.application.config.cut.completed := by
        rw [same]
        exact ready.1
      simp only [ReactiveApplication.runUntil, running, ↓reduceIte] at reached
      obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨middleTrace⟩ := app.raw_trace_round (initialLaw setup) horizon scheduler players
        (remaining + fuel) execution middle (by simpa only [Nat.add_assoc] using trace) moved
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
        exact ih remaining middle middleTrace
          (retained.runRounds scheduler 1 execution middle member one) unchanged
          ((soleDecisionPacket_silent_invariant players owner follows event message).runRounds
            scheduler 1 execution middle solePacket one)
          (realized.round moved) stopped rest
      · have changed := realizingDecision_changed_round players owner trace event owned config
          same ready action entry member message authored seen solePacket realized moved unchanged
        have finished : event ∈ middle.application.config.cut.completed := by
          rcases changed with marked | completed
          · exact markedDecision_completed middleTrace event marked
          · rw [config.step_cut event ready action _ completed]
            exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)
        rw [app.runUntil_of_stop scheduler players _ fuel middle finished] at rest
        cases (PMF.mem_support_pure_iff _ _).mp rest
        exact Or.inr changed

variable [Fintype Player]

/-- One actual canonical transmission, followed by owner silence, cannot be
completed by an unrelated packet. At the real horizon it makes its chosen
effective typed step or records a public miss. The transmission need only meet
the handler's actual deadline; it need not meet the protected inclusion gate. -/
theorem sourceServiceCanonicalDecision_include_or_miss
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (bounds : MessageBounds (graph setup))
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (owner : Player) (execution : (application setup leaks).Execution)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some owner, execution⟩))
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline (runtime setup) event)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
    (action : (graph setup).Action event)
    (effective : EffectiveAction execution.application.config event action)
    (players : Player → (application setup leaks).Policy)
    (follows : players owner = (application setup leaks).silentPolicy)
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ ((application setup leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon
      (execution.respond (application setup leaks) owner
        ((runtime setup).canonicalServiceDecision leaks owner (execution.recall owner)
          (execution.observe (application setup leaks) owner) event action))).support) :
    event ∈ stopped.application.config.cut.completed ∧
      (event ∈ stopped.application.missedEvents ∨ stopped.application.config ∈
        (execution.application.config.step event ready action).support) := by
  let app := application setup leaks
  let response := (runtime setup).canonicalServiceDecision leaks owner (execution.recall owner)
    (execution.observe app owner) event action
  have rawTrace := (bounds.riskMenu (runtime setup) leaks bound).toRawTrace _ _ _ trace
  have facts := legalFacts setup leaks horizon scheduler _ rawTrace
  have accounted := ((bounds.riskMenu (runtime setup) leaks bound).roundSupported_uniform
    (initialLaw setup) horizon scheduler trace).1
  change execution.environmentRecall.length + remaining = horizon at accounted
  obtain ⟨material, responseEq, authored, named, seen, realized⟩ :=
    sourceServiceCanonicalDecision_timely_realizes rawTrace event owned ready timely action
      effective
  let message : Message Player (WitnessedPacket (graph setup)) :=
    ⟨(owner, execution.network.nextSerial owner), app.packet
      (app.submit execution.application owner material) owner (execution.network.known owner)
        material⟩
  let entry : app.PlayerEntry := ⟨execution.observe app owner, response, some message⟩
  let start := execution.respond app owner response
  change stopped ∈ (app.runUntilHorizon scheduler players
    (fun final => event ∈ final.application.config.cut.completed) horizon start).support at reached
  have recallEq : start.recall owner = execution.recall owner ++ [entry] := by
    change (execution.respond app owner response).recall owner = _
    change response = ⟨some material⟩ at responseEq
    simpa only [entry, responseEq, message, app] using
      respond_submit_recall execution owner material
  have member : entry ∈ start.recall owner := by
    rw [recallEq]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have solePacket : SoleDecisionPacket start owner event message := by
    intro issuer issuerMember packet emitted addressed
    rw [recallEq] at issuerMember
    rcases List.mem_append.mp issuerMember with before | last
    · have output : packet ∈ app.outputs (execution.recall owner) :=
        List.mem_filterMap.mpr ⟨issuer, before, emitted⟩
      rw [← facts.inputs owner] at output
      have author : packet.sender = owner := of_decide_eq_true (List.mem_filter.mp output).2
      obtain ⟨original, originalMember, raw, transmission, _emitted, state, known, issued⟩ :=
        facts.provenance.inputs packet (List.mem_filter.mp output).1
      rw [author] at originalMember
      have submitted : (runtime setup).submittedEvent? leaks original.action = some event := by
        unfold EventGraphRuntime.submittedEvent?
        rw [transmission]
        change (app.packet state packet.sender known raw).call.event? (graph setup) = some event
        rw [issued]
        exact addressed
      have recorded := ((runtime setup).eventRecorded_iff leaks _ event).mpr
        ⟨original, originalMember, submitted⟩
      rw [unrecorded] at recorded
      cases recorded
    · cases List.mem_singleton.mp last
      exact (Option.some.inj emitted).symm
  have configEq : start.application.config = execution.application.config :=
    ((runtime setup).reactive_respond_application leaks execution owner response).1
  obtain ⟨startTrace⟩ := app.raw_trace_respond (initialLaw setup) horizon scheduler remaining
    execution owner response rawTrace
  have budget : start.environmentRecall.length + remaining = horizon := by
    rw [app.respond_environmentRecall]
    exact accounted
  have complete := runUntilHorizon_completes contract.completes (by omega)
    (by simpa only [show horizon - start.environmentRecall.length = remaining by omega]
      using startTrace) stopped reached
  refine ⟨complete, ?_⟩
  have dichotomy := realizingDecision_runUntil players owner follows event owned
    execution.application.config ready action entry message authored seen remaining 0 start
      (by simpa only [Nat.zero_add] using startTrace) member configEq solePacket realized
      stopped (by simpa only [ReactiveApplication.runUntilHorizon,
        show horizon - start.environmentRecall.length = remaining by omega] using reached)
  rcases dichotomy with unchanged | actual
  · rw [unchanged] at complete
    exact (ready.1 complete).elim
  · exact actual

end Vegas
