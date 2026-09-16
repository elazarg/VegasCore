/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ServiceTermination
import Interaction.MessageApplicationPending
import Interaction.MessageApplicationSubmission
import Interaction.MessageApplicationAuthorship
import Interaction.MessagePoolCounters
import Vegas.Pending.PolicyFreshness

/-! # Protection at reserved service inclusion -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
variable {Δ : VCtx Player L}

/-- At every residual reaction-round cursor of the real service plan, the
environment callback is exactly the supplied wire policy. In particular it is
not an expiry callback, regardless of earlier phase advancement. -/
theorem serviceEnvironment_reactionRound_wire
    (runtime : GraphRuntime Player L Δ)
    (before suffix : List (ServiceInstruction Player)) (roster : List Player)
    (completed remaining : Nat) (wire : runtime.application.WirePolicy)
    (history : List runtime.application.EnvironmentEntry)
    (view : runtime.application.EnvironmentObservation)
    (cursor : history.length =
      ((before ++ (List.replicate completed (reactionRound roster)).flatten).filterMap
        ServiceInstruction.environmentSlot).length) :
    runtime.serviceEnvironment
      (before ++ (List.replicate completed (reactionRound roster)).flatten ++
        (List.replicate (remaining + 1) (reactionRound roster)).flatten ++ suffix)
      wire history view = runtime.application.wireEnvironment wire history view := by
  rw [List.replicate_succ, List.flatten_cons]
  simp only [reactionRound, List.append_assoc]
  simpa only [reactionRound, List.append_assoc, List.cons_append] using
    runtime.serviceEnvironment_at
    (before ++ (List.replicate completed (reactionRound roster)).flatten)
    (roster.map ServiceInstruction.player ++
      (List.replicate remaining (reactionRound roster)).flatten ++ suffix)
    .wire wire history view rfl cursor

/-- Commands selected in a real reaction wire slot cannot be application
commands, hence cannot tick or expire a graph phase. -/
theorem serviceEnvironment_reactionRound_not_application
    (runtime : GraphRuntime Player L Δ)
    (before suffix : List (ServiceInstruction Player)) (roster : List Player)
    (completed remaining : Nat) (wire : runtime.application.WirePolicy)
    (history : List runtime.application.EnvironmentEntry)
    (view : runtime.application.EnvironmentObservation)
    (cursor : history.length =
      ((before ++ (List.replicate completed (reactionRound roster)).flatten).filterMap
        ServiceInstruction.environmentSlot).length)
    (command : runtime.application.EnvironmentPolicyCommand)
    (supported : command ∈ (runtime.serviceEnvironment
      (before ++ (List.replicate completed (reactionRound roster)).flatten ++
        (List.replicate (remaining + 1) (reactionRound roster)).flatten ++ suffix)
      wire history view).support) :
    ∀ applicationCommand, command ≠ .application applicationCommand := by
  rw [runtime.serviceEnvironment_reactionRound_wire before suffix roster completed remaining
    wire history view cursor] at supported
  unfold MessageApplication.wireEnvironment at supported
  rw [FinDist.support_map] at supported
  obtain ⟨wireCommand, _, rfl⟩ := supported
  cases wireCommand <;> simp [WireCommand.toEnvironmentCommand]

private theorem handle_clock (runtime : GraphRuntime Player L Δ)
    (state next : State Player L Δ) (message : Message Player runtime.application.Payload)
    (accepted : runtime.handle state message = some next) :
    next.publicView.clock = state.publicView.clock := by
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases message with
      | mk id payload =>
          cases graph with
          | ret => simp [GraphRuntime.handle] at accepted
          | sample => simp [GraphRuntime.handle] at accepted
          | bind name owner fresh tail =>
              cases payload <;> simp only [GraphRuntime.handle] at accepted
              · split_ifs at accepted
                cases accepted
                rfl
              all_goals contradiction
          | resolve output owner binding fresh source checks tail =>
              cases payload with
              | commitment | malformed => simp [GraphRuntime.handle] at accepted
              | opening site candidate raw =>
                  simp only [GraphRuntime.handle] at accepted
                  split_ifs at accepted
                  cases typed : raw.as? _ with
                  | none => rw [typed] at accepted; contradiction
                  | some encoded => rw [typed] at accepted; cases accepted; rfl
              | withhold site =>
                  simp only [GraphRuntime.handle] at accepted
                  split_ifs at accepted
                  cases accepted
                  rfl

private theorem includePending_clock (runtime : GraphRuntime Player L Δ)
    (state : runtime.application.State) (id : MessageId Player) :
    (runtime.application.includePending state id).application.publicView.clock =
      state.application.publicView.clock := by
  cases lookup : state.pool.lookup id with
  | none => rw [runtime.application.includePending_missing state id lookup]
  | some message =>
      cases accepted : runtime.handle state.application message with
      | none => rw [runtime.application.includePending_reject state id message lookup accepted]
      | some next =>
          rw [runtime.application.includePending_accept state id message next lookup accepted]
          exact runtime.handle_clock state.application next message accepted

private theorem playerStep_clock (runtime : GraphRuntime Player L Δ)
    (who : Player) (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.PlayerCommand)
    (supported : next ∈ (runtime.application.playerStep who execution command).support) :
    next.native.application.publicView.clock =
      execution.native.application.publicView.clock := by
  have nativeMem : next.native ∈
      ((runtime.application.playerStep who execution command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  rw [runtime.application.playerStep_native] at nativeMem
  cases command with
  | privateCommand privateCommand =>
      simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at nativeMem
      rw [nativeMem]
      cases execution.native.application
      cases privateCommand <;> rfl
  | submit payload | replay id | wait =>
      simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at nativeMem
      rw [nativeMem]

private theorem environmentWireStep_clock (runtime : GraphRuntime Player L Δ)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.EnvironmentPolicyCommand)
    (notApplication : ∀ applicationCommand, command ≠ .application applicationCommand)
    (supported : next ∈
      (runtime.application.environmentPolicyStep execution command).support) :
    next.native.application.publicView.clock =
      execution.native.application.publicView.clock := by
  have nativeMem : next.native ∈
      ((runtime.application.environmentPolicyStep execution command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  rw [runtime.application.environmentStep_native] at nativeMem
  cases command with
  | deliver observer id =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at nativeMem
      rw [nativeMem]
  | «include» id =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at nativeMem
      rw [nativeMem]
      exact runtime.includePending_clock execution.native id
  | application applicationCommand => exact (notApplication applicationCommand rfl).elim
  | wait =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        FinDist.mem_support_pure] at nativeMem
      rw [nativeMem]

private theorem runPolicies_players_clock (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy) (roster : List Player)
    (execution next : runtime.application.PolicyExecution)
    (supported : next ∈ (runtime.application.runPolicies players environment
      (roster.map (MessageApplication.Invocation.player)) execution).support) :
    next.native.application.publicView.clock =
      execution.native.application.publicView.clock := by
  induction roster generalizing execution with
  | nil =>
      simp only [List.map_nil, MessageApplication.runPolicies,
        FinDist.mem_support_pure] at supported
      subst next
      rfl
  | cons who rest ih =>
      simp only [List.map_cons, MessageApplication.runPolicies,
        FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨middle, first, last⟩ := supported
      simp only [MessageApplication.invoke, FinDist.support_bind,
        Set.mem_iUnion] at first
      obtain ⟨command, _, step⟩ := first
      exact (ih middle last).trans (runtime.playerStep_clock who execution middle command step)

/-- A complete reaction round in the actual residual service plan consumes its
wire slot and all roster reactions without changing the graph clock. Thus the
round cannot perform expiry, although a wire inclusion may advance the phase. -/
theorem runPolicies_service_reactionRound_clock
    (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (before suffix : List (ServiceInstruction Player)) (roster : List Player)
    (completed remaining : Nat) (wire : runtime.application.WirePolicy)
    (execution next : runtime.application.PolicyExecution)
    (cursor : execution.environmentHistory.length =
      ((before ++ (List.replicate completed (reactionRound roster)).flatten).filterMap
        ServiceInstruction.environmentSlot).length)
    (supported : next ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment
        (before ++ (List.replicate completed (reactionRound roster)).flatten ++
          (List.replicate (remaining + 1) (reactionRound roster)).flatten ++ suffix) wire)
      ((reactionRound roster).map ServiceInstruction.invocation) execution).support) :
    next.native.application.publicView.clock =
      execution.native.application.publicView.clock := by
  simp only [reactionRound, List.map_cons, List.map_map,
    ServiceInstruction.invocation, MessageApplication.runPolicies,
    FinDist.support_bind, Set.mem_iUnion] at supported
  obtain ⟨middle, first, last⟩ := supported
  simp only [MessageApplication.invoke, FinDist.support_bind,
    Set.mem_iUnion] at first
  obtain ⟨command, commandMem, stepMem⟩ := first
  have noApplication := runtime.serviceEnvironment_reactionRound_not_application
    before suffix roster completed remaining wire execution.environmentHistory
    (MessageApplication.State.environmentView runtime.application execution.native)
    cursor command commandMem
  have firstClock := runtime.environmentWireStep_clock execution middle command
    noApplication stepMem
  have lastClock := runtime.runPolicies_players_clock players
    (runtime.serviceEnvironment
      (before ++ (List.replicate completed (reactionRound roster)).flatten ++
        (List.replicate (remaining + 1) (reactionRound roster)).flatten ++ suffix) wire)
    roster middle next last
  exact lastClock.trans firstClock

/-- The entire replicated reaction prefix of the real service plan preserves
the graph clock. No reaction wire or player opportunity can consume timeout
budget before the designated expiry block. -/
theorem runPolicies_service_reactions_clock
    (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (before suffix : List (ServiceInstruction Player)) (roster : List Player)
    (rounds : Nat) (wire : runtime.application.WirePolicy)
    (execution next : runtime.application.PolicyExecution)
    (cursor : execution.environmentHistory.length =
      (before.filterMap ServiceInstruction.environmentSlot).length)
    (supported : next ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment
        (before ++ (List.replicate rounds (reactionRound roster)).flatten ++ suffix) wire)
      (((List.replicate rounds (reactionRound roster)).flatten).map
        ServiceInstruction.invocation) execution).support) :
    next.native.application.publicView.clock =
      execution.native.application.publicView.clock := by
  induction rounds generalizing before execution with
  | zero =>
      simp only [List.replicate_zero, List.flatten_nil, List.map_nil,
        MessageApplication.runPolicies, FinDist.mem_support_pure] at supported
      subst next
      rfl
  | succ rounds ih =>
      simp only [List.replicate_succ, List.flatten_cons, List.map_append,
        runtime.application.runPolicies_append] at supported
      simp only [FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨middle, first, last⟩ := supported
      have firstClock := runtime.runPolicies_service_reactionRound_clock players
        before suffix roster 0 rounds wire execution middle (by simpa using cursor) (by
          simpa [Nat.add_comm, List.replicate_succ, List.append_assoc] using first)
      have middleCursor : middle.environmentHistory.length =
          ((before ++ reactionRound roster).filterMap
            ServiceInstruction.environmentSlot).length := by
        have advanced := runtime.runPolicies_service_cursor players
          (runtime.serviceEnvironment
            (before ++ reactionRound roster ++
              (List.replicate rounds (reactionRound roster)).flatten ++ suffix) wire)
          (reactionRound roster) execution middle (by
            simpa [List.append_assoc] using first)
        simp [cursor, reactionRound] at advanced ⊢
        omega
      have lastClock := ih (before ++ reactionRound roster) middle middleCursor (by
        simpa [List.append_assoc] using last)
      exact lastClock.trans firstClock

/-- The reserved selector chooses the exact newest pending envelope. -/
theorem latestSubmissionCommand_of_pending_latest
    (runtime : GraphRuntime Player L Δ) (who : Player) (serial : Nat)
    (view : runtime.application.EnvironmentObservation)
    (nextSerial : view.pool.nextSerial who = serial + 1)
    (pending : ∃ message, view.pool.lookup (who, serial) = some message) :
    runtime.application.latestSubmissionCommand who view = .include (who, serial) := by
  rcases pending with ⟨message, pending⟩
  simp only [MessageApplication.latestSubmissionCommand, nextSerial]
  simp [pending]

/-- At the exact service cursor, a still-pending newest submission makes the
real service environment request its inclusion. -/
theorem serviceEnvironment_includeLatest_pending
    (runtime : GraphRuntime Player L Δ)
    (before suffix : List (ServiceInstruction Player)) (who : Player) (serial : Nat)
    (wire : runtime.application.WirePolicy)
    (history : List runtime.application.EnvironmentEntry)
    (view : runtime.application.EnvironmentObservation)
    (cursor : history.length =
      (before.filterMap ServiceInstruction.environmentSlot).length)
    (nextSerial : view.pool.nextSerial who = serial + 1)
    (pending : ∃ message, view.pool.lookup (who, serial) = some message) :
    runtime.serviceEnvironment (before ++ .includeLatest who :: suffix) wire history view =
      FinDist.pure (.include (who, serial)) := by
  have law := runtime.serviceEnvironment_at before suffix (.includeLatest who) wire
    history view (by simp [ServiceInstruction.environmentSlot]) cursor
  have selected := runtime.latestSubmissionCommand_of_pending_latest who serial view
    nextSerial pending
  simpa [ServiceInstruction.environmentSlot, selected] using law

/-- Consequently, the shared runner executes `includePending` on that exact
identifier; application acceptance or rejection remains the handler's result. -/
theorem runPolicies_includeLatest_pending
    (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (before suffix : List (ServiceInstruction Player)) (who : Player) (serial : Nat)
    (wire : runtime.application.WirePolicy)
    (execution next : runtime.application.PolicyExecution)
    (cursor : execution.environmentHistory.length =
      (before.filterMap ServiceInstruction.environmentSlot).length)
    (nextSerial : execution.native.pool.nextSerial who = serial + 1)
    (pending : ∃ message, execution.native.pool.lookup (who, serial) = some message)
    (supported : next ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment (before ++ .includeLatest who :: suffix) wire)
      [.environment] execution).support) :
    next.native = runtime.application.includePending execution.native (who, serial) := by
  simp only [MessageApplication.runPolicies, FinDist.support_bind,
    Set.mem_iUnion] at supported
  obtain ⟨middle, hmiddle, hnext⟩ := supported
  simp only [FinDist.mem_support_pure] at hnext
  subst next
  simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
  obtain ⟨command, hcommand, hstep⟩ := hmiddle
  have selected := runtime.serviceEnvironment_includeLatest_pending before suffix who serial
    wire execution.environmentHistory
    (MessageApplication.State.environmentView runtime.application execution.native)
    cursor nextSerial pending
  rw [selected] at hcommand
  simp only [FinDist.mem_support_pure] at hcommand
  subst command
  simp only [MessageApplication.environmentPolicyStep,
    MessageApplication.advance, MessageApplication.EnvironmentPolicyCommand.toAction,
    MessageApplication.step, FinDist.pure_bind, FinDist.mem_support_pure] at hstep
  exact congrArg MessageInterface.PolicyExecution.native hstep

/-- Across arbitrary wire commands and authenticated player reactions, an
authored valid packet remains pending at its phase or that phase has already
completed. The only semantic premise is that including the protected packet
while its phase is current is accepted and advances the application. -/
theorem runPolicies_pending_or_phase_advanced
    (runtime : GraphRuntime Player L Δ) (phase : Nat) (who : Player)
    (payload : runtime.application.Payload)
    (valid : State Player L Δ → Prop)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (initialBridge : runtime.application.PendingOrResolved
      (fun state => valid state ∧ state.phase = phase) (fun state => phase < state.phase)
      who payload execution.native)
    (validPrivate : ∀ application actor command, valid application →
      valid (runtime.privateStep application actor command))
    (validTick : ∀ application after, valid application →
      after ∈ (runtime.tick application).support → valid after)
    (accepts : ∀ application serial, valid application → application.phase = phase →
      ∃ after, runtime.handle application
        ({ id := (who, serial), payload } : Message Player runtime.application.Payload) =
          some after ∧ phase < after.phase)
    (supported : next ∈ (runtime.application.runPolicies players environment
      schedule execution).support) :
    runtime.application.PendingOrResolved
      (fun state => valid state ∧ state.phase = phase) (fun state => phase < state.phase)
      who payload next.native := by
  obtain ⟨actions, _trace, native⟩ :=
    runtime.application.runPolicies_native_support players environment schedule
      execution next supported
  apply runtime.application.run_pendingOrResolved
    (fun state => valid state ∧ state.phase = phase) (fun state => phase < state.phase)
    who payload
  · intro application actor command done
    change phase < (runtime.privateStep application actor command).phase
    rw [runtime.privateStep_phase]
    exact done
  · intro application actor command ready
    left
    refine ⟨validPrivate application actor command ready.1, ?_⟩
    change (runtime.privateStep application actor command).phase = phase
    rw [runtime.privateStep_phase]
    exact ready.2
  · intro application message after done accepted
    have step := runtime.handle_phase application after message accepted
    omega
  · intro application message after ready accepted
    right
    have step := runtime.handle_phase application after message accepted
    omega
  · intro application command after done happened
    have monotone := runtime.tick_phase_mono application after happened
    omega
  · intro application command after ready happened
    have monotone := runtime.tick_phase_mono application after happened
    rcases Nat.eq_or_lt_of_le monotone with same | later
    · left
      exact ⟨validTick application after ready.1 happened, by omega⟩
    · right; omega
  · intro application serial ready
    exact accepts application serial ready.1 ready.2
  · exact initialBridge
  · exact native

/-- The exact allocated envelope, rather than merely some authored envelope
with the same payload, survives until the current phase advances. -/
theorem runPolicies_exact_pending_or_phase_advanced
    (runtime : GraphRuntime Player L Δ) (phase : Nat) (who : Player) (serial : Nat)
    (payload : runtime.application.Payload)
    (valid : State Player L Δ → Prop)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (initialValid : valid execution.native.application)
    (atPhase : execution.native.application.phase = phase)
    (pending : ({ id := (who, serial), payload } :
      Message Player runtime.application.Payload) ∈ execution.native.pool.pending)
    (validPrivate : ∀ application actor command, valid application →
      valid (runtime.privateStep application actor command))
    (validTick : ∀ application after, valid application →
      after ∈ (runtime.tick application).support → valid after)
    (accepts : ∀ application allocated, valid application →
      application.phase = phase →
      ∃ after, runtime.handle application
        ({ id := (who, allocated), payload } : Message Player runtime.application.Payload) =
          some after ∧ phase < after.phase)
    (supported : next ∈ (runtime.application.runPolicies players environment
      schedule execution).support) :
    phase < next.native.application.phase ∨
      (next.native.application.phase = phase ∧
        ({ id := (who, serial), payload } : Message Player runtime.application.Payload) ∈
          next.native.pool.pending) := by
  obtain ⟨actions, _trace, native⟩ :=
    runtime.application.runPolicies_native_support players environment schedule
      execution next supported
  have bridge := runtime.application.run_exactPendingOrResolved
    (fun state => valid state ∧ state.phase = phase) (fun state => phase < state.phase)
    who serial payload
    (fun application actor command done => by
      change phase < (runtime.privateStep application actor command).phase
      rw [runtime.privateStep_phase]; exact done)
    (fun application actor command ready => Or.inl
      ⟨validPrivate application actor command ready.1, by
        change (runtime.privateStep application actor command).phase = phase
        rw [runtime.privateStep_phase]; exact ready.2⟩)
    (fun application message after done accepted => by
      have step := runtime.handle_phase application after message accepted
      omega)
    (fun application message after ready accepted => Or.inr (by
      have step := runtime.handle_phase application after message accepted
      omega))
    (fun application command after done happened => by
      have monotone := runtime.tick_phase_mono application after happened
      omega)
    (fun application command after ready happened => by
      have monotone := runtime.tick_phase_mono application after happened
      rcases Nat.eq_or_lt_of_le monotone with same | later
      · exact Or.inl ⟨validTick application after ready.1 happened, by omega⟩
      · exact Or.inr (by omega))
    (fun application allocated ready => accepts application allocated ready.1 ready.2)
    execution.native next.native actions
    (Or.inr ⟨⟨initialValid, atPhase⟩, pending⟩) native
  rcases bridge with advanced | ⟨⟨_, same⟩, remains⟩
  · exact Or.inl advanced
  · exact Or.inr ⟨same, remains⟩

/-- A concrete authored packet that starts pending at its current phase cannot
be stranded by an arbitrary reaction prefix: it is still pending afterwards,
or some inclusion/progress action has completed that phase. -/
theorem runPolicies_valid_pending_or_advanced
    (runtime : GraphRuntime Player L Δ) (phase : Nat) (who : Player)
    (payload : runtime.application.Payload)
    (valid : State Player L Δ → Prop)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (initialValid : valid execution.native.application)
    (atPhase : execution.native.application.phase = phase)
    (pending : runtime.application.AuthoredPending who payload execution.native)
    (validPrivate : ∀ application actor command, valid application →
      valid (runtime.privateStep application actor command))
    (validTick : ∀ application after, valid application →
      after ∈ (runtime.tick application).support → valid after)
    (accepts : ∀ application serial, valid application → application.phase = phase →
      ∃ after, runtime.handle application
        ({ id := (who, serial), payload } : Message Player runtime.application.Payload) =
          some after ∧ phase < after.phase)
    (supported : next ∈ (runtime.application.runPolicies players environment
      schedule execution).support) :
    phase < next.native.application.phase ∨
      (next.native.application.phase = phase ∧
        runtime.application.AuthoredPending who payload next.native) := by
  have bridge := runtime.runPolicies_pending_or_phase_advanced phase who payload valid players
    environment schedule execution next (Or.inr ⟨⟨initialValid, atPhase⟩, pending⟩)
    validPrivate validTick accepts supported
  rcases bridge with advanced | ⟨⟨_, same⟩, remains⟩
  · exact Or.inl advanced
  · exact Or.inr ⟨same, remains⟩

/-- A current binding commitment from its authenticated owner remains authored
and pending through arbitrary native reactions, unless that binding phase has
already advanced. Binding acceptance does not inspect candidate meaning. -/
theorem runPolicies_bind_commitment_pending_or_advanced
    (runtime : GraphRuntime Player L Δ) {Γ : VCtx Player L}
    {name : VarId} {owner : Player} {payloadTy : L.Ty} {fresh}
    {tail : Graph Player L ((name, .sealed owner
      (IExpr.ResultTypes.result payloadTy)) :: Γ) Δ}
    (base : Nat) (handle : Handle Player) (owned : handle.1 = owner)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows
      (.bind name owner fresh tail) base)
    (atPhase : execution.native.application.phase = base)
    (pending : runtime.application.AuthoredPending owner
      (.commitment base handle) execution.native)
    (supported : next ∈ (runtime.application.runPolicies players environment
      schedule execution).support) :
    base < next.native.application.phase ∨
      (next.native.application.phase = base ∧
        runtime.application.AuthoredPending owner (.commitment base handle) next.native) := by
  apply runtime.runPolicies_valid_pending_or_advanced base owner
    (.commitment base handle)
    (fun state => state.Follows (.bind name owner fresh tail) base)
    players environment schedule execution next follows atPhase pending
  · intro application actor command valid
    exact runtime.privateStep_follows _ _ _ actor command valid
  · intro application after valid ticked
    exact runtime.tick_follows _ _ application after valid ticked
  · intro application serial valid current
    obtain ⟨ideal, values, bindings, candidates, clock, enteredAt, stateEq⟩ :=
      State.follows_at_base (.bind name owner fresh tail) base application valid
        (by simpa using current)
    refine ⟨advanceBind tail ideal values bindings candidates base clock handle, ?_, ?_⟩
    · rw [stateEq]
      simp [GraphRuntime.handle, Message.sender, owned]
    · simp [State.phase, advanceBind]
  · exact supported

/-- Exact-identifier strengthening of bind commitment protection. This is the
form consumed by newest-message selection after the reaction prefix. -/
theorem runPolicies_bind_commitment_exact_pending_or_advanced
    (runtime : GraphRuntime Player L Δ) {Γ : VCtx Player L}
    {name : VarId} {owner : Player} {payloadTy : L.Ty} {fresh}
    {tail : Graph Player L ((name, .sealed owner
      (IExpr.ResultTypes.result payloadTy)) :: Γ) Δ}
    (base serial : Nat) (handle : Handle Player) (owned : handle.1 = owner)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows
      (.bind name owner fresh tail) base)
    (atPhase : execution.native.application.phase = base)
    (pending : ({ id := (owner, serial), payload := .commitment base handle } :
      Message Player runtime.application.Payload) ∈ execution.native.pool.pending)
    (supported : next ∈ (runtime.application.runPolicies players environment
      schedule execution).support) :
    base < next.native.application.phase ∨
      (next.native.application.phase = base ∧
        ({ id := (owner, serial), payload := .commitment base handle } :
          Message Player runtime.application.Payload) ∈ next.native.pool.pending) := by
  apply runtime.runPolicies_exact_pending_or_phase_advanced base owner serial
    (.commitment base handle)
    (fun state => state.Follows (.bind name owner fresh tail) base)
    players environment schedule execution next follows atPhase pending
  · intro application actor command valid
    exact runtime.privateStep_follows _ _ _ actor command valid
  · intro application after valid ticked
    exact runtime.tick_follows _ _ application after valid ticked
  · intro application allocated valid current
    obtain ⟨ideal, values, bindings, candidates, clock, enteredAt, stateEq⟩ :=
      State.follows_at_base (.bind name owner fresh tail) base application valid
        (by simpa using current)
    refine ⟨advanceBind tail ideal values bindings candidates base clock handle, ?_, ?_⟩
    · rw [stateEq]
      simp [GraphRuntime.handle, Message.sender, owned]
    · simp [State.phase, advanceBind]
  · exact supported

/-- After a compiled owner has submitted at a site, its sender counter remains
fixed for as long as that site remains current. Other principals are
authenticated under their own identifiers, and environment commands allocate
no sender identifiers. -/
theorem runPolicies_compiled_submitted_counter
    (runtime : GraphRuntime Player L Δ) {Γ : VCtx Player L}
    (graph : Graph Player L Γ Δ) (who : Player) (policy : Graph.BehavioralPolicy who graph)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerCompiled : players who = runtime.compilePlayerPolicy graph who policy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution) (site serial : Nat)
    (atSite : execution.native.application.phase = site)
    (submitted : submittedAt (execution.principalHistory who) site = true)
    (counter : execution.native.pool.nextSerial who = serial)
    (supported : next ∈ (runtime.application.runPolicies players environment
      schedule execution).support) :
    site < next.native.application.phase ∨
      (next.native.application.phase = site ∧
        submittedAt (next.principalHistory who) site = true ∧
        next.native.pool.nextSerial who = serial) := by
  let invariant : runtime.application.PolicyExecution → Prop := fun current =>
    site < current.native.application.phase ∨
      (current.native.application.phase = site ∧
        submittedAt (current.principalHistory who) site = true ∧
        current.native.pool.nextSerial who = serial)
  refine runtime.application.runPolicies_execution_invariant invariant players environment
    ?_ ?_ schedule execution next (Or.inr ⟨atSite, submitted, counter⟩) supported
  · intro current actor command after currentInv commandMem stepMem
    have phaseMono := runtime.playerStep_phase_mono actor current after command stepMem
    rcases currentInv with done | ⟨currentPhase, currentSubmitted, currentCounter⟩
    · exact Or.inl (done.trans_le phaseMono)
    · by_cases same : actor = who
      · subst actor
        rw [ownerCompiled] at commandMem
        change command ∈ (runtime.compileAt who graph graph policy 0
          (current.principalHistory who)
          (MessageApplication.State.observe runtime.application current.native who)).support
          at commandMem
        have waits := runtime.compileAt_wait_of_submitted who graph graph policy 0
          (current.principalHistory who)
          (MessageApplication.State.observe runtime.application current.native who)
          (by
            change submittedAt (current.principalHistory who)
              current.native.application.phase = true
            rwa [currentPhase])
        rw [waits] at commandMem
        simp only [FinDist.mem_support_pure] at commandMem
        subst command
        rw [runtime.application.playerStep_wait who current] at stepMem
        simp only [FinDist.mem_support_pure] at stepMem
        subst after
        exact Or.inr ⟨currentPhase, by simpa [submittedAt] using currentSubmitted,
          currentCounter⟩
      · have history := runtime.application.playerStep_other_history actor who
          (Ne.symm same) current command after stepMem
        by_cases advanced : site < after.native.application.phase
        · exact Or.inl advanced
        have phaseEq : after.native.application.phase = site := by omega
        have nativeMem : after.native ∈
            ((runtime.application.playerStep actor current command).map
              MessageInterface.PolicyExecution.native).support := by
          rw [FinDist.support_map]
          exact ⟨after, stepMem, rfl⟩
        rw [runtime.application.playerStep_native] at nativeMem
        cases command <;>
          simp only [MessageApplication.PlayerCommand.toAction,
            MessageApplication.step, FinDist.mem_support_pure] at nativeMem
        all_goals
          right
          refine ⟨phaseEq, by simpa [history] using currentSubmitted, ?_⟩
        · simpa [nativeMem] using currentCounter
        · simpa [nativeMem, MessagePool.submit, Ne.symm same] using currentCounter
        · simpa [nativeMem, MessagePool.replay_nextSerial] using currentCounter
        · simpa [nativeMem] using currentCounter
  · intro current command after currentInv _commandMem stepMem
    have phaseMono := runtime.environmentPolicyStep_phase_mono current after command stepMem
    rcases currentInv with done | ⟨currentPhase, currentSubmitted, currentCounter⟩
    · exact Or.inl (done.trans_le phaseMono)
    · have history := runtime.application.environmentStep_principalHistory
        current command after stepMem
      by_cases advanced : site < after.native.application.phase
      · exact Or.inl advanced
      · right
        have phaseEq : after.native.application.phase = site := by omega
        refine ⟨phaseEq, by simpa [history] using currentSubmitted, ?_⟩
        have nativeMem : after.native ∈
            ((runtime.application.environmentPolicyStep current command).map
              MessageInterface.PolicyExecution.native).support := by
          rw [FinDist.support_map]
          exact ⟨after, stepMem, rfl⟩
        rw [runtime.application.environmentStep_native] at nativeMem
        cases command <;>
          simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
            MessageApplication.step, FinDist.mem_support_pure] at nativeMem
        · simpa [nativeMem] using currentCounter
        · simpa [nativeMem, MessagePool.include_preserves_nextSerial] using currentCounter
        · rw [FinDist.support_map] at nativeMem
          obtain ⟨application, _, nativeEq⟩ := nativeMem
          rw [← nativeEq]
          exact currentCounter
        · simpa [nativeMem] using currentCounter

/-- A current, latest bind commitment is protected through arbitrary reactions
up to the phase-progress boundary, and the real reserved service cursor then
advances the bind whenever reactions have not already advanced it. The earlier
advance may itself be expiry; this theorem asserts phase progress, not chosen-
value success. -/
theorem runPolicies_bind_reactions_then_reserved_include_advances
    (runtime : GraphRuntime Player L Δ) {Γ origin : VCtx Player L}
    {name : VarId} {owner : Player} {payloadTy : L.Ty} {fresh}
    {tail : Graph Player L ((name, .sealed owner
      (IExpr.ResultTypes.result payloadTy)) :: Γ) Δ}
    (whole : Graph Player L origin Δ)
    (policy : Graph.BehavioralPolicy owner whole)
    (base serial : Nat) (handle : Handle Player) (owned : handle.1 = owner)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy whole owner policy)
    (reactionEnvironment : runtime.application.EnvironmentPolicy)
    (reactions : List (@MessageApplication.Invocation Player))
    (before suffix : List (ServiceInstruction Player))
    (wire : runtime.application.WirePolicy)
    (execution reacted included : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows
      (.bind name owner fresh tail) base)
    (atPhase : execution.native.application.phase = base)
    (submitted : submittedAt (execution.principalHistory owner) base = true)
    (nextSerial : execution.native.pool.nextSerial owner = serial + 1)
    (pending : ({ id := (owner, serial), payload := .commitment base handle } :
      Message Player runtime.application.Payload) ∈ execution.native.pool.pending)
    (authorship : runtime.application.Authorship execution)
    (reactionSupported : reacted ∈ (runtime.application.runPolicies players
      reactionEnvironment reactions execution).support)
    (cursor : reacted.environmentHistory.length =
      (before.filterMap ServiceInstruction.environmentSlot).length)
    (includeSupported : included ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment (before ++ .includeLatest owner :: suffix) wire)
      [.environment] reacted).support) :
    base < included.native.application.phase := by
  have protection := runtime.runPolicies_bind_commitment_exact_pending_or_advanced
    base serial handle owned players reactionEnvironment reactions execution reacted
    follows atPhase pending reactionSupported
  rcases protection with advanced | ⟨reactedPhase, reactedPending⟩
  · have monotone := runtime.runPolicies_phase_mono players
      (runtime.serviceEnvironment (before ++ .includeLatest owner :: suffix) wire)
      [.environment] reacted included includeSupported
    exact advanced.trans_le monotone
  · have counterProtected := runtime.runPolicies_compiled_submitted_counter
      whole owner policy players ownerCompiled reactionEnvironment reactions
      execution reacted base (serial + 1) atPhase submitted nextSerial reactionSupported
    have reactedCounter : reacted.native.pool.nextSerial owner = serial + 1 := by
      rcases counterProtected with later | ⟨_, _, same⟩
      · omega
      · exact same
    have reactedAuthorship := runtime.application.runPolicies_authorship players
      reactionEnvironment reactions execution reacted authorship reactionSupported
    have lookup := MessageApplication.Authorship.lookup_eq_of_mem_pending
      runtime.application reacted reactedAuthorship
      ({ id := (owner, serial), payload := .commitment base handle } :
        Message Player runtime.application.Payload) reactedPending
    have nativeEq := runtime.runPolicies_includeLatest_pending players before suffix owner
      serial wire reacted included cursor reactedCounter
      ⟨_, lookup⟩ includeSupported
    have reactedFollows := runtime.runPolicies_follows (.bind name owner fresh tail) base
      players reactionEnvironment reactions execution reacted follows reactionSupported
    obtain ⟨ideal, values, bindings, candidates, clock, enteredAt, stateEq⟩ :=
      State.follows_at_base (.bind name owner fresh tail) base
        reacted.native.application reactedFollows (by simpa using reactedPhase)
    let after := advanceBind tail ideal values bindings candidates base clock handle
    have accepted : runtime.handle reacted.native.application
        ({ id := (owner, serial), payload := .commitment base handle } :
          Message Player runtime.application.Payload) = some after := by
      rw [stateEq]
      simp [GraphRuntime.handle, Message.sender, owned, after]
    have includedState := runtime.application.includePending_accept reacted.native
      (owner, serial)
      ({ id := (owner, serial), payload := .commitment base handle } :
        Message Player runtime.application.Payload)
      after lookup accepted
    rw [nativeEq, includedState]
    simp [after, State.phase, advanceBind]

/-- For the actual pre-expiry service prefix of a bind, either wire/player
reactions accept some packet and advance while preserving the clock, or the
designated newest-message inclusion advances the still-current bind. Timeout
cannot account for the first alternative. -/
theorem runPolicies_bind_service_reactions_or_reserved_include
    (runtime : GraphRuntime Player L Δ) {Γ origin : VCtx Player L}
    {name : VarId} {owner : Player} {payloadTy : L.Ty} {fresh}
    {tail : Graph Player L ((name, .sealed owner
      (IExpr.ResultTypes.result payloadTy)) :: Γ) Δ}
    (whole : Graph Player L origin Δ) (policy : Graph.BehavioralPolicy owner whole)
    (base serial rounds : Nat) (handle : Handle Player) (owned : handle.1 = owner)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy whole owner policy)
    (before suffix : List (ServiceInstruction Player)) (roster : List Player)
    (wire : runtime.application.WirePolicy)
    (execution reacted included : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows
      (.bind name owner fresh tail) base)
    (atPhase : execution.native.application.phase = base)
    (submitted : submittedAt (execution.principalHistory owner) base = true)
    (nextSerial : execution.native.pool.nextSerial owner = serial + 1)
    (pending : ({ id := (owner, serial), payload := .commitment base handle } :
      Message Player runtime.application.Payload) ∈ execution.native.pool.pending)
    (authorship : runtime.application.Authorship execution)
    (cursor : execution.environmentHistory.length =
      (before.filterMap ServiceInstruction.environmentSlot).length)
    (reactionSupported : reacted ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment
        (before ++ (List.replicate rounds (reactionRound roster)).flatten ++
          .includeLatest owner :: suffix) wire)
      (((List.replicate rounds (reactionRound roster)).flatten).map
        ServiceInstruction.invocation) execution).support)
    (includeSupported : included ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment
        (before ++ (List.replicate rounds (reactionRound roster)).flatten ++
          .includeLatest owner :: suffix) wire)
      [.environment] reacted).support) :
    (base < reacted.native.application.phase ∧
      reacted.native.application.publicView.clock =
        execution.native.application.publicView.clock) ∨
      (reacted.native.application.phase = base ∧
        base < included.native.application.phase) := by
  let reactionBlock := (List.replicate rounds (reactionRound roster)).flatten
  let plan := before ++ reactionBlock ++ .includeLatest owner :: suffix
  have clockEq := runtime.runPolicies_service_reactions_clock players before
    (.includeLatest owner :: suffix) roster rounds wire execution reacted cursor (by
      simpa [reactionBlock, plan, List.append_assoc] using reactionSupported)
  have phaseMono := runtime.runPolicies_phase_mono players
    (runtime.serviceEnvironment plan wire) _ execution reacted (by
      simpa [plan, reactionBlock] using reactionSupported)
  by_cases advanced : base < reacted.native.application.phase
  · exact Or.inl ⟨advanced, clockEq⟩
  · have reactedPhase : reacted.native.application.phase = base := by omega
    have reactedCursor : reacted.environmentHistory.length =
        ((before ++ reactionBlock).filterMap
          ServiceInstruction.environmentSlot).length := by
      have cursorStep := runtime.runPolicies_service_cursor players
        (runtime.serviceEnvironment plan wire) reactionBlock execution reacted (by
          simpa [plan, reactionBlock] using reactionSupported)
      rw [cursor] at cursorStep
      simpa [List.filterMap_append] using cursorStep
    right
    refine ⟨reactedPhase, ?_⟩
    apply runtime.runPolicies_bind_reactions_then_reserved_include_advances
      whole policy base serial handle owned players ownerCompiled
      (runtime.serviceEnvironment plan wire)
      (reactionBlock.map ServiceInstruction.invocation)
      (before ++ reactionBlock) suffix wire execution reacted included
      follows atPhase submitted nextSerial pending authorship
    · simpa [plan, reactionBlock] using reactionSupported
    · exact reactedCursor
    · simpa [plan, reactionBlock, List.append_assoc] using includeSupported

end Vegas.GraphRuntime
