/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageServiceTermination
import Interaction.MessageApplicationPending
import Interaction.MessageApplicationSubmission
import Interaction.MessagePoolCounters
import Vegas.Graph.MessagePolicyFreshness

/-! # Protection at reserved service inclusion -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
variable {Δ : VCtx Player L}

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
    (_validHandler : ∀ application message after, valid application →
      runtime.handle application message = some after → valid after)
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
    (_validHandler : ∀ application message after, valid application →
      runtime.handle application message = some after → valid after)
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
    (validHandler : ∀ application message after, valid application →
      runtime.handle application message = some after → valid after)
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
    validPrivate validHandler validTick accepts supported
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
  · intro application message after valid accepted
    exact runtime.handle_follows _ _ application after message valid accepted
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
  · intro application message after valid accepted
    exact runtime.handle_follows _ _ application after message valid accepted
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

end Vegas.GraphRuntime
