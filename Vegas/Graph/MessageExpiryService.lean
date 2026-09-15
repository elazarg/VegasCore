/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageServiceCompletion

/-! # Gated expiry blocks in the concrete graph service -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

/-- At its exact cursor and phase, a reserved expiry invocation executes the
real application tick through the shared policy runner. -/
theorem runPolicies_expire_tick (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (before suffix : List (ServiceInstruction Player)) (phase : Nat)
    (wire : runtime.application.WirePolicy)
    (execution next : runtime.application.PolicyExecution)
    (cursor : execution.environmentHistory.length =
      (before.filterMap ServiceInstruction.environmentSlot).length)
    (atPhase : (MessageApplication.State.environmentView runtime.application
      execution.native).application.pc = phase)
    (supported : next ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment (before ++ .expire phase :: suffix) wire)
      [.environment] execution).support) :
    next.native.application ∈ (runtime.tick execution.native.application).support := by
  simp only [MessageApplication.runPolicies, FinDist.support_bind,
    Set.mem_iUnion] at supported
  obtain ⟨middle, hmiddle, hnext⟩ := supported
  simp only [FinDist.mem_support_pure] at hnext
  subst next
  simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
  obtain ⟨command, hcommand, hstep⟩ := hmiddle
  have environment := runtime.serviceEnvironment_at before suffix (.expire phase) wire
    execution.environmentHistory
    (MessageApplication.State.environmentView runtime.application execution.native)
    (by simp [ServiceInstruction.environmentSlot]) cursor
  have environment' : runtime.serviceEnvironment
      (before ++ .expire phase :: suffix) wire execution.environmentHistory
      (MessageApplication.State.environmentView runtime.application execution.native) =
      FinDist.pure (if (MessageApplication.State.environmentView runtime.application
        execution.native).application.pc = phase then
        .application .tick else .wait) := by
    simpa [ServiceInstruction.environmentSlot] using environment
  rw [environment', atPhase] at hcommand
  simp only [ite_true, FinDist.mem_support_pure] at hcommand
  subst command
  have hmapped : middle.native ∈
      ((runtime.application.environmentPolicyStep execution (.application .tick)).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨middle, hstep, rfl⟩
  rw [MessageApplication.environmentStep_native] at hmapped
  simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
    MessageApplication.step, FinDist.support_map, Set.mem_image] at hmapped
  obtain ⟨application, happened, equality⟩ := hmapped
  have applicationEq := congrArg (fun state => state.application) equality
  rw [← applicationEq]
  exact happened

/-- The single reserved expiry slot of a chance phase advances that exact
typed graph head. -/
theorem runPolicies_expire_sample_advances (runtime : GraphRuntime Player L Δ)
    {name : VarId} {payload : L.Ty} {fresh law}
    {tail : Graph Player L ((name, .pub payload) :: Γ) Δ}
    (players : Player → runtime.application.PlayerPolicy)
    (before suffix : List (ServiceInstruction Player)) (phase : Nat)
    (wire : runtime.application.WirePolicy)
    (execution next : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows
      (.sample name fresh law tail) phase)
    (cursor : execution.environmentHistory.length =
      (before.filterMap ServiceInstruction.environmentSlot).length)
    (atPhase : execution.native.application.publicView.pc = phase)
    (supported : next ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment (before ++ .expire phase :: suffix) wire)
      [.environment] execution).support) :
    next.native.application.publicView.pc = phase + 1 := by
  have environmentPhase : (MessageApplication.State.environmentView runtime.application
      execution.native).application.pc = phase := by
    simpa [MessageApplication.State.environmentView, GraphRuntime.application,
      MessageApplication.toMessageInterface] using atPhase
  have ticked := runtime.runPolicies_expire_tick players before suffix phase wire
    execution next cursor environmentPhase supported
  obtain ⟨ideal, values, bindings, candidates, clock, enteredAt, stateEq⟩ :=
    State.follows_at_base (.sample name fresh law tail) phase
      execution.native.application follows atPhase
  rw [stateEq] at ticked
  simp only [tick, FinDist.support_map, Set.mem_image] at ticked
  obtain ⟨value, _, nextEq⟩ := ticked
  rw [← nextEq]
  rfl

/-- At a sample's reserved slot, execution passes that nominal phase. If
earlier inclusions already advanced further, phase monotonicity suffices. -/
theorem runPolicies_sample_slot_advances (runtime : GraphRuntime Player L Δ)
    {name : VarId} {payload : L.Ty} {fresh law}
    {tail : Graph Player L ((name, .pub payload) :: Γ) Δ}
    (players : Player → runtime.application.PlayerPolicy)
    (before suffix : List (ServiceInstruction Player)) (phase : Nat)
    (wire : runtime.application.WirePolicy)
    (execution next : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows (.sample name fresh law tail) phase)
    (cursor : execution.environmentHistory.length =
      (before.filterMap ServiceInstruction.environmentSlot).length)
    (supported : next ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment (before ++ .expire phase :: suffix) wire)
      [.environment] execution).support) : phase < next.native.application.phase := by
  obtain ⟨length, phaseEq⟩ := State.follows_phase
    (.sample name fresh law tail) phase execution.native.application follows
  have lower : phase ≤ execution.native.application.phase := by
    simpa only [State.publicView_pc] using
      (show phase ≤ execution.native.application.publicView.pc by omega)
  rcases lower.eq_or_lt with current | passed
  · have advanced := runtime.runPolicies_expire_sample_advances players before suffix phase wire
      execution next follows cursor (by simpa only [State.publicView_pc] using current.symm)
      supported
    rw [State.publicView_pc] at advanced
    omega
  · exact passed.trans_le (runtime.runPolicies_phase_mono players
      (runtime.serviceEnvironment (before ++ .expire phase :: suffix) wire)
      [.environment] execution next supported)

private theorem runPolicies_expire_progress (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (before suffix : List (ServiceInstruction Player)) (phase : Nat)
    (wire : runtime.application.WirePolicy)
    (execution next : runtime.application.PolicyExecution)
    (cursor : execution.environmentHistory.length =
      (before.filterMap ServiceInstruction.environmentSlot).length)
    (ordered : execution.native.application.ClockOrdered)
    (atPhase : execution.native.application.phase = phase)
    (supported : next ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment (before ++ .expire phase :: suffix) wire)
      [.environment] execution).support) :
    next.native.application.ClockOrdered ∧
      next.native.application.ticksRemaining runtime ≤
        execution.native.application.ticksRemaining runtime - 1 ∧
      execution.native.application.phase ≤ next.native.application.phase ∧
      next.environmentHistory.length =
        ((before ++ [ServiceInstruction.expire phase]).filterMap
          ServiceInstruction.environmentSlot).length := by
  have ticked := runtime.runPolicies_expire_tick players before suffix phase wire
    execution next cursor (by
      change execution.native.application.publicView.pc = phase
      exact (State.publicView_pc _).trans atPhase) supported
  have progress := runtime.tick_progress execution.native.application
    next.native.application ordered ticked
  refine ⟨progress.1, progress.2,
    runtime.tick_phase_mono execution.native.application next.native.application ticked, ?_⟩
  have length := runtime.application.runPolicies_environmentHistory_length
    players _ [.environment] execution next supported
  simpa [cursor, ServiceInstruction.environmentSlot,
    MessageApplication.Invocation.isEnvironment] using length

/-- If a repeated reserved-expiry block ends at its starting phase, every
invocation really ticked that phase and consumed one unit of its tick budget. -/
theorem runPolicies_expire_budget (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (before suffix : List (ServiceInstruction Player)) (phase count : Nat)
    (wire : runtime.application.WirePolicy)
    (execution next : runtime.application.PolicyExecution)
    (cursor : execution.environmentHistory.length =
      (before.filterMap ServiceInstruction.environmentSlot).length)
    (ordered : execution.native.application.ClockOrdered)
    (startPhase : execution.native.application.phase = phase)
    (endPhase : next.native.application.phase = phase)
    (supported : next ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment
        (before ++ List.replicate count (.expire phase) ++ suffix) wire)
      ((List.replicate count (.expire phase)).map ServiceInstruction.invocation)
      execution).support) :
    next.native.application.ticksRemaining runtime ≤
      execution.native.application.ticksRemaining runtime - count := by
  induction count generalizing before execution with
  | zero =>
      simp only [List.replicate_zero, List.map_nil, MessageApplication.runPolicies,
        FinDist.mem_support_pure] at supported
      subst next
      omega
  | succ count ih =>
      let rest := List.replicate count (.expire phase) ++ suffix
      let environment := runtime.serviceEnvironment (before ++ .expire phase :: rest) wire
      have expanded : next ∈ (runtime.application.runPolicies players environment
          (.environment :: (List.replicate count (.expire phase)).map
            ServiceInstruction.invocation) execution).support := by
        simpa only [List.replicate_succ, List.cons_append, List.map_cons,
          ServiceInstruction.invocation, environment, rest, List.append_assoc] using supported
      simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion]
        at expanded
      obtain ⟨middle, first, later⟩ := expanded
      have firstRun : middle ∈ (runtime.application.runPolicies players environment
          [.environment] execution).support := by
        simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using first
      have progress := runPolicies_expire_progress runtime players before rest phase wire
        execution middle cursor ordered startPhase firstRun
      have late := runtime.runPolicies_phase_mono players environment _ middle next later
      have middlePhase : middle.native.application.phase = phase := by
        have early := progress.2.2.1
        omega
      have laterRun : next ∈ (runtime.application.runPolicies players
          (runtime.serviceEnvironment ((before ++ [.expire phase]) ++
            List.replicate count (.expire phase) ++ suffix) wire)
          ((List.replicate count (.expire phase)).map ServiceInstruction.invocation)
          middle).support := by
        simpa only [List.append_assoc, List.singleton_append, List.cons_append,
          List.nil_append, rest, environment] using later
      have bound : next.native.application.ticksRemaining runtime ≤
          middle.native.application.ticksRemaining runtime - count := by
        apply ih (before := before ++ [.expire phase]) (execution := middle)
        · exact progress.2.2.2
        · exact progress.1
        · exact middlePhase
        · exact laterRun
      have decrease := progress.2.1
      omega

/-- A full reserved expiry block passes any nonterminal graph head, regardless
of player traffic before that block and regardless of the retained wire policy. -/
theorem runPolicies_expire_advances (runtime : GraphRuntime Player L Δ)
    (graph : Graph Player L Γ Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (before suffix : List (ServiceInstruction Player)) (phase : Nat)
    (wire : runtime.application.WirePolicy)
    (execution next : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows graph phase)
    (ordered : execution.native.application.ClockOrdered)
    (nonterminal : remainingPhases graph ≠ 0)
    (cursor : execution.environmentHistory.length =
      (before.filterMap ServiceInstruction.environmentSlot).length)
    (supported : next ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment
        (before ++ List.replicate (max 1 (runtime.deadline phase)) (.expire phase) ++ suffix) wire)
      ((List.replicate (max 1 (runtime.deadline phase)) (.expire phase)).map
        ServiceInstruction.invocation) execution).support) :
    phase < next.native.application.publicView.pc := by
  have monotone := runtime.runPolicies_phase_mono players _ _ execution next supported
  have startBound := State.follows_phase graph phase execution.native.application follows
  have nextFollows := runtime.runPolicies_follows graph phase players _ _ execution next
    follows supported
  simp only [State.publicView_pc] at startBound ⊢
  by_contra notPassed
  have startPhase : execution.native.application.phase = phase := by omega
  have endPhase : next.native.application.phase = phase := by omega
  have budget := runtime.runPolicies_expire_budget players before suffix phase
    (max 1 (runtime.deadline phase)) wire execution next cursor ordered startPhase endPhase
    supported
  obtain ⟨ideal, values, bindings, candidates, clock, enteredAt, stateEq⟩ :=
    State.follows_at_base graph phase execution.native.application follows
      (by simpa using startPhase)
  obtain ⟨nextIdeal, nextValues, nextBindings, nextCandidates, nextClock, nextEnteredAt,
      nextEq⟩ := State.follows_at_base graph phase next.native.application nextFollows
        (by simpa using endPhase)
  rw [stateEq, nextEq] at budget
  cases graph <;>
    simp only [remainingPhases, State.ticksRemaining] at nonterminal budget <;> omega

end Vegas.GraphRuntime
