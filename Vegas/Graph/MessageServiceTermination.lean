/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageExpiryService

/-! # Whole-plan termination of concrete graph service -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

/-- Clock order is preserved by the actual shared policy runner, independently
of the commands selected by players and the environment. -/
theorem runPolicies_clockOrdered (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (ordered : execution.native.application.ClockOrdered)
    (supported : next ∈ (runtime.application.runPolicies players environment
      schedule execution).support) :
    next.native.application.ClockOrdered := by
  obtain ⟨actions, _trace, native⟩ :=
    runtime.application.runPolicies_native_support players environment schedule
      execution next supported
  exact (runtime.run_progress actions execution.native next.native ordered native).1

/-- Running a service-plan prefix advances its exact environment cursor while
preserving the typed graph suffix and clock order. -/
theorem runPolicies_service_prefix_invariants (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ Δ) (phase : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (segment : List (ServiceInstruction Player))
    (execution next : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows whole phase)
    (ordered : execution.native.application.ClockOrdered)
    (supported : next ∈ (runtime.application.runPolicies players environment
      (segment.map ServiceInstruction.invocation) execution).support) :
    next.native.application.Follows whole phase ∧
      next.native.application.ClockOrdered ∧
      next.environmentHistory.length = execution.environmentHistory.length +
        (segment.filterMap ServiceInstruction.environmentSlot).length := by
  exact ⟨runtime.runPolicies_follows whole phase players environment _ _ _ follows supported,
    runtime.runPolicies_clockOrdered players environment _ _ _ ordered supported,
    runtime.runPolicies_service_cursor players environment segment execution next supported⟩

/-- Every supported execution of the remaining concrete service plan reaches
the terminal graph boundary. The accumulated prefix is explicit so the real
environment-policy cursor and complete wire history are retained. -/
theorem servicePlan_terminates_from (runtime : GraphRuntime Player L Δ)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (before : List (ServiceInstruction Player)) (phase : Nat)
    (graph : Graph Player L Γ Δ)
    (execution next : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows graph phase)
    (ordered : execution.native.application.ClockOrdered)
    (cursor : execution.environmentHistory.length =
      (before.filterMap ServiceInstruction.environmentSlot).length)
    (supported : next ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment
        (before ++ runtime.servicePlan roster reactionRounds graph phase) wire)
      ((runtime.servicePlan roster reactionRounds graph phase).map
        ServiceInstruction.invocation) execution).support) :
    next.native.application.outcome?.isSome = true := by
  induction graph generalizing phase before with
  | ret payoffs =>
      simp only [servicePlan, List.map_nil, MessageApplication.runPolicies,
        FinDist.mem_support_pure] at supported
      subst next
      rcases follows with
        ⟨target, suffix, length, ideal, values, bindings, candidates, clock,
          enteredAt, walk, stateEq⟩
      cases walk
      rw [stateEq]
      simp [State.outcome?]
  | sample name fresh law tail ih =>
      simp only [servicePlan, List.map_cons, MessageApplication.runPolicies,
        FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨middle, first, rest⟩ := supported
      have firstRun : middle ∈ (runtime.application.runPolicies players
          (runtime.serviceEnvironment
            (before ++ .expire phase :: runtime.servicePlan roster reactionRounds tail
              (phase + 1)) wire)
          [.environment] execution).support := by
        simp only [MessageApplication.runPolicies, FinDist.support_bind,
          Set.mem_iUnion, FinDist.mem_support_pure]
        exact ⟨middle, first, rfl⟩
      obtain ⟨length, hlength⟩ := State.follows_phase
        (.sample name fresh law tail) phase execution.native.application follows
      have phaseLe : phase ≤ execution.native.application.publicView.pc := by omega
      have advanced : phase < middle.native.application.publicView.pc := by
        rcases phaseLe.eq_or_lt with atPhase | already
        · have exactAdvance := runtime.runPolicies_expire_sample_advances players before
            (runtime.servicePlan roster reactionRounds tail (phase + 1)) phase wire
            execution middle follows cursor atPhase.symm firstRun
          omega
        · have monotone := runtime.runPolicies_phase_mono players _ [.environment]
            execution middle firstRun
          change phase < execution.native.application.phase at already
          change phase < middle.native.application.phase
          omega
      have middleFollows := runtime.runPolicies_follows
        (.sample name fresh law tail) phase players _ [.environment]
        execution middle follows firstRun
      have tailFollows := State.follows_sample_tail_of_lt phase
        middle.native.application middleFollows (by simpa using advanced)
      have middleOrdered := runtime.runPolicies_clockOrdered players _ [.environment]
        execution middle ordered firstRun
      have middleCursor := runtime.runPolicies_service_cursor players _
        [.expire phase] execution middle firstRun
      apply ih runtime players wire (before ++ [ServiceInstruction.expire phase])
        (phase + 1) middle next tailFollows middleOrdered
      · simpa [List.filterMap_append, cursor] using middleCursor
      · simpa [List.append_assoc] using rest
  | bind name owner fresh tail ih =>
      rename_i payloadTy
      let lead : List (ServiceInstruction Player) :=
        [.player owner, .player owner] ++
          (List.replicate reactionRounds (reactionRound roster)).flatten ++
          [.includeLatest owner]
      let expiry : List (ServiceInstruction Player) :=
        List.replicate (max 1 (runtime.deadline phase)) (.expire phase)
      have planEq : runtime.servicePlan roster reactionRounds
          (.bind name owner fresh tail) phase =
          lead ++ expiry ++ runtime.servicePlan roster reactionRounds tail (phase + 1) := by
        simp [servicePlan, lead, expiry, List.append_assoc]
      rw [planEq, List.map_append, List.map_append,
        runtime.application.runPolicies_append] at supported
      simp only [FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨afterExpiry, headRun, tailRun⟩ := supported
      rw [runtime.application.runPolicies_append] at headRun
      simp only [FinDist.support_bind, Set.mem_iUnion] at headRun
      obtain ⟨afterLead, leadRun, expiryRun⟩ := headRun
      have leadInv := runtime.runPolicies_service_prefix_invariants
        (.bind name owner fresh tail) phase players _ lead execution afterLead
        follows ordered leadRun
      have leadCursor : afterLead.environmentHistory.length =
          ((before ++ lead).filterMap ServiceInstruction.environmentSlot).length := by
        rw [List.filterMap_append, List.length_append, leadInv.2.2, cursor]
      have advanced := runtime.runPolicies_expire_advances
        (.bind name owner fresh tail) players (before ++ lead)
        (runtime.servicePlan roster reactionRounds tail (phase + 1)) phase wire
        afterLead afterExpiry leadInv.1 leadInv.2.1 (by simp [remainingPhases])
        leadCursor (by simpa [expiry, List.append_assoc] using expiryRun)
      have expiryFollows := runtime.runPolicies_follows
        (.bind name owner fresh tail) phase players _ _ afterLead afterExpiry
        leadInv.1 expiryRun
      have tailFollows := State.follows_bind_tail_of_lt phase
        afterExpiry.native.application expiryFollows (by simpa using advanced)
      have expiryOrdered := runtime.runPolicies_clockOrdered players _ _ afterLead
        afterExpiry leadInv.2.1 expiryRun
      have expiryCursor := runtime.runPolicies_service_cursor players _ expiry
        afterLead afterExpiry expiryRun
      apply ih runtime players wire (before ++ lead ++ expiry)
        (phase + 1) afterExpiry next tailFollows expiryOrdered
      · rw [List.filterMap_append, List.filterMap_append, List.length_append,
          List.length_append, expiryCursor, leadInv.2.2, cursor]
      · simpa [List.append_assoc] using tailRun
  | resolve output owner binding fresh source checks tail ih =>
      rename_i payloadTy
      let lead : List (ServiceInstruction Player) :=
        [.player owner, .player owner] ++
          (List.replicate reactionRounds (reactionRound roster)).flatten ++
          [.includeLatest owner]
      let expiry : List (ServiceInstruction Player) :=
        List.replicate (max 1 (runtime.deadline phase)) (.expire phase)
      have planEq : runtime.servicePlan roster reactionRounds
          (.resolve output owner binding fresh source checks tail) phase =
          lead ++ expiry ++ runtime.servicePlan roster reactionRounds tail (phase + 1) := by
        simp [servicePlan, lead, expiry, List.append_assoc]
      rw [planEq, List.map_append, List.map_append,
        runtime.application.runPolicies_append] at supported
      simp only [FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨afterExpiry, headRun, tailRun⟩ := supported
      rw [runtime.application.runPolicies_append] at headRun
      simp only [FinDist.support_bind, Set.mem_iUnion] at headRun
      obtain ⟨afterLead, leadRun, expiryRun⟩ := headRun
      have leadInv := runtime.runPolicies_service_prefix_invariants
        (.resolve output owner binding fresh source checks tail) phase players _ lead
        execution afterLead follows ordered leadRun
      have leadCursor : afterLead.environmentHistory.length =
          ((before ++ lead).filterMap ServiceInstruction.environmentSlot).length := by
        rw [List.filterMap_append, List.length_append, leadInv.2.2, cursor]
      have advanced := runtime.runPolicies_expire_advances
        (.resolve output owner binding fresh source checks tail) players (before ++ lead)
        (runtime.servicePlan roster reactionRounds tail (phase + 1)) phase wire
        afterLead afterExpiry leadInv.1 leadInv.2.1 (by simp [remainingPhases])
        leadCursor (by simpa [expiry, List.append_assoc] using expiryRun)
      have expiryFollows := runtime.runPolicies_follows
        (.resolve output owner binding fresh source checks tail) phase players _ _
        afterLead afterExpiry leadInv.1 expiryRun
      have tailFollows := State.follows_resolve_tail_of_lt phase
        afterExpiry.native.application expiryFollows (by simpa using advanced)
      have expiryOrdered := runtime.runPolicies_clockOrdered players _ _ afterLead
        afterExpiry leadInv.2.1 expiryRun
      have expiryCursor := runtime.runPolicies_service_cursor players _ expiry
        afterLead afterExpiry expiryRun
      apply ih runtime players wire (before ++ lead ++ expiry)
        (phase + 1) afterExpiry next tailFollows expiryOrdered
      · rw [List.filterMap_append, List.filterMap_append, List.length_append,
          List.length_append, expiryCursor, leadInv.2.2, cursor]
      · simpa [List.append_assoc] using tailRun

/-- The concrete plan terminates from the actual graph-runtime initialization,
including its generated initial bindings and commitment candidates. -/
theorem servicePlan_terminates (runtime : GraphRuntime Player L Δ)
    (graph : Graph Player L Γ Δ) (input : VEnv L Γ)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (next : runtime.application.PolicyExecution)
    (supported : next ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment (runtime.servicePlan roster reactionRounds graph 0) wire)
      ((runtime.servicePlan roster reactionRounds graph 0).map
        ServiceInstruction.invocation)
      (MessageApplication.PolicyExecution.initial _
        (MessageApplication.State.initial _ (State.initial graph input)))).support) :
    next.native.application.outcome?.isSome = true := by
  apply runtime.servicePlan_terminates_from roster reactionRounds players wire [] 0 graph
    (MessageApplication.PolicyExecution.initial _
      (MessageApplication.State.initial _ (State.initial graph input))) next
  · exact State.initial_follows graph input
  · exact State.initial_clockOrdered graph input
  · rfl
  · simpa using supported

/-- Every supported play of the actual service game has a terminal graph
outcome, for arbitrary players, wire policy, roster, reaction count, and input
distribution. -/
theorem servicedGame_complete (runtime : GraphRuntime Player L Δ)
    (graph : Graph Player L Γ Δ) (inputs : FinDist (VEnv L Γ))
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy)
    (players : Player → runtime.application.PlayerPolicy)
    (next : runtime.application.PolicyExecution)
    (supported : next ∈
      ((runtime.servicedGame graph inputs roster reactionRounds wire).play players).support) :
    next.native.application.outcome?.isSome = true := by
  simp only [servicedGame, FinDist.support_bind, Set.mem_iUnion] at supported
  obtain ⟨input, _inputSupport, runSupport⟩ := supported
  exact runtime.servicePlan_terminates graph input roster reactionRounds players wire
    next runSupport

end Vegas.GraphRuntime
