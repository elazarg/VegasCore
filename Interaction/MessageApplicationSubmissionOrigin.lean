/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageApplicationPolicyInvariant

/-! # Operational origins of retained messages -/

noncomputable section
namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} [DecidableEq Principal]
variable (app : MessageApplication Principal)

private theorem invoke_history_origin
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (invocation : @Invocation Principal) (execution next : app.PolicyExecution)
    (supported : next ∈ (app.invoke players environment execution invocation).support)
    (who : Principal) (entry : app.PlayerEntry) (member : entry ∈ next.principalHistory who) :
    entry ∈ execution.principalHistory who ∨
      (invocation = .player who ∧ entry.beforeView = State.observe app execution.native who ∧
        entry.command ∈ (players who (execution.principalHistory who) entry.beforeView).support ∧
        next ∈ (app.playerStep who execution entry.command).support) := by
  cases invocation with
  | environment =>
      simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨command, _, step⟩ := supported
      left
      rwa [app.environmentStep_principalHistory execution command next step] at member
  | player actor =>
      simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨command, commandMem, step⟩ := supported
      by_cases same : actor = who
      · subst actor
        rw [app.playerStep_history_self who execution command next step] at member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with prior | rfl
        · exact Or.inl prior
        · exact Or.inr ⟨rfl, rfl, commandMem, step⟩
      · left
        rwa [app.playerStep_other_history actor who (Ne.symm same)
          execution command next step] at member

/-- A history entry either predates the run or records an actual supported
player invocation in it. The checkpoint retains the entire native execution,
not only the observation stored in the entry. -/
theorem runPolicies_history_origin
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (execution final : app.PolicyExecution)
    (supported : final ∈ (app.runPolicies players environment schedule execution).support)
    (who : Principal) (entry : app.PlayerEntry) (member : entry ∈ final.principalHistory who) :
    entry ∈ execution.principalHistory who ∨
      ∃ front suffix before after,
        schedule = front ++ .player who :: suffix ∧
        before ∈ (app.runPolicies players environment front execution).support ∧
        entry.beforeView = State.observe app before.native who ∧
        entry.command ∈ (players who (before.principalHistory who) entry.beforeView).support ∧
        after ∈ (app.playerStep who before entry.command).support ∧
        final ∈ (app.runPolicies players environment suffix after).support := by
  induction schedule generalizing execution with
  | nil =>
      simp only [runPolicies, FinDist.mem_support_pure] at supported
      subst final
      exact Or.inl member
  | cons invocation rest ih =>
      simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨middle, first, last⟩ := supported
      rcases ih middle last with prior | origin
      · rcases app.invoke_history_origin players environment invocation execution middle
          first who entry prior with initial | here
        · exact Or.inl initial
        · rcases here with ⟨invocationEq, viewEq, commandMem, step⟩
          subst invocation
          exact Or.inr ⟨[], rest, execution, middle, rfl,
            FinDist.mem_support_pure.mpr rfl, viewEq, commandMem, step, last⟩
      · rcases origin with
          ⟨front, suffix, before, after, split, beforeMem, viewEq, commandMem, step, residual⟩
        refine Or.inr ⟨invocation :: front, suffix, before, after, ?_, ?_,
          viewEq, commandMem, step, residual⟩
        · simp only [List.cons_append, split]
        · simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion]
          exact ⟨middle, first, beforeMem⟩

/-- Every history entry in an initialized run has its own supported invocation
checkpoint and a supported residual execution with the same policies. -/
theorem runPolicies_initial_history_origin
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (initial : app.State)
    (final : app.PolicyExecution)
    (supported : final ∈ (app.runPolicies players environment schedule
      (PolicyExecution.initial app initial)).support)
    (who : Principal) (entry : app.PlayerEntry) (member : entry ∈ final.principalHistory who) :
    ∃ front suffix before after,
      schedule = front ++ .player who :: suffix ∧
      before ∈ (app.runPolicies players environment front
        (PolicyExecution.initial app initial)).support ∧
      entry.beforeView = State.observe app before.native who ∧
      entry.command ∈ (players who (before.principalHistory who) entry.beforeView).support ∧
      after ∈ (app.playerStep who before entry.command).support ∧
      final ∈ (app.runPolicies players environment suffix after).support := by
  rcases app.runPolicies_history_origin players environment schedule
      (PolicyExecution.initial app initial) final supported who entry member with prior | origin
  · exact (List.not_mem_nil prior).elim
  · exact origin

/-- Every recorded player command in an actual initialized run is supported
by that player's policy at its recorded observation and some prior history. -/
theorem runPolicies_initial_history_supported
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (initial : app.State)
    (next : app.PolicyExecution)
    (supported : next ∈ (app.runPolicies players environment schedule
      (PolicyExecution.initial app initial)).support) :
    ∀ who entry, entry ∈ next.principalHistory who →
      ∃ history, entry.command ∈ (players who history entry.beforeView).support := by
  intro who entry member
  obtain ⟨_, _, before, _, _, _, _, commandMem, _, _⟩ :=
    app.runPolicies_initial_history_origin players environment schedule initial next
      supported who entry member
  exact ⟨before.principalHistory who, commandMem⟩

/-- A message is retained in at least one pool store. Retention does not imply
that every principal has observed it. -/
def Retained (pool : MessagePool Principal app.Payload)
    (message : Message Principal app.Payload) : Prop :=
  message ∈ pool.pending ∨ message ∈ pool.ledger ∨
    (∃ who, message ∈ pool.inbox who) ∨ ∃ who, message ∈ pool.sent who

omit [DecidableEq Principal] in
private theorem satisfies_retained (pool : MessagePool Principal app.Payload) :
    pool.Satisfies (app.Retained pool) := by
  exact ⟨fun message mem => Or.inl mem,
    fun message mem => Or.inr (Or.inl mem),
    fun who message mem => Or.inr (Or.inr (Or.inl ⟨who, mem⟩)),
    fun who message mem => Or.inr (Or.inr (Or.inr ⟨who, mem⟩))⟩

omit [DecidableEq Principal] in
private theorem satisfies_of_retained
    {safe : Message Principal app.Payload → Prop}
    {pool : MessagePool Principal app.Payload} (all : pool.Satisfies safe)
    {message : Message Principal app.Payload} (retained : app.Retained pool message) :
    safe message := by
  rcases retained with pending | ledger | ⟨who, inbox⟩ | ⟨who, sent⟩
  · exact all.1 message pending
  · exact all.2.1 message ledger
  · exact all.2.2.1 who message inbox
  · exact all.2.2.2 who message sent

private theorem invoke_retained_origin
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (invocation : @Invocation Principal) (execution next : app.PolicyExecution)
    (supported : next ∈ (app.invoke players environment execution invocation).support)
    (message : Message Principal app.Payload) (retained : app.Retained next.native.pool message) :
    app.Retained execution.native.pool message ∨
      (invocation = .player message.sender ∧
        (.submit message.payload : app.PlayerCommand) ∈
          (players message.sender (execution.principalHistory message.sender)
            (State.observe app execution.native message.sender)).support ∧
        next ∈ (app.playerStep message.sender execution (.submit message.payload)).support ∧
        message.id = (message.sender, execution.native.pool.nextSerial message.sender)) := by
  cases invocation with
  | environment =>
      simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨command, _, step⟩ := supported
      left
      have safe := app.environmentPolicyStep_pool_satisfies
        (app.Retained execution.native.pool) execution next command
        (app.satisfies_retained execution.native.pool) step
      exact app.satisfies_of_retained safe retained
  | player actor =>
      simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨command, commandMem, step⟩ := supported
      cases command with
      | submit payload =>
          let newly : Message Principal app.Payload :=
            ⟨(actor, execution.native.pool.nextSerial actor), payload⟩
          let safe : Message Principal app.Payload → Prop := fun candidate =>
            app.Retained execution.native.pool candidate ∨ candidate = newly
          have prior : execution.native.pool.Satisfies safe :=
            (app.satisfies_retained execution.native.pool).mono
              (fun candidate old => Or.inl old)
          have afterSafe := app.playerStep_pool_satisfies safe actor execution next
            (.submit payload) prior (by
              intro submitted commandEq
              injection commandEq with payloadEq
              subst submitted
              exact Or.inr rfl) step
          have classified : safe message := app.satisfies_of_retained afterSafe retained
          rcases classified with old | new
          · exact Or.inl old
          · subst message
            exact Or.inr ⟨rfl, commandMem, step, rfl⟩
      | privateCommand privateCommand | replay privateCommand | wait =>
          left
          have afterSafe := app.playerStep_pool_satisfies
            (app.Retained execution.native.pool) actor execution next _
            (app.satisfies_retained execution.native.pool) (by intros; contradiction) step
          exact app.satisfies_of_retained afterSafe retained

/-- A retained message either predates the run or has a concrete submission
checkpoint in this very policy execution, with unchanged policies before and
after that checkpoint. -/
theorem runPolicies_retained_submission_origin
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (execution final : app.PolicyExecution)
    (supported : final ∈ (app.runPolicies players environment schedule execution).support)
    (message : Message Principal app.Payload) (retained : app.Retained final.native.pool message) :
    app.Retained execution.native.pool message ∨
      ∃ front suffix before submitted,
        schedule = front ++ .player message.sender :: suffix ∧
        before ∈ (app.runPolicies players environment front execution).support ∧
        (.submit message.payload : app.PlayerCommand) ∈
          (players message.sender (before.principalHistory message.sender)
            (State.observe app before.native message.sender)).support ∧
        submitted ∈
          (app.playerStep message.sender before (.submit message.payload)).support ∧
        message.id = (message.sender, before.native.pool.nextSerial message.sender) ∧
        final ∈ (app.runPolicies players environment suffix submitted).support := by
  induction schedule generalizing execution with
  | nil =>
      simp only [runPolicies, FinDist.mem_support_pure] at supported
      subst final
      exact Or.inl retained
  | cons invocation rest ih =>
      simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨middle, first, last⟩ := supported
      rcases ih middle last with old | origin
      · rcases app.invoke_retained_origin players environment invocation execution middle
          first message old with initial | submittedHere
        · exact Or.inl initial
        · rcases submittedHere with ⟨invocationEq, commandMem, step, idEq⟩
          subst invocation
          exact Or.inr ⟨[], rest, execution, middle, rfl,
            FinDist.mem_support_pure.mpr rfl, commandMem, step, idEq, last⟩
      · rcases origin with
          ⟨front, suffix, before, submitted, split, beforeMem, commandMem,
            step, idEq, residual⟩
        refine Or.inr ⟨invocation :: front, suffix, before, submitted, ?_, ?_,
          commandMem, step, idEq, residual⟩
        · simp only [List.cons_append, split]
        · simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion]
          exact ⟨middle, first, beforeMem⟩

/-- From the actual empty-pool initialization, every pending message has a
supported player-submission checkpoint and a supported residual execution. -/
theorem runPolicies_initial_pending_submission_origin
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (application : app.Application)
    (final : app.PolicyExecution)
    (supported : final ∈ (app.runPolicies players environment schedule
      (PolicyExecution.initial app (State.initial app application))).support)
    (message : Message Principal app.Payload) (pending : message ∈ final.native.pool.pending) :
    ∃ front suffix before submitted,
      schedule = front ++ .player message.sender :: suffix ∧
      before ∈ (app.runPolicies players environment front
        (PolicyExecution.initial app (State.initial app application))).support ∧
      (.submit message.payload : app.PlayerCommand) ∈
        (players message.sender (before.principalHistory message.sender)
          (State.observe app before.native message.sender)).support ∧
      submitted ∈ (app.playerStep message.sender before (.submit message.payload)).support ∧
      message.id = (message.sender, before.native.pool.nextSerial message.sender) ∧
      final ∈ (app.runPolicies players environment suffix submitted).support := by
  have origin := app.runPolicies_retained_submission_origin players environment schedule
    (PolicyExecution.initial app (State.initial app application)) final supported message
    (Or.inl pending)
  rcases origin with prior | actual
  · simp [Retained, PolicyExecution.initial, State.initial, MessagePool.empty] at prior
  · exact actual

end Interaction.MessageApplication
