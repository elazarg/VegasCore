/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageBindingAcceptance
import Vegas.Graph.MessagePolicyLaws
import Vegas.Graph.MessageServiceLaw
import Vegas.Graph.MessageServiceProtection
import Interaction.MessageApplicationSubmission
import Interaction.MessageApplicationSubmissionOrigin

/-! # Phase-local submission protection for graph bindings -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

private theorem compileAt_bind_submit_payload
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (name : VarId) (owner : Player) {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst)
    (tail : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner (.bind name owner fresh tail))
    (site : Nat) (history : List (Entry runtime)) (view : runtime.application.View)
    (wirePayload : Payload Player L)
    (atSite : view.application.publicState.pc = site)
    (supported : (.submit wirePayload : Command runtime) ∈
      (compileAt runtime owner whole (.bind name owner fresh tail) policy site history
        view).support) :
    wirePayload = .commitment site (owner, .prepared site) := by
  simp only [compileAt, atSite, ↓reduceDIte] at supported
  split at supported
  · simp only [FinDist.mem_support_pure] at supported
    cases supported
  · split at supported
    · simp only [FinDist.mem_support_pure] at supported
      exact MessageInterface.PlayerCommand.submit.inj supported
    · split at supported
      · split at supported
        · rw [FinDist.support_map] at supported
          obtain ⟨choice, _, impossible⟩ := supported
          cases impossible
        · simp only [FinDist.mem_support_pure] at supported
          cases supported
      · simp only [FinDist.mem_support_pure] at supported
        cases supported

private theorem canonicalSubmitted_of_actual_history
    (runtime : GraphRuntime Player L Δ)
    (name : VarId) (owner : Player) {payload : L.Ty}
    (whole : Graph Player L Γ₀ Δ) (policy : BehavioralPolicy owner whole)
    (fresh : name ∉ Γ.map Prod.fst)
    (tail : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (site : Nat) (walk : Prefix Δ whole (.bind name owner fresh tail) site)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy whole owner policy)
    (execution : runtime.application.PolicyExecution)
    (provenance : ∀ who entry, entry ∈ execution.principalHistory who →
      ∃ history, entry.command ∈ (players who history entry.beforeView).support)
    (submitted : submittedAt (execution.principalHistory owner) site = true) :
    runtime.application.SubmittedPayload (.commitment site (owner, .prepared site))
      (execution.principalHistory owner) := by
  unfold submittedAt at submitted
  rw [List.any_eq_true] at submitted
  obtain ⟨entry, member, matched⟩ := submitted
  obtain ⟨prior, commandMem⟩ := provenance owner entry member
  have atPhase := runtime.compilePlayerPolicy_command_atPhase whole owner policy prior
    entry.beforeView entry.command (by rwa [← ownerCompiled])
  cases commandEq : entry.command with
  | privateCommand privateCommand | replay privateCommand | wait =>
      rw [commandEq] at matched
      change false = true at matched
      contradiction
  | submit wirePayload =>
      cases wirePayload with
      | malformed raw =>
          rw [commandEq] at matched
          change false = true at matched
          contradiction
      | commitment submittedSite handle =>
          rw [commandEq] at matched
          change decide (submittedSite = site) = true at matched
          simp only [decide_eq_true_eq] at matched
          subst submittedSite
          have siteEq : entry.beforeView.application.publicState.pc = site := by
            rw [commandEq] at atPhase
            simpa only [Command.AtPhase] using atPhase.1.symm
          rw [commandEq] at commandMem
          rw [ownerCompiled,
            Prefix.compilePlayerPolicy_eq_suffix walk owner policy prior entry.beforeView siteEq]
            at commandMem
          have payloadEq := compileAt_bind_submit_payload runtime whole name owner fresh tail
            (walk.policyTail owner policy) site prior entry.beforeView _ siteEq commandMem
          cases payloadEq
          exact ⟨entry, member, commandEq⟩
      | opening submittedSite handle raw =>
          rw [commandEq] at matched
          change decide (submittedSite = site) = true at matched
          simp only [decide_eq_true_eq] at matched
          subst submittedSite
          have siteEq : entry.beforeView.application.publicState.pc = site := by
            rw [commandEq] at atPhase
            simpa only [Command.AtPhase] using atPhase.symm
          rw [commandEq] at commandMem
          rw [ownerCompiled,
            Prefix.compilePlayerPolicy_eq_suffix walk owner policy prior entry.beforeView siteEq]
            at commandMem
          have impossible := compileAt_bind_submit_payload runtime whole name owner fresh tail
            (walk.policyTail owner policy) site prior entry.beforeView _ siteEq commandMem
          cases impossible
      | withhold submittedSite =>
          rw [commandEq] at matched
          change decide (submittedSite = site) = true at matched
          simp only [decide_eq_true_eq] at matched
          subst submittedSite
          have siteEq : entry.beforeView.application.publicState.pc = site := by
            rw [commandEq] at atPhase
            simpa only [Command.AtPhase] using atPhase.symm
          rw [commandEq] at commandMem
          rw [ownerCompiled,
            Prefix.compilePlayerPolicy_eq_suffix walk owner policy prior entry.beforeView siteEq]
            at commandMem
          have impossible := compileAt_bind_submit_payload runtime whole name owner fresh tail
            (walk.policyTail owner policy) site prior entry.beforeView _ siteEq commandMem
          cases impossible

private theorem runPolicies_submittedPayload_preserved
    (runtime : GraphRuntime Player L Δ) (who : Player)
    (payload : runtime.application.Payload)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (submitted : runtime.application.SubmittedPayload payload
      (execution.principalHistory who))
    (supported : next ∈ (runtime.application.runPolicies players environment schedule
      execution).support) :
    runtime.application.SubmittedPayload payload (next.principalHistory who) := by
  apply runtime.application.runPolicies_execution_invariant
    (fun current => runtime.application.SubmittedPayload payload
      (current.principalHistory who)) players environment
  · intro current actor command after currentSubmitted _commandMem stepMem
    obtain ⟨entry, member, entryCommand⟩ := currentSubmitted
    by_cases same : actor = who
    · subst actor
      refine ⟨entry, ?_, entryCommand⟩
      rw [runtime.application.playerStep_history_self who current command after stepMem]
      exact List.mem_append_left _ member
    · refine ⟨entry, ?_, entryCommand⟩
      rwa [runtime.application.playerStep_other_history actor who (Ne.symm same) current command
        after stepMem]
  · intro current command after currentSubmitted _commandMem stepMem
    simpa [runtime.application.environmentStep_principalHistory current command after stepMem]
      using currentSubmitted
  · exact submitted
  · exact supported

private theorem submittedAt_true_of_canonicalSubmitted
    (runtime : GraphRuntime Player L Δ) (owner : Player) (site : Nat)
    (history : List (Entry runtime))
    (submitted : runtime.application.SubmittedPayload
      (.commitment site (owner, .prepared site)) history) :
    submittedAt history site = true := by
  obtain ⟨entry, member, command⟩ := submitted
  unfold submittedAt
  rw [List.any_eq_true]
  refine ⟨entry, member, ?_⟩
  rw [command]
  simp

/-- Once the canonical commitment is first emitted during an actual run, it
remains pending while its binding stays current, or that binding phase has
already advanced. Other players and the environment are unrestricted. -/
theorem runPolicies_bind_submission_pending_or_advanced
    (runtime : GraphRuntime Player L Δ)
    (name : VarId) (owner : Player) {payload : L.Ty}
    (whole : Graph Player L Γ₀ Δ) (policy : BehavioralPolicy owner whole)
    (fresh : name ∉ Γ.map Prod.fst)
    (tail : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (base : Nat) (players : Player → runtime.application.PlayerPolicy)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy whole owner policy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows
      (.bind name owner fresh tail) base)
    (notSubmitted : ¬ runtime.application.SubmittedPayload
      (.commitment base (owner, .prepared base)) (execution.principalHistory owner))
    (supported : next ∈ (runtime.application.runPolicies players environment schedule
      execution).support)
    (submitted : runtime.application.SubmittedPayload
      (.commitment base (owner, .prepared base)) (next.principalHistory owner)) :
    base < next.native.application.phase ∨
      (next.native.application.Follows (.bind name owner fresh tail) base ∧
        next.native.application.phase = base ∧
        runtime.application.AuthoredPending owner
          (.commitment base (owner, .prepared base)) next.native) := by
  let invariant : State Player L Δ → Prop := fun state =>
    state.Follows (.bind name owner fresh tail) base
  let ready : State Player L Δ → Prop := fun state => invariant state ∧ state.phase = base
  let milestone : State Player L Δ → Prop := fun state => base < state.phase
  have bridge := runtime.application.runPolicies_submitted_pendingOrResolved
    invariant ready milestone owner (.commitment base (owner, .prepared base))
    players environment
    (fun application actor command valid =>
      runtime.privateStep_follows (.bind name owner fresh tail) base application actor command
        valid)
    (fun application message after valid accepted =>
      runtime.handle_follows (.bind name owner fresh tail) base application after message valid
        accepted)
    (fun (application : State Player L Δ)
        (command : runtime.application.EnvironmentCommand)
        (after : State Player L Δ) (valid : invariant application)
        (happened : after ∈ (runtime.application.environmentStep application command).support) => by
      cases command with
      | tick =>
          exact runtime.tick_follows (.bind name owner fresh tail) base application after
            valid happened)
    (fun application actor command done => by
      change base < (runtime.privateStep application actor command).phase
      rw [runtime.privateStep_phase]
      exact done)
    (fun application actor command current => by
      left
      refine ⟨runtime.privateStep_follows (.bind name owner fresh tail) base application actor
        command current.1, ?_⟩
      change (runtime.privateStep application actor command).phase = base
      rw [runtime.privateStep_phase]
      exact current.2)
    (fun application message after done accepted => by
      have step := runtime.handle_phase application after message accepted
      omega)
    (fun application message after current accepted => by
      right
      have step := runtime.handle_phase application after message accepted
      omega)
    (fun (application : State Player L Δ)
        (command : runtime.application.EnvironmentCommand)
        (after : State Player L Δ) done happened => by
      cases command with
      | tick =>
          have monotone := runtime.tick_phase_mono application after happened
          omega)
    (fun (application : State Player L Δ)
        (command : runtime.application.EnvironmentCommand)
        (after : State Player L Δ) current happened => by
      cases command with
      | tick =>
          have monotone := runtime.tick_phase_mono application after happened
          rcases Nat.eq_or_lt_of_le monotone with same | later
          · left
            exact ⟨runtime.tick_follows (.bind name owner fresh tail) base application after
              current.1 happened, by omega⟩
          · right; omega)
    (fun application serial current => by
      obtain ⟨ideal, values, bindings, candidates, clock, enteredAt, stateEq⟩ :=
        State.follows_at_base (.bind name owner fresh tail) base application current.1
          (by simpa using current.2)
      refine ⟨advanceBind tail ideal values bindings candidates base clock
        (owner, .prepared base), ?_, ?_⟩
      · rw [stateEq]
        simp only [GraphRuntime.application]
        simp only [GraphRuntime.handle, Message.sender, decide_eq_true_eq,
          Bool.and_self, if_true]
      · simp [milestone, State.phase, advanceBind])
    (fun current command valid commandMem commandEq => by
      have atPhase := runtime.compilePlayerPolicy_command_atPhase whole owner policy
        (current.principalHistory owner)
        (MessageApplication.State.observe runtime.application current.native owner)
        command (by rwa [← ownerCompiled])
      refine ⟨valid, ?_⟩
      rw [commandEq] at atPhase
      have siteEq := atPhase.1
      change base = current.native.application.publicView.pc at siteEq
      change current.native.application.phase = base
      rw [← State.publicView_pc]
      exact siteEq.symm)
    schedule execution next follows notSubmitted supported submitted
  rcases bridge with advanced | ⟨⟨stillFollows, same⟩, pending⟩
  · exact Or.inl advanced
  · exact Or.inr ⟨stillFollows, same, pending⟩

/-- If the current binding already has an immutable preparation, its next
actual compiled-owner invocation records the exact canonical submission. -/
theorem runPolicies_bind_prepared_owner_submits
    (runtime : GraphRuntime Player L Δ)
    (name : VarId) (owner : Player) {payload : L.Ty}
    (whole : Graph Player L Γ₀ Δ) (policy : BehavioralPolicy owner whole)
    (fresh : name ∉ Γ.map Prod.fst)
    (tail : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (base : Nat) (walk : Prefix Δ whole (.bind name owner fresh tail) base)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy whole owner policy)
    (environment : runtime.application.EnvironmentPolicy)
    (execution next : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows (.bind name owner fresh tail) base)
    (atPhase : execution.native.application.phase = base)
    (raw : Raw L) (prepared : preparedRaw (execution.principalHistory owner) base = some raw)
    (unsubmitted : submittedAt (execution.principalHistory owner) base = false)
    (supported : next ∈ (runtime.application.runPolicies players environment
      [.player owner] execution).support) :
    runtime.application.SubmittedPayload (.commitment base (owner, .prepared base))
      (next.principalHistory owner) := by
  obtain ⟨ideal, values, bindings, candidates, clock, enteredAt, stateEq⟩ :=
    State.follows_at_base (.bind name owner fresh tail) base execution.native.application
      follows (by simpa using atPhase)
  simp only [MessageApplication.runPolicies, MessageApplication.invoke,
    FinDist.support_bind, Set.mem_iUnion, FinDist.mem_support_pure] at supported
  obtain ⟨middle, ⟨command, commandMem, stepMem⟩, rfl⟩ := supported
  let currentView :=
    MessageApplication.State.observe runtime.application execution.native owner
  have viewPhase : currentView.application.publicState.pc = base := by
    change execution.native.application.publicView.pc = base
    rw [State.publicView_pc]
    exact atPhase
  change command ∈ (players owner (execution.principalHistory owner) currentView).support
    at commandMem
  rw [ownerCompiled,
    Prefix.compilePlayerPolicy_eq_suffix walk owner policy _ _ viewPhase,
    compileAt_bind_prepared runtime whole base name owner fresh tail
      (walk.policyTail owner policy) _ _ raw viewPhase prepared unsubmitted] at commandMem
  simp only [FinDist.mem_support_pure] at commandMem
  subst command
  have history := runtime.application.playerStep_history_self owner execution
    (.submit (.commitment base (owner, .prepared base))) next stepMem
  unfold MessageApplication.SubmittedPayload
  refine ⟨⟨currentView,
    .submit (.commitment base (owner, .prepared base))⟩, ?_, rfl⟩
  rw [history]
  simp only [List.mem_append, List.mem_singleton]
  right
  rfl

/-- From a genuinely fresh binding cache, two consecutive actual invocations
of the compiled owner first record its sampled choice and then submit the
canonical commitment. -/
theorem runPolicies_bind_two_owner_calls_submit
    (runtime : GraphRuntime Player L Δ)
    (name : VarId) (owner : Player) {payload : L.Ty}
    (whole : Graph Player L Γ₀ Δ) (policy : BehavioralPolicy owner whole)
    (fresh : name ∉ Γ.map Prod.fst)
    (tail : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (base : Nat) (walk : Prefix Δ whole (.bind name owner fresh tail) base)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy whole owner policy)
    (environment : runtime.application.EnvironmentPolicy)
    (execution next : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows (.bind name owner fresh tail) base)
    (atPhase : execution.native.application.phase = base)
    (unprepared : preparedRaw (execution.principalHistory owner) base = none)
    (unsubmitted : submittedAt (execution.principalHistory owner) base = false)
    (supported : next ∈ (runtime.application.runPolicies players environment
      [.player owner, .player owner] execution).support) :
    runtime.application.SubmittedPayload (.commitment base (owner, .prepared base))
      (next.principalHistory owner) := by
  obtain ⟨ideal, values, bindings, candidates, clock, enteredAt, stateEq⟩ :=
    State.follows_at_base (.bind name owner fresh tail) base execution.native.application
      follows (by simpa using atPhase)
  let view := MessageApplication.State.observe runtime.application execution.native owner
  have viewPhase : view.application.publicState.pc = base := by
    change execution.native.application.publicView.pc = base
    rw [State.publicView_pc]
    exact atPhase
  have viewOwner : view.application.who = owner := rfl
  have viewContext : view.application.publicState.Γ = Γ := by
    change execution.native.application.publicView.Γ = Γ
    rw [stateEq]
    rfl
  have playerAtHead : players owner (execution.principalHistory owner) view =
      compileAt runtime owner whole (.bind name owner fresh tail)
        (walk.policyTail owner policy) base (execution.principalHistory owner) view := by
    rw [ownerCompiled]
    exact Prefix.compilePlayerPolicy_eq_suffix walk owner policy _ _ viewPhase
  have factor := runtime.runPolicies_bind_first_kernel whole base name owner fresh tail
    (walk.policyTail owner policy) players execution environment [.player owner]
    playerAtHead viewPhase viewOwner viewContext unprepared unsubmitted
  rw [factor] at supported
  simp only [FinDist.support_bind, Set.mem_iUnion] at supported
  obtain ⟨choice, _choiceMem, preparedExecution, prepareStep, remaining⟩ := supported
  have history := runtime.application.playerStep_history_self owner execution
    (.privateCommand (.prepare base
      ⟨R.result payload, (R.valueEquiv payload).symm choice⟩)) preparedExecution prepareStep
  have nowPrepared : preparedRaw (preparedExecution.principalHistory owner) base =
      some ⟨R.result payload, (R.valueEquiv payload).symm choice⟩ := by
    rw [history]
    exact preparedRaw_append_prepare runtime _ _ base _ unprepared
  have stillUnsubmitted : submittedAt (preparedExecution.principalHistory owner) base = false := by
    rw [history]
    unfold submittedAt at unsubmitted ⊢
    rw [List.any_append, unsubmitted]
    rfl
  have nativeMem : preparedExecution.native ∈
      ((runtime.application.playerStep owner execution
        (.privateCommand (.prepare base
          ⟨R.result payload, (R.valueEquiv payload).symm choice⟩))).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨preparedExecution, prepareStep, rfl⟩
  rw [runtime.application.playerStep_native] at nativeMem
  simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
    FinDist.mem_support_pure] at nativeMem
  have preparedApplication : preparedExecution.native.application =
      runtime.privateStep execution.native.application owner
        (.prepare base ⟨R.result payload, (R.valueEquiv payload).symm choice⟩) := by
    rw [nativeMem]
    rfl
  have preparedFollows : preparedExecution.native.application.Follows
      (.bind name owner fresh tail) base := by
    rw [preparedApplication]
    exact runtime.privateStep_follows (.bind name owner fresh tail) base
      execution.native.application owner _ follows
  have preparedPhase : preparedExecution.native.application.phase = base := by
    rw [preparedApplication, runtime.privateStep_phase]
    exact atPhase
  exact runPolicies_bind_prepared_owner_submits runtime name owner whole policy fresh tail base
    walk players ownerCompiled environment preparedExecution next preparedFollows preparedPhase _
    nowPrepared stillUnsubmitted remaining

private theorem notSubmittedPayload_of_submittedAt_false
    (runtime : GraphRuntime Player L Δ) (owner : Player) (site : Nat)
    (history : List (Entry runtime)) (missing : submittedAt history site = false) :
    ¬ runtime.application.SubmittedPayload (.commitment site (owner, .prepared site)) history := by
  intro submitted
  obtain ⟨entry, member, command⟩ := submitted
  unfold submittedAt at missing
  rw [List.any_eq_false] at missing
  have entryFalse := missing entry member
  rw [command] at entryFalse
  simp at entryFalse

/-- The two fresh-cache owner calls establish the protected-envelope side of
the service invariant: afterwards the binding has advanced, or its exact
canonical commitment is still pending at the current phase. -/
theorem runPolicies_bind_fresh_two_calls_pending_or_advanced
    (runtime : GraphRuntime Player L Δ)
    (name : VarId) (owner : Player) {payload : L.Ty}
    (whole : Graph Player L Γ₀ Δ) (policy : BehavioralPolicy owner whole)
    (fresh : name ∉ Γ.map Prod.fst)
    (tail : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (base : Nat) (walk : Prefix Δ whole (.bind name owner fresh tail) base)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy whole owner policy)
    (environment : runtime.application.EnvironmentPolicy)
    (execution next : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows (.bind name owner fresh tail) base)
    (atPhase : execution.native.application.phase = base)
    (unprepared : preparedRaw (execution.principalHistory owner) base = none)
    (unsubmitted : submittedAt (execution.principalHistory owner) base = false)
    (supported : next ∈ (runtime.application.runPolicies players environment
      [.player owner, .player owner] execution).support) :
    base < next.native.application.phase ∨
      (next.native.application.Follows (.bind name owner fresh tail) base ∧
        next.native.application.phase = base ∧
        runtime.application.AuthoredPending owner
          (.commitment base (owner, .prepared base)) next.native) := by
  apply runPolicies_bind_submission_pending_or_advanced runtime name owner whole policy fresh
    tail base players ownerCompiled environment [.player owner, .player owner] execution next
    follows
  · exact notSubmittedPayload_of_submittedAt_false runtime owner base _ unsubmitted
  · exact supported
  · exact runPolicies_bind_two_owner_calls_submit runtime name owner whole policy fresh tail base
      walk players ownerCompiled environment execution next follows atPhase unprepared unsubmitted
      supported

/-- For an actually reached current binding, two consecutive compiled-owner
calls leave a canonical submission in history for every cache state. -/
theorem runPolicies_bind_two_owner_calls_submitted
    (runtime : GraphRuntime Player L Δ)
    (name : VarId) (owner : Player) {payload : L.Ty}
    (whole : Graph Player L Γ₀ Δ) (policy : BehavioralPolicy owner whole)
    (fresh : name ∉ Γ.map Prod.fst)
    (tail : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (base : Nat) (walk : Prefix Δ whole (.bind name owner fresh tail) base)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy whole owner policy)
    (environment : runtime.application.EnvironmentPolicy)
    (initial : runtime.application.Application)
    (prefixSchedule : List (@MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (reached : execution ∈ (runtime.application.runPolicies players environment prefixSchedule
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application initial))).support)
    (follows : execution.native.application.Follows (.bind name owner fresh tail) base)
    (atPhase : execution.native.application.phase = base)
    (supported : next ∈ (runtime.application.runPolicies players environment
      [.player owner, .player owner] execution).support) :
    submittedAt (next.principalHistory owner) base = true ∧
      runtime.application.SubmittedPayload (.commitment base (owner, .prepared base))
        (next.principalHistory owner) := by
  have provenance := runtime.application.runPolicies_initial_history_supported players environment
    prefixSchedule (MessageApplication.State.initial runtime.application initial) execution reached
  have canonical : runtime.application.SubmittedPayload
      (.commitment base (owner, .prepared base)) (next.principalHistory owner) := by
    by_cases wasSubmitted : submittedAt (execution.principalHistory owner) base = true
    · have beforeCanonical := canonicalSubmitted_of_actual_history runtime name owner whole policy
        fresh tail base walk players ownerCompiled execution provenance wasSubmitted
      exact runPolicies_submittedPayload_preserved runtime owner _ players environment
        [.player owner, .player owner] execution next beforeCanonical supported
    · have unsubmitted : submittedAt (execution.principalHistory owner) base = false :=
        Bool.eq_false_iff.mpr wasSubmitted
      cases prepared : preparedRaw (execution.principalHistory owner) base with
      | none =>
          exact runPolicies_bind_two_owner_calls_submit runtime name owner whole policy fresh tail
            base walk players ownerCompiled environment execution next follows atPhase prepared
            unsubmitted supported
      | some raw =>
          simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion]
            at supported
          obtain ⟨middle, first, second⟩ := supported
          have firstSupported : middle ∈ (runtime.application.runPolicies players environment
              [.player owner] execution).support := by
            simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion]
            exact ⟨middle, first, FinDist.mem_support_pure.mpr rfl⟩
          have middleSubmitted := runPolicies_bind_prepared_owner_submits runtime name owner whole
            policy fresh tail base walk players ownerCompiled environment execution middle follows
            atPhase raw prepared unsubmitted firstSupported
          have secondSupported : next ∈ (runtime.application.runPolicies players environment
              [.player owner] middle).support := by
            simpa only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion,
              FinDist.mem_support_pure] using second
          exact runPolicies_submittedPayload_preserved runtime owner _ players environment
            [.player owner] middle next middleSubmitted secondSupported
  exact ⟨submittedAt_true_of_canonicalSubmitted runtime owner base _ canonical, canonical⟩

end Vegas.GraphRuntime
