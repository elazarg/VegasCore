/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.DeviationStopping
import Vegas.Pending.DeviationServiceSafety
import Vegas.Pending.ImmutablePrefix
import Vegas.Pending.DisclosureAcceptance

/-! # Recovering unchanged players' disclosures from later endpoints -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- A phase-changing wire step must be an accepted inclusion of the actual
selected pending packet. Delivery and rejected traffic cannot supply a phase
change. -/
theorem wireStep_phase_change_accepted (runtime : GraphRuntime Player L Δ)
    (execution next : runtime.application.PolicyExecution) (command : WireCommand Player)
    (supported : next ∈ (runtime.application.environmentPolicyStep execution
      (command.toEnvironmentCommand runtime.application)).support)
    (advanced : execution.native.application.phase < next.native.application.phase) :
    ∃ id message, execution.native.pool.lookup id = some message ∧
      runtime.handle execution.native.application message = some next.native.application := by
  have native : next.native ∈ ((runtime.application.environmentPolicyStep execution
      (command.toEnvironmentCommand runtime.application)).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  rw [runtime.application.environmentStep_native] at native
  cases command with
  | deliver who id | wait =>
      simp only [WireCommand.toEnvironmentCommand,
        MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at native
      rw [native] at advanced
      exact (Nat.lt_irrefl _ advanced).elim
  | «include» id =>
      simp only [WireCommand.toEnvironmentCommand,
        MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at native
      cases lookup : execution.native.pool.lookup id with
      | none =>
          rw [runtime.application.includePending_missing execution.native id lookup] at native
          rw [native] at advanced
          exact (Nat.lt_irrefl _ advanced).elim
      | some message =>
          cases accepted : runtime.handle execution.native.application message with
          | none =>
              rw [runtime.application.includePending_reject execution.native id message
                lookup accepted] at native
              rw [native] at advanced
              exact (Nat.lt_irrefl _ advanced).elim
          | some state =>
              rw [runtime.application.includePending_accept execution.native id message state
                lookup accepted] at native
              exact ⟨id, message, lookup, by simpa only [native] using accepted⟩

/-- At an unchanged player-owned cursor, a serviced phase change is an actual
accepted pending message. Deadline-relative safety rules out a timeout here. -/
theorem service_phase_change_accepted (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy) (focal : Player)
    (wire : runtime.application.WirePolicy)
    (before rest : List (ServiceInstruction Player)) (instruction : ServiceInstruction Player)
    (initial execution next : runtime.application.PolicyExecution)
    (empty : initial.environmentHistory = [])
    (safe : DeviationExpirySafe runtime players
      (runtime.serviceEnvironment (before ++ instruction :: rest) wire) (some focal)
      (before ++ instruction :: rest) initial)
    (reached : execution ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment (before ++ instruction :: rest) wire)
      (before.map ServiceInstruction.invocation) initial).support)
    (supported : next ∈ (runtime.application.invoke players
      (runtime.serviceEnvironment (before ++ instruction :: rest) wire)
      execution instruction.invocation).support)
    (notSample : ¬ execution.native.application.IsSample)
    (notFocal : ¬ execution.native.application.IsOwnedBy (some focal))
    (advanced : execution.native.application.phase < next.native.application.phase) :
    ∃ id message, execution.native.pool.lookup id = some message ∧
      runtime.handle execution.native.application message = some next.native.application := by
  cases instruction with
  | player actor =>
      simp only [ServiceInstruction.invocation, MessageApplication.invoke,
        FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨command, _, step⟩ := supported
      have same := runtime.playerStep_phase actor execution next command step
      rw [same] at advanced
      exact (Nat.lt_irrefl _ advanced).elim
  | wire =>
      have kernel := runtime.serviceEnvironment_after_prefix players before rest .wire wire
        initial execution empty rfl reached
      simp only [ServiceInstruction.invocation, MessageApplication.invoke, kernel,
        MessageApplication.wireEnvironment, FinDist.bind_map, FinDist.support_bind,
        Set.mem_iUnion] at supported
      obtain ⟨command, _, step⟩ := supported
      exact runtime.wireStep_phase_change_accepted execution next command step advanced
  | includeLatest owner =>
      have kernel := runtime.serviceEnvironment_after_prefix players before rest
        (.includeLatest owner) wire initial execution empty rfl reached
      simp only [ServiceInstruction.invocation, MessageApplication.invoke, kernel,
        FinDist.pure_bind] at supported
      rcases runtime.application.latestSubmissionCommand_cases owner
          (MessageApplication.State.environmentView runtime.application execution.native) with
        waiting | ⟨id, including⟩
      · rw [waiting] at supported
        exact runtime.wireStep_phase_change_accepted execution next .wait supported advanced
      · rw [including] at supported
        exact runtime.wireStep_phase_change_accepted execution next (.include id) supported advanced
  | expire phase =>
      have gated : execution.native.application.phase ≠ phase := by
        rcases safe before phase rest rfl execution reached with other | sample | owned
        · exact other
        · exact (notSample sample).elim
        · exact (notFocal owned).elim
      have kernel := runtime.serviceEnvironment_after_prefix players before rest
        (.expire phase) wire initial execution empty rfl reached
      simp only [State.publicView_pc, if_neg gated] at kernel
      simp only [ServiceInstruction.invocation, MessageApplication.invoke, kernel,
        FinDist.pure_bind] at supported
      exact runtime.wireStep_phase_change_accepted execution next .wait supported advanced

/-- Once an unchanged owner has sampled its disclosure, any later supported
endpoint beyond that resolve retains exactly its guarded publication result.
The endpoint need not coincide with the end of a nominal service block. -/
theorem compiled_resolve_endpoint_extends (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (input : VEnv L Γ₀)
    (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (focal owner : Player) (different : owner ≠ focal)
    (policy : BehavioralPolicy owner whole)
    (players : Player → runtime.application.PlayerPolicy)
    (compiled : players owner = runtime.compilePlayerPolicy whole owner policy)
    (wire : runtime.application.WirePolicy)
    (plan before segment rest : List (ServiceInstruction Player))
    (split : plan = before ++ segment ++ rest)
    (safe : DeviationExpirySafe runtime players (runtime.serviceEnvironment plan wire)
      (some focal) plan (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial whole input))))
    (execution final : runtime.application.PolicyExecution)
    (reached : execution ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment plan wire) (before.map ServiceInstruction.invocation)
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (supported : final ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment plan wire) (segment.map ServiceInstruction.invocation)
      execution).support)
    (outputName bindingName : VarId) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck ((outputName, .pub (R.result payload)) :: Γ)))
    (tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (ideal : VEnv L Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (site clock enteredAt : Nat)
    (atCursor : execution.native.application =
      .running (.resolve outputName owner bindingName fresh source checks tail)
        ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt)
    (disclose : Bool)
    (remembered : rememberedDisclosure (execution.principalHistory owner) site = some disclose)
    (advanced : site < final.native.application.phase) :
    final.native.application.Extends tail
      (VEnv.cons ((R.valueEquiv payload).symm
        (acceptedResult source checks ideal disclose)) ideal) := by
  let environment := runtime.serviceEnvironment plan wire
  let initial := MessageApplication.PolicyExecution.initial runtime.application
    (MessageApplication.State.initial runtime.application (State.initial whole input))
  obtain ⟨pre, instruction, suffix, segmentEq, prior, next, priorRun, nextStep,
      finalRun, priorPhase, changed⟩ :=
    runtime.exists_first_phaseChange_invocation players environment segment execution final
      supported (by simpa only [atCursor, State.phase] using advanced)
  have actualSplit : plan = (before ++ pre) ++ instruction :: (suffix ++ rest) := by
    rw [split, segmentEq]
    simp only [List.append_assoc, List.cons_append]
  have priorReached : prior ∈ (runtime.application.runPolicies players environment
      ((before ++ pre).map ServiceInstruction.invocation) initial).support := by
    rw [List.map_append, runtime.application.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨execution, reached, priorRun⟩
  have priorSite : prior.native.application.phase = site := by
    simpa only [atCursor, State.phase] using priorPhase
  obtain ⟨priorCandidates, priorClock, priorEnteredAt, priorState⟩ :=
    runtime.runPolicies_running_eq_of_phase_eq
      (.resolve outputName owner bindingName fresh source checks tail)
      ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt
      players environment (pre.map ServiceInstruction.invocation) execution prior
      atCursor priorRun priorSite
  have notSample : ¬ prior.native.application.IsSample := by
    simp [priorState, State.IsSample]
  have notFocal : ¬ prior.native.application.IsOwnedBy (some focal) := by
    simpa only [priorState, State.IsOwnedBy, Option.some.injEq] using Ne.symm different
  obtain ⟨id, message, lookup, accepted⟩ := runtime.service_phase_change_accepted players focal
    wire (before ++ pre) (suffix ++ rest) instruction initial prior next rfl
    (by simpa only [← actualSplit, environment, initial] using safe)
    (by simpa only [← actualSplit, environment] using priorReached)
    (by simpa only [← actualSplit, environment] using nextStep) notSample notFocal changed
  obtain ⟨actualDisclose, actualRemembered, afterEq⟩ :=
    runtime.accepted_initial_compiled_resolve_packet whole input unique discipline
      outputName bindingName owner fresh source checks tail policy players compiled environment
      ((before ++ pre).map ServiceInstruction.invocation) prior ideal bindings priorCandidates
      site priorClock priorEnteredAt message id next.native.application priorReached priorState
      lookup accepted
  have rememberedPrior := runtime.runPolicies_rememberedDisclosure_of_some owner site disclose
    players environment (pre.map ServiceInstruction.invocation) execution prior remembered priorRun
  have same : actualDisclose = disclose := Option.some.inj
    (actualRemembered.symm.trans rememberedPrior)
  subst actualDisclose
  have retention : next.native.application.Extends tail
      (VEnv.cons ((R.valueEquiv payload).symm
        (acceptedResult source checks ideal disclose)) ideal) := by
    rw [afterEq]
    exact State.running_extends tail _ _ _ _ _ _ _
  exact runtime.runPolicies_extends tail _ players environment
    (suffix.map ServiceInstruction.invocation) next final retention finalRun

end Vegas.GraphRuntime
