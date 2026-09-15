/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageResolutionLaw
import Vegas.Graph.MessagePhaseFrame
import Vegas.Graph.MessageVerification
import Interaction.MessageApplicationSubmissionOrigin

/-! # Exact acceptance of compiled disclosures

A disclosure packet emitted by the compiled owner keeps its exact graph value
across arbitrary same-phase execution. Candidate preparation may continue, but
an opening that verified when emitted remains verified when it is accepted.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

/-- Once a disclosure marker has been found, later authenticated commands
cannot replace it: histories grow at the right, while `rememberedDisclosure`
selects the first marker for the site. -/
theorem rememberedDisclosure_append_of_some
    {runtime : GraphRuntime Player L Δ} (history extension : List (Entry runtime))
    (site : Nat) (disclose : Bool)
    (remembered : rememberedDisclosure history site = some disclose) :
    rememberedDisclosure (history ++ extension) site = some disclose := by
  unfold rememberedDisclosure at remembered ⊢
  rw [List.findSome?_append, remembered]
  rfl

/-- A cached disclosure remains the current cached value through every shared
policy invocation, independently of the other players and environment. -/
theorem runPolicies_rememberedDisclosure_of_some
    (runtime : GraphRuntime Player L Δ) (who : Player) (site : Nat) (disclose : Bool)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (remembered : rememberedDisclosure (execution.principalHistory who) site = some disclose)
    (supported : next ∈ (runtime.application.runPolicies players environment
      schedule execution).support) :
    rememberedDisclosure (next.principalHistory who) site = some disclose := by
  apply runtime.application.runPolicies_execution_invariant
    (fun current => rememberedDisclosure (current.principalHistory who) site = some disclose)
    players environment
  · intro current actor command after holds _ stepMem
    by_cases same : actor = who
    · subst actor
      rw [runtime.application.playerStep_history_self who current command after stepMem]
      exact rememberedDisclosure_append_of_some _ [_] site disclose holds
    · rw [runtime.application.playerStep_other_history actor who
        (Ne.symm same) current command after stepMem]
      exact holds
  · intro current command after holds _ stepMem
    rw [runtime.application.environmentStep_principalHistory current command after stepMem]
    exact holds
  · exact remembered
  · exact supported

private theorem handle_resolve_sender
    (runtime : GraphRuntime Player L Δ)
    (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ)))
    (tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (site clock enteredAt : Nat) (message : Message Player (Payload Player L))
    (after : State Player L Δ)
    (accepted : runtime.handle
      (.running (.resolve outputName owner bindingName fresh source checks tail)
        ideal values bindings candidates site clock enteredAt) message = some after) :
    message.sender = owner := by
  rcases message with ⟨⟨sender, serial⟩, packet⟩
  cases packet <;> simp only [GraphRuntime.handle, Bool.and_eq_true,
    decide_eq_true_eq, Option.ite_none_right_eq_some] at accepted ⊢
  · contradiction
  · exact accepted.1.1.1.1.2
  · exact accepted.1.2
  · contradiction

private theorem handle_resolve_payload_at_site
    (runtime : GraphRuntime Player L Δ)
    (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ)))
    (tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (site clock enteredAt : Nat) (message : Message Player (Payload Player L))
    (after : State Player L Δ)
    (accepted : runtime.handle
      (.running (.resolve outputName owner bindingName fresh source checks tail)
        ideal values bindings candidates site clock enteredAt) message = some after) :
    (∃ handle raw, message.payload = .opening site handle raw) ∨
      message.payload = .withhold site := by
  rcases message with ⟨id, packet⟩
  cases packet <;> simp only [GraphRuntime.handle, Bool.and_eq_true,
    decide_eq_true_eq, Option.ite_none_right_eq_some] at accepted ⊢
  · contradiction
  · exact Or.inl ⟨_, _, by rw [accepted.1.1.1.1.1]⟩
  · exact Or.inr (by rw [accepted.1.1])
  · contradiction

/-- A supported submit at the current resolve head can only occur after the
compiled owner cached its disclosure decision and before any earlier submit at
that site. -/
theorem compileAt_resolve_submit_cached
    (runtime : GraphRuntime Player L Δ) {origin : VCtx Player L}
    (whole : Graph Player L origin Δ)
    (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ)))
    (tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner
      (.resolve outputName owner bindingName fresh source checks tail))
    (history : List (Entry runtime)) (native : runtime.application.State)
    (ideal : VEnv L Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (site clock enteredAt : Nat) (packet : Payload Player L)
    (application : native.application =
      .running (.resolve outputName owner bindingName fresh source checks tail)
        ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt)
    (supported : (.submit packet : Command runtime) ∈
      (compileAt runtime owner whole
        (.resolve outputName owner bindingName fresh source checks tail) policy site
        history (MessageApplication.State.observe runtime.application native owner)).support) :
    ∃ disclose, rememberedDisclosure history site = some disclose ∧
      submittedAt history site = false := by
  rcases native with ⟨nativeApplication, pool, receipts⟩
  change nativeApplication = _ at application
  subst nativeApplication
  simp only [MessageApplication.State.observe, GraphRuntime.application,
    State.playerView, compileAt] at supported
  split at supported
  · split at supported
    · simp only [FinDist.mem_support_pure] at supported
      contradiction
    · rename_i unsubmitted
      cases remembered : rememberedDisclosure history site with
      | none =>
          rw [remembered] at supported
          rw [FinDist.support_map] at supported
          obtain ⟨disclose, _, impossible⟩ := supported
          contradiction
      | some disclose =>
          exact ⟨disclose, rfl, Bool.eq_false_of_not_eq_true unsubmitted⟩
  · rename_i impossible
    contradiction

/-- If an exact packet supported by the compiled resolve command is accepted
after an arbitrary run that leaves the resolve phase current, it installs the
remembered graph result. This includes `true` disclosures rejected by guards:
their compiled packet is the same failure/withhold transition. -/
theorem accepted_compiled_resolve_packet
    (runtime : GraphRuntime Player L Δ) {origin : VCtx Player L}
    (whole : Graph Player L origin Δ)
    (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ)))
    (tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner
      (.resolve outputName owner bindingName fresh source checks tail))
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (emitted current : runtime.application.PolicyExecution)
    (after : State Player L Δ)
    (ideal : VEnv L Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (site clock enteredAt serial : Nat) (disclose : Bool)
    (packet : Payload Player L)
    (emittedState : emitted.native.application =
      .running (.resolve outputName owner bindingName fresh source checks tail)
        ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt)
    (remembered : rememberedDisclosure (emitted.principalHistory owner) site = some disclose)
    (unsubmitted : submittedAt (emitted.principalHistory owner) site = false)
    (provenance : emitted.native.application.DisciplinedBindingProvenance)
    (compiled : (.submit packet : Command runtime) ∈
      (compileAt runtime owner whole
        (.resolve outputName owner bindingName fresh source checks tail) policy site
        (emitted.principalHistory owner)
        (MessageApplication.State.observe runtime.application emitted.native owner)).support)
    (runSupported : current ∈ (runtime.application.runPolicies players environment
      schedule emitted).support)
    (samePhase : current.native.application.phase = site)
    (accepted : runtime.handle current.native.application
      ({ id := (owner, serial), payload := packet } :
        Message Player runtime.application.Payload) = some after) :
    ∃ candidates' clock' enteredAt',
      current.native.application =
        .running (.resolve outputName owner bindingName fresh source checks tail)
          ideal (PublicValues.ofVEnv ideal) bindings candidates' site clock' enteredAt' ∧
      after = advanceResolve tail ideal (PublicValues.ofVEnv ideal) bindings candidates'
        site clock' (acceptedResult source checks ideal disclose) := by
  obtain ⟨candidates', clock', enteredAt', currentState⟩ :=
    runtime.runPolicies_running_eq_of_phase_eq
      (.resolve outputName owner bindingName fresh source checks tail)
      ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt
      players environment schedule emitted current emittedState runSupported samePhase
  have compiledLaw := compileAt_resolve_result runtime whole outputName bindingName owner
    fresh source checks tail policy (emitted.principalHistory owner) emitted.native
    ideal bindings candidates site clock enteredAt disclose emittedState remembered unsubmitted
  rw [compiledLaw] at compiled
  simp only [FinDist.mem_support_pure] at compiled
  have packetCommand : (.submit packet : Command runtime) =
      runtime.disclosureCommand site bindingName bindings
        (acceptedResult source checks ideal disclose) := compiled
  refine ⟨candidates', clock', enteredAt', currentState, ?_⟩
  cases result : acceptedResult source checks ideal disclose with
  | failure =>
      simp only [result, disclosureCommand] at packetCommand
      injection packetCommand with packetEq
      subst packet
      rw [currentState] at accepted
      simp only [GraphRuntime.handle, decide_true, Bool.true_and, decide_eq_true_eq,
        Option.ite_none_right_eq_some, Option.some.injEq] at accepted
      exact accepted.2.symm
  | success value =>
      simp only [result, disclosureCommand] at packetCommand
      cases binding : lookupBinding bindings bindingName with
      | none =>
          rw [binding] at packetCommand
          contradiction
      | some handle =>
          rw [binding] at packetCommand
          injection packetCommand with packetEq
          subst packet
          obtain ⟨discloseEq, encoded⟩ :=
            acceptedResult_success source checks ideal disclose value result
          subst disclose
          have decoded : R.valueEquiv payload (ideal.get source) = .success value := by
            rw [encoded, Equiv.apply_symm_apply]
          obtain ⟨sourceHandle, sourceBinding, ownerEq, verified⟩ :=
            State.resolveSource_verified fresh source checks tail ideal
              (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt decoded
              (emittedState ▸ provenance)
          have handleEq : sourceHandle = handle := by
            rw [binding] at sourceBinding
            exact (Option.some.inj sourceBinding).symm
          subst sourceHandle
          have emittedVerified : emitted.native.application.candidates.verify handle
              ⟨R.result payload, ideal.get source⟩ = true := by
            rw [emittedState]
            exact verified
          have stillVerified := runtime.runPolicies_preserves_verification handle
            ⟨R.result payload, ideal.get source⟩ players environment schedule
            emitted current emittedVerified runSupported
          rw [← encoded] at accepted
          rw [currentState] at stillVerified accepted
          have exactAcceptance := runtime.handle_resolve_verified fresh source checks tail
            ideal bindings candidates' site clock' enteredAt' serial handle
            (ideal.get source) binding ownerEq stillVerified rfl
          rw [result] at exactAcceptance
          exact Option.some.inj (accepted.symm.trans exactAcceptance)

/-- Every packet accepted at a current resolve node in an actual supported run
from initialization was emitted by the compiled owner at that same typed graph
cursor. Consequently acceptance installs exactly the owner's cached resolve
result, and that cache is still present in the accepting execution. -/
theorem accepted_initial_compiled_resolve_packet
    (runtime : GraphRuntime Player L Δ) {origin : VCtx Player L}
    (whole : Graph Player L origin Δ) (input : VEnv L origin)
    (unique : (origin.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline Graph.BindingOrigins.none)
    (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ)))
    (tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner whole)
    (players : Player → runtime.application.PlayerPolicy)
    (compiledOwner : players owner = runtime.compilePlayerPolicy whole owner policy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (current : runtime.application.PolicyExecution)
    (ideal : VEnv L Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (site clock enteredAt : Nat) (message : Message Player (Payload Player L))
    (id : MessageId Player)
    (after : State Player L Δ)
    (supported : current ∈ (runtime.application.runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (currentState : current.native.application =
      .running (.resolve outputName owner bindingName fresh source checks tail)
        ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt)
    (lookup : current.native.pool.lookup id = some message)
    (accepted : runtime.handle current.native.application message = some after) :
    ∃ disclose,
      rememberedDisclosure (current.principalHistory owner) site = some disclose ∧
      after = advanceResolve tail ideal (PublicValues.ofVEnv ideal) bindings candidates
        site clock (acceptedResult source checks ideal disclose) := by
  have acceptedExact : runtime.handle
      (.running (.resolve outputName owner bindingName fresh source checks tail)
        ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt)
      message = some after := by
    rw [← currentState]
    exact accepted
  have senderEq := handle_resolve_sender runtime outputName bindingName owner fresh source checks
    tail ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt message after
    acceptedExact
  have payloadAt := handle_resolve_payload_at_site runtime outputName bindingName owner fresh source
    checks tail ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt message
    after acceptedExact
  rcases message with ⟨⟨sender, serial⟩, packet⟩
  change sender = owner at senderEq
  subst sender
  have pending : ({ id := (owner, serial), payload := packet } :
      Message Player (Payload Player L)) ∈ current.native.pool.pending :=
    List.mem_of_find?_eq_some lookup
  obtain ⟨front, suffix, before, submitted, splitSchedule, beforeMem, commandMem,
      stepMem, idEq, residual⟩ :=
    runtime.application.runPolicies_initial_pending_submission_origin players environment schedule
      (State.initial whole input) current supported _ pending
  change (.submit packet : Command runtime) ∈
    (players owner (before.principalHistory owner)
      (MessageApplication.State.observe runtime.application before.native owner)).support
    at commandMem
  change submitted ∈ (runtime.application.playerStep owner before (.submit packet)).support
    at stepMem
  have beforeAtPhase := runtime.compilePlayerPolicy_command_atPhase whole owner policy
    (before.principalHistory owner)
    (MessageApplication.State.observe runtime.application before.native owner)
    (.submit packet) (by simpa [compiledOwner] using commandMem)
  have beforePhase : before.native.application.phase = site := by
    rcases payloadAt with ⟨handle, raw, packetEq⟩ | packetEq
    · change packet = .opening site handle raw at packetEq
      subst packet
      change site = before.native.application.phase at beforeAtPhase
      exact beforeAtPhase.symm
    · change packet = .withhold site at packetEq
      subst packet
      change site = before.native.application.phase at beforeAtPhase
      exact beforeAtPhase.symm
  have fromBefore : current ∈ (runtime.application.runPolicies players environment
      (.player owner :: suffix) before).support := by
    simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion]
    refine ⟨submitted, ?_, residual⟩
    simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion]
    exact ⟨.submit packet, by simpa using commandMem, stepMem⟩
  obtain ⟨beforeCandidates, beforeClock, beforeEnteredAt, beforeState⟩ :=
    runtime.runPolicies_running_before_of_phase_eq
      (.resolve outputName owner bindingName fresh source checks tail)
      ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt
      players environment (.player owner :: suffix) before current currentState fromBefore
      beforePhase
  have follows := runtime.runPolicies_follows whole 0 players environment schedule _ current
    (State.initial_follows whole input) supported
  have exactFollows : (State.running
      (.resolve outputName owner bindingName fresh source checks tail)
      ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt).Follows whole 0 :=
    currentState ▸ follows
  obtain ⟨walk⟩ := State.prefix_of_running_follows whole
    (.resolve outputName owner bindingName fresh source checks tail)
    ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt exactFollows
  have localCommand : (.submit packet : Command runtime) ∈
      (compileAt runtime owner whole
        (.resolve outputName owner bindingName fresh source checks tail)
        (walk.policyTail owner policy) site (before.principalHistory owner)
        (MessageApplication.State.observe runtime.application before.native owner)).support := by
    rw [← walk.compilePlayerPolicy_eq_suffix owner policy]
    · simpa [compiledOwner] using commandMem
    · change before.native.application.phase = site
      exact beforePhase
  obtain ⟨disclose, rememberedBefore, unsubmitted⟩ :=
    compileAt_resolve_submit_cached runtime whole outputName bindingName owner fresh source checks
      tail (walk.policyTail owner policy) (before.principalHistory owner) before.native ideal
      bindings beforeCandidates site beforeClock beforeEnteredAt packet beforeState localCommand
  have provenanceBefore := runtime.runPolicies_initial_disciplinedBindingProvenance whole input
    unique discipline players environment front before beforeMem
  obtain ⟨currentCandidates, currentClock, currentEnteredAt, currentFrame, afterEq⟩ :=
    accepted_compiled_resolve_packet runtime whole outputName bindingName owner fresh source checks
      tail (walk.policyTail owner policy) players environment (.player owner :: suffix) before
      current
      after ideal bindings beforeCandidates site beforeClock beforeEnteredAt serial disclose packet
      beforeState rememberedBefore unsubmitted provenanceBefore localCommand fromBefore
      (by rw [currentState]; rfl) accepted
  have cached := runPolicies_rememberedDisclosure_of_some runtime owner site disclose players
    environment (.player owner :: suffix) before current rememberedBefore fromBefore
  rw [currentState] at currentFrame
  injection currentFrame with _ _ _ _ candidatesEq _ clockEq _
  subst currentCandidates
  subst currentClock
  exact ⟨disclose, cached, afterEq⟩

end Vegas.GraphRuntime
