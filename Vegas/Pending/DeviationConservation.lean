/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.DeviationEnvironmentConservation

/-! # Conservation laws for one native deviation -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- At a typed cursor, the sanitized continuation is the ordinary graph
continuation of the execution with only focal bookkeeping erased. The focal
logical prefix reconstructed from immutable observations is harmless exactly
because the extracted policy ignores that prefix. -/
theorem deviationContinuationAt_eq_erased (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (profile : BehavioralProfile whole)
    (focal : Player) (independent : IgnoresOwnHistory whole profile focal)
    (execution : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows whole 0)
    (suffix : Graph Player L Γ Δ) (site : Nat) (walk : Prefix Δ whole suffix site)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (clock enteredAt : Nat)
    (atCursor : execution.native.application =
      .running suffix ideal values bindings candidates site clock enteredAt) :
    deviationContinuationAt runtime whole profile focal execution.principalHistory
        execution.native.application follows =
      let erased := eraseFocalExecution runtime focal execution
      continuation runtime suffix (walk.profileTail profile) site ideal
        (fun who => projectLogicalHistory who (observe who ideal)
          (erased.principalHistory who) whole 0 site)
        erased.principalHistory := by
  rw [runtime.deviationContinuationAt_running whole profile focal execution follows
    suffix site walk ideal values bindings candidates clock enteredAt atCursor]
  apply runtime.continuation_congr_focal_logical suffix (walk.profileTail profile) focal
    (walk.policyTail_ignoresOwnHistory profile focal independent) site ideal
  · intro who whoNe
    simp [eraseFocalLogical, eraseFocalExecution, eraseFocalHistory, whoNe]
  · simp [eraseFocalHistory]

/-- Invoking a compiled nonfocal player preserves the deviation continuation.
The existing compiler law is applied to the execution with focal bookkeeping
erased; history independence identifies its reconstructed focal logical prefix
with the deliberately empty prefix used by `deviationContinuationAt`. -/
theorem deviationContinuationAt_compiled_nonfocal_player_invoke
    (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (profile : BehavioralProfile whole)
    (focal actor : Player) (different : actor ≠ focal)
    (independent : IgnoresOwnHistory whole profile focal)
    (execution : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows whole 0)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (compiled : players actor = runtime.compilePlayerPolicy whole actor (profile actor)) :
    deviationContinuationAt runtime whole profile focal execution.principalHistory
        execution.native.application follows =
      (runtime.application.invoke players environment execution (.player actor)).bindOnSupport
        fun after supported => deviationContinuationAt runtime whole profile focal
          after.principalHistory after.native.application
          (runtime.invoke_follows whole 0 players environment (.player actor)
            execution after follows supported) := by
  obtain ⟨target, suffix, site, ideal, values, bindings, candidates, clock, enteredAt,
      walk, atCursor⟩ := (show execution.native.application.Follows whole 0 from follows)
  simp only [Nat.zero_add] at atCursor
  let cleaned := eraseFocalExecution runtime focal execution
  have cleanedCursor : cleaned.native.application =
      .running suffix ideal values bindings candidates site clock enteredAt := atCursor
  have residualIndependent := walk.policyTail_ignoresOwnHistory profile focal independent
  let cleanedLogical : History Player L := fun who =>
    projectLogicalHistory who (observe who ideal) (cleaned.principalHistory who) whole 0 site
  have initialLaw : deviationContinuationAt runtime whole profile focal
      execution.principalHistory execution.native.application follows =
      continuation runtime suffix (walk.profileTail profile) site ideal cleanedLogical
        cleaned.principalHistory := by
    rw [runtime.deviationContinuationAt_running whole profile focal execution follows
      suffix site walk ideal values bindings candidates clock enteredAt atCursor]
    apply runtime.continuation_congr_focal_logical suffix (walk.profileTail profile) focal
      residualIndependent site ideal
    · intro who whoNe
      simp [cleanedLogical, cleaned, eraseFocalLogical, eraseFocalExecution,
        eraseFocalHistory, whoNe]
    · simp [eraseFocalHistory]
  rw [initialLaw]
  rw [runtime.continuation_compiled_player_invoke whole profile suffix site walk ideal values
    bindings candidates clock enteredAt cleaned cleanedCursor players environment actor compiled]
  rw [← runtime.invoke_eraseFocalExecution_of_ne focal actor different players environment
    execution]
  rw [FinDist.bind_map]
  symm
  apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
  intro after supported
  have stepSupport := supported
  simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at stepSupport
  obtain ⟨command, _commandMem, stepMem⟩ := stepSupport
  have phase := runtime.playerStep_phase actor execution after command stepMem
  rw [atCursor] at phase
  have runMem : after ∈ (runtime.application.runPolicies players environment
      [.player actor] execution).support := by
    simpa [MessageApplication.runPolicies] using supported
  obtain ⟨candidates', clock', enteredAt', atNext⟩ :=
    runtime.runPolicies_running_eq_of_phase_eq suffix ideal values bindings candidates
      site clock enteredAt players environment [.player actor] execution after
      atCursor runMem phase
  have erasedCursor : (eraseFocalExecution runtime focal after).native.application =
      .running suffix ideal values bindings candidates' site clock' enteredAt' := atNext
  rw [runtime.deviationContinuationAt_running whole profile focal after _ suffix site walk
    ideal values bindings candidates' clock' enteredAt' atNext]
  let erased := eraseFocalExecution runtime focal after
  let projected : History Player L := fun who =>
    projectLogicalHistory who (observe who ideal) (erased.principalHistory who) whole 0 site
  apply runtime.continuation_congr_focal_logical suffix (walk.profileTail profile) focal
    residualIndependent site ideal
  · intro who whoNe
    simp [eraseFocalLogical, eraseFocalExecution, eraseFocalHistory, whoNe]
  · simp [eraseFocalHistory]

/-- Pointwise conservation for the concrete environment instructions lifts
with no further interpreter to the entire shared policy run. Player steps are
fully discharged here: the focal policy is arbitrary, while every nonfocal
invoked policy is the graph compiler. Thus callers only supply the genuinely
semantic wire/include/expiry transition laws. -/
theorem runPolicies_deviationContinuation_of_environment
    (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (profile : BehavioralProfile whole)
    (focal : Player) (independent : IgnoresOwnHistory whole profile focal)
    (players : Player → runtime.application.PlayerPolicy)
    (compiled : ∀ actor, actor ≠ focal →
      players actor = runtime.compilePlayerPolicy whole actor (profile actor))
    (environment : runtime.application.EnvironmentPolicy)
    (plan : List (ServiceInstruction Player))
    (initial : runtime.application.PolicyExecution)
    (initialFollows : initial.native.application.Follows whole 0)
    (environmentLaw : ∀ before instruction after,
      plan = before ++ instruction :: after →
      instruction.invocation = .environment →
      ∀ execution, execution ∈ (runtime.application.runPolicies players environment
        (before.map ServiceInstruction.invocation) initial).support →
      ∀ follows : execution.native.application.Follows whole 0,
        (runtime.application.invoke players environment execution .environment).bindOnSupport
            (fun next supported => deviationContinuationAt runtime whole profile focal
              next.principalHistory next.native.application
              (runtime.invoke_follows whole 0 players environment .environment
                execution next follows supported)) =
          deviationContinuationAt runtime whole profile focal execution.principalHistory
            execution.native.application follows) :
    (runtime.application.runPolicies players environment
      (plan.map ServiceInstruction.invocation) initial).bindOnSupport
        (fun execution supported => deviationContinuationAt runtime whole profile focal
          execution.principalHistory execution.native.application
          (runtime.runPolicies_follows whole 0 players environment _ initial execution
            initialFollows supported)) =
      deviationContinuationAt runtime whole profile focal initial.principalHistory
        initial.native.application initialFollows := by
  apply runtime.application.runPolicies_map_bindOnSupport_conservation
    ServiceInstruction.invocation plan
    (fun execution => execution.native.application.Follows whole 0)
    (fun execution follows => deviationContinuationAt runtime whole profile focal
      execution.principalHistory execution.native.application follows)
    players environment initial initialFollows
    (fun instruction execution follows next supported => runtime.invoke_follows whole 0
      players environment instruction.invocation execution next follows supported)
  intro before instruction after split execution reached follows
  cases instruction with
  | player actor =>
      symm
      by_cases same : actor = focal
      · subst actor
        exact runtime.deviationContinuationAt_focal_player_invoke whole profile focal execution
          follows players environment
      · exact runtime.deviationContinuationAt_compiled_nonfocal_player_invoke whole profile
          focal actor same independent execution follows players environment (compiled actor same)
  | wire => exact environmentLaw before .wire after split rfl execution reached follows
  | includeLatest owner =>
      exact environmentLaw before (.includeLatest owner) after split rfl execution reached follows
  | expire phase =>
      exact environmentLaw before (.expire phase) after split rfl execution reached follows

/-- A concrete wire command at a prepared nonfocal bind cursor conserves the
deviation continuation.  Authorship and preparation are taken from the actual
mixed execution; only the proof-side continuation erases the focal transcript. -/
theorem Prefix.deviationContinuationAt_bind_wireStep
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (focal : Player)
    (independent : IgnoresOwnHistory whole profile focal)
    (site : Nat) (name : VarId) (owner : Player) (ownerNe : owner ≠ focal)
    {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (tail : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (walk : Prefix Δ whole (.bind name owner fresh tail) site)
    (execution after : runtime.application.PolicyExecution)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (clock enteredAt : Nat) (encoded : L.Val (R.result payload))
    (atCursor : execution.native.application =
      .running (.bind name owner fresh tail) ideal values bindings candidates
        site clock enteredAt)
    (follows : execution.native.application.Follows whole 0)
    (invariant : PreparationInvariant runtime owner execution)
    (prepared : preparedRaw (execution.principalHistory owner) site =
      some ⟨R.result payload, encoded⟩)
    (unique : (Γ.map Prod.fst).Nodup) (command : WireCommand Player)
    (supported : after ∈ (runtime.application.environmentPolicyStep execution
      (command.toEnvironmentCommand runtime.application)).support)
    (afterFollows : after.native.application.Follows whole 0) :
    deviationContinuationAt runtime whole profile focal after.principalHistory
        after.native.application afterFollows =
      deviationContinuationAt runtime whole profile focal execution.principalHistory
        execution.native.application follows := by
  have histories := runtime.application.environmentStep_principalHistory execution
    (command.toEnvironmentCommand runtime.application) after supported
  have erasedHistories :
      (eraseFocalExecution runtime focal after).principalHistory =
        (eraseFocalExecution runtime focal execution).principalHistory := by
    exact congrArg (eraseFocalHistory focal) histories
  rcases runtime.wireStep_bind_classify name owner fresh tail execution after ideal values
      bindings candidates site clock enteredAt encoded atCursor invariant prepared command
      supported with stutter | advanced
  · rw [runtime.deviationContinuationAt_eq_erased whole profile focal independent after
      afterFollows (.bind name owner fresh tail) site walk ideal values bindings candidates clock
      enteredAt (stutter.trans atCursor)]
    rw [runtime.deviationContinuationAt_eq_erased whole profile focal independent execution
      follows (.bind name owner fresh tail) site walk ideal values bindings candidates clock
      enteredAt atCursor]
    dsimp only
    rw [erasedHistories]
  · rw [runtime.deviationContinuationAt_eq_erased whole profile focal independent after
      afterFollows tail (site + 1) (walk.trans (.bind (.refl tail)))
      (VEnv.cons encoded ideal) (PublicValues.consSealed values)
      ((name, (owner, .prepared site)) :: bindings)
      (candidates.accept (owner, .prepared site)) clock clock advanced]
    rw [runtime.deviationContinuationAt_eq_erased whole profile focal independent execution
      follows (.bind name owner fresh tail) site walk ideal values bindings candidates clock
      enteredAt atCursor]
    dsimp only
    rw [erasedHistories]
    have cached : preparedChoice
        ((eraseFocalExecution runtime focal execution).principalHistory owner) site payload =
        some (R.valueEquiv payload encoded) := by
      rw [eraseFocalExecution_history_of_ne runtime focal owner ownerNe execution]
      simp [preparedChoice, prepared]
    simpa using
      (walk.continuation_bind_advance runtime whole profile site name owner fresh tail ideal
        (eraseFocalExecution runtime focal execution).principalHistory
        (R.valueEquiv payload encoded) cached unique).symm

/-- Direct accepted-packet form of the preceding bind law, suitable as the
accepted branch of `deviationContinuationAt_wire`. -/
theorem Prefix.deviationContinuationAt_bind_accepted
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (focal : Player)
    (independent : IgnoresOwnHistory whole profile focal)
    (site : Nat) (name : VarId) (owner : Player) (ownerNe : owner ≠ focal)
    {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (tail : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (walk : Prefix Δ whole (.bind name owner fresh tail) site)
    (execution : runtime.application.PolicyExecution)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (clock enteredAt : Nat) (encoded : L.Val (R.result payload))
    (atCursor : execution.native.application =
      .running (.bind name owner fresh tail) ideal values bindings candidates
        site clock enteredAt)
    (follows : execution.native.application.Follows whole 0)
    (invariant : PreparationInvariant runtime owner execution)
    (prepared : preparedRaw (execution.principalHistory owner) site =
      some ⟨R.result payload, encoded⟩)
    (unique : (Γ.map Prod.fst).Nodup) (id : MessageId Player)
    (message : Message Player (Payload Player L)) (after : State Player L Δ)
    (lookup : execution.native.pool.lookup id = some message)
    (accepted : runtime.handle execution.native.application message = some after) :
    deviationContinuationAt runtime whole profile focal execution.principalHistory after
        (runtime.handle_follows whole 0 execution.native.application after message follows
          accepted) =
      deviationContinuationAt runtime whole profile focal execution.principalHistory
        execution.native.application follows := by
  obtain ⟨_, advanced⟩ := runtime.accepted_bind_installs_prepared_choice name owner fresh tail
    execution ideal values bindings candidates site clock enteredAt encoded message id after
    atCursor invariant prepared lookup accepted
  let successor : runtime.application.PolicyExecution :=
    { execution with native := { execution.native with application := after } }
  have afterFollows := runtime.handle_follows whole 0 execution.native.application after
    message follows accepted
  change deviationContinuationAt runtime whole profile focal successor.principalHistory
      successor.native.application afterFollows = _
  rw [runtime.deviationContinuationAt_eq_erased whole profile focal independent successor
    afterFollows tail (site + 1) (walk.trans (.bind (.refl tail)))
    (VEnv.cons encoded ideal) (PublicValues.consSealed values)
    ((name, (owner, .prepared site)) :: bindings)
    (candidates.accept (owner, .prepared site)) clock clock advanced]
  rw [runtime.deviationContinuationAt_eq_erased whole profile focal independent execution follows
    (.bind name owner fresh tail) site walk ideal values bindings candidates clock enteredAt
    atCursor]
  dsimp only [successor, eraseFocalExecution]
  have cached : preparedChoice
      (eraseFocalHistory focal execution.principalHistory owner) site payload =
      some (R.valueEquiv payload encoded) := by
    rw [eraseFocalHistory_of_ne focal owner ownerNe]
    simp [preparedChoice, prepared]
  simpa using
    (walk.continuation_bind_advance runtime whole profile site name owner fresh tail ideal
      (eraseFocalHistory focal execution.principalHistory) (R.valueEquiv payload encoded)
      cached unique).symm

/-- In an actual initialized mixed run, every packet accepted at a nonfocal
bind cursor conserves the sanitized continuation; preparation and its exact
type are derived rather than assumed by the caller. -/
theorem Prefix.deviationContinuationAt_bind_accepted_initialized
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (input : VEnv L Γ₀)
    (focal : Player) (independent : IgnoresOwnHistory whole profile focal)
    (site : Nat) (name : VarId) (owner : Player) (ownerNe : owner ≠ focal)
    {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (tail : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (walk : Prefix Δ whole (.bind name owner fresh tail) site)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy whole owner (profile owner))
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution : runtime.application.PolicyExecution)
    (reached : execution ∈ (runtime.application.runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (clock enteredAt : Nat)
    (atCursor : execution.native.application =
      .running (.bind name owner fresh tail) ideal values bindings candidates
        site clock enteredAt)
    (follows : execution.native.application.Follows whole 0)
    (unique : (Γ.map Prod.fst).Nodup) (id : MessageId Player)
    (message : Message Player (Payload Player L)) (after : State Player L Δ)
    (lookup : execution.native.pool.lookup id = some message)
    (accepted : runtime.handle execution.native.application message = some after) :
    deviationContinuationAt runtime whole profile focal execution.principalHistory after
        (runtime.handle_follows whole 0 execution.native.application after message follows
          accepted) =
      deviationContinuationAt runtime whole profile focal execution.principalHistory
        execution.native.application follows := by
  have invariant := runtime.runPolicies_initial_preparationInvariant whole input owner
    (profile owner) players ownerCompiled environment schedule execution reached
  cases cached : preparedRaw (execution.principalHistory owner) site with
  | some raw =>
      obtain ⟨encoded, rfl⟩ := runtime.preparedRaw_typed_of_initialized_bind whole profile site
        name owner fresh tail walk input environment players ownerCompiled schedule execution
        reached ideal values bindings candidates clock enteredAt atCursor raw cached
      exact walk.deviationContinuationAt_bind_accepted runtime whole profile focal independent
        site name owner ownerNe fresh tail execution ideal values bindings candidates clock
        enteredAt encoded atCursor follows invariant cached unique id message after lookup accepted
  | none =>
      exfalso
      rcases invariant with ⟨authorship, _agreement, commitments⟩
      cases message with
      | mk messageId packet =>
        cases packet with
        | opening packetSite handle raw => simp [GraphRuntime.handle, atCursor] at accepted
        | withhold packetSite => simp [GraphRuntime.handle, atCursor] at accepted
        | malformed raw => simp [GraphRuntime.handle, atCursor] at accepted
        | commitment packetSite handle =>
            have acceptedOriginal := accepted
            simp only [GraphRuntime.handle, atCursor] at accepted
            split at accepted
            · rename_i conditions
              simp only [Bool.and_eq_true, decide_eq_true_eq] at conditions
              obtain ⟨⟨siteEq, senderEq⟩, handleOwner⟩ := conditions
              subst packetSite
              have sender : messageId.1 = owner := senderEq
              have safe := authorship.2.1
                ({ id := messageId, payload := .commitment site handle } :
                  Message Player (Payload Player L))
                (List.mem_of_find?_eq_some lookup)
              have submitted : (.commitment site handle : Payload Player L) ∈
                  runtime.application.submittedPayloads
                    (execution.principalHistory owner) := by
                change (runtime.application.submittedPayloads
                  (execution.principalHistory messageId.1))[messageId.2]? =
                    some (.commitment site handle) at safe
                rw [sender] at safe
                rw [List.getElem?_eq_some_iff] at safe
                rw [List.mem_iff_getElem]
                exact ⟨messageId.2, safe.1, safe.2⟩
              obtain ⟨canonical, _, _⟩ := commitments site handle submitted
              have sameHandle : handle = (owner, .prepared site) := by
                simpa using canonical
              obtain ⟨raw, prepared⟩ := runtime.accepted_commitment_was_prepared owner execution
                authorship commitments ⟨messageId, .commitment site handle⟩ after id site site
                handle lookup rfl acceptedOriginal sameHandle
              rw [cached] at prepared
              contradiction
            · contradiction

/-- Acceptance of an authenticated packet at a nonfocal resolve cursor has
the exact sanitized graph advancement. The remembered disclosure and accepted
value are reconstructed from the actual initialized mixed execution. -/
theorem Prefix.deviationContinuationAt_resolve_accepted
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (input : VEnv L Γ₀)
    (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (focal : Player) (independent : IgnoresOwnHistory whole profile focal)
    (site : Nat) (outputName bindingName : VarId) (owner : Player)
    (ownerNe : owner ≠ focal) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck ((outputName, .pub (R.result payload)) :: Γ)))
    (tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (walk : Prefix Δ whole
      (.resolve outputName owner bindingName fresh source checks tail) site)
    (execution : runtime.application.PolicyExecution) (ideal : VEnv L Γ)
    (bindings : Bindings Player) (candidates : CommitmentCandidates Player Slot (Raw L))
    (clock enteredAt : Nat)
    (atCursor : execution.native.application =
      .running (.resolve outputName owner bindingName fresh source checks tail)
        ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt)
    (follows : execution.native.application.Follows whole 0)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy whole owner (profile owner))
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (reached : execution ∈ (runtime.application.runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (id : MessageId Player) (message : Message Player (Payload Player L))
    (after : State Player L Δ) (lookup : execution.native.pool.lookup id = some message)
    (accepted : runtime.handle execution.native.application message = some after) :
    deviationContinuationAt runtime whole profile focal execution.principalHistory after
        (runtime.handle_follows whole 0 execution.native.application after message follows
          accepted) =
      deviationContinuationAt runtime whole profile focal execution.principalHistory
        execution.native.application follows := by
  obtain ⟨disclose, remembered, advanced⟩ :=
    runtime.accepted_initial_compiled_resolve_packet whole input unique discipline
      outputName bindingName owner fresh source checks tail (profile owner) players ownerCompiled
      environment schedule execution ideal bindings candidates site clock enteredAt message id
      after reached atCursor lookup accepted
  let successor : runtime.application.PolicyExecution :=
    { execution with native := { execution.native with application := after } }
  have afterFollows := runtime.handle_follows whole 0 execution.native.application after
    message follows accepted
  change deviationContinuationAt runtime whole profile focal successor.principalHistory
      successor.native.application afterFollows = _
  rw [runtime.deviationContinuationAt_eq_erased whole profile focal independent successor
    afterFollows tail (site + 1) (walk.trans (.resolve (.refl tail)))
    (VEnv.cons ((R.valueEquiv payload).symm
      (acceptedResult source checks ideal disclose)) ideal)
    (PublicValues.consPublic ((R.valueEquiv payload).symm
      (acceptedResult source checks ideal disclose)) (PublicValues.ofVEnv ideal))
    bindings candidates clock clock advanced]
  rw [runtime.deviationContinuationAt_eq_erased whole profile focal independent execution follows
    (.resolve outputName owner bindingName fresh source checks tail) site walk ideal
    (PublicValues.ofVEnv ideal) bindings candidates clock enteredAt atCursor]
  dsimp only [successor, eraseFocalExecution]
  have cached : rememberedDisclosure
      (eraseFocalHistory focal execution.principalHistory owner) site = some disclose := by
    rw [eraseFocalHistory_of_ne focal owner ownerNe]
    exact remembered
  exact (walk.continuation_resolve_advance runtime whole profile site outputName bindingName owner
    fresh source checks tail ideal (eraseFocalHistory focal execution.principalHistory)
    disclose cached (walk.target_names_nodup unique)).symm

/-- An arbitrary wire invocation at a cursor not owned by the focal deviator
preserves the sanitized continuation. Every accepted packet is discharged by
the initialized bind/resolve provenance laws above. -/
theorem deviationContinuationAt_initialized_wire_nonfocal
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (input : VEnv L Γ₀)
    (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (focal : Player) (independent : IgnoresOwnHistory whole profile focal)
    (players : Player → runtime.application.PlayerPolicy)
    (compiled : ∀ owner, owner ≠ focal →
      players owner = runtime.compilePlayerPolicy whole owner (profile owner))
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution : runtime.application.PolicyExecution)
    (reached : execution ∈ (runtime.application.runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (notFocal : ¬ execution.native.application.IsOwnedBy (some focal))
    (wire : runtime.application.WirePolicy) :
    let follows := runtime.runPolicies_follows whole 0 players environment schedule _ execution
      (State.initial_follows whole input) reached
    deviationContinuationAt runtime whole profile focal execution.principalHistory
        execution.native.application follows =
      (runtime.application.invoke players (runtime.application.wireEnvironment wire)
        execution .environment).bindOnSupport fun after supported =>
          deviationContinuationAt runtime whole profile focal after.principalHistory
            after.native.application
            (runtime.invoke_follows whole 0 players
              (runtime.application.wireEnvironment wire) .environment execution after follows
              supported) := by
  dsimp only
  have follows := runtime.runPolicies_follows whole 0 players environment schedule _ execution
    (State.initial_follows whole input) reached
  have agreement := runtime.runPolicies_preserves_publicAgreement players environment schedule _
    execution (State.initial_publicAgreement whole input) reached
  obtain ⟨target, suffix, site, ideal, values, bindings, candidates, clock, enteredAt,
      walk, atCursor⟩ := (show execution.native.application.Follows whole 0 from follows)
  simp only [Nat.zero_add] at atCursor
  rw [atCursor] at agreement
  change (values : PublicValues target) = (PublicValues.ofVEnv ideal : PublicValues target)
    at agreement
  rw [agreement] at atCursor
  cases suffix with
  | ret output =>
      apply runtime.deviationContinuationAt_wire whole profile focal execution follows players wire
      intro id message next lookup accepted
      simp [atCursor, GraphRuntime.handle] at accepted
  | sample name fresh law tail =>
      apply runtime.deviationContinuationAt_wire whole profile focal execution follows players wire
      intro id message next lookup accepted
      simp [atCursor, GraphRuntime.handle] at accepted
  | bind name owner fresh tail =>
      have ownerNe : owner ≠ focal := by
        intro same
        subst owner
        apply notFocal
        simp [State.IsOwnedBy, atCursor]
      apply runtime.deviationContinuationAt_wire whole profile focal execution follows players wire
      intro id message next lookup accepted
      exact walk.deviationContinuationAt_bind_accepted_initialized runtime whole profile input
        focal independent site name owner ownerNe fresh tail players (compiled owner ownerNe)
        environment schedule execution reached ideal (PublicValues.ofVEnv ideal) bindings candidates
        clock enteredAt atCursor follows (walk.target_names_nodup unique) id message next lookup
        accepted
  | resolve outputName owner bindingName fresh source checks tail =>
      have ownerNe : owner ≠ focal := by
        intro same
        subst owner
        apply notFocal
        simp [State.IsOwnedBy, atCursor]
      apply runtime.deviationContinuationAt_wire whole profile focal execution follows players wire
      intro id message next lookup accepted
      exact walk.deviationContinuationAt_resolve_accepted runtime whole profile input unique
        discipline focal independent site outputName bindingName owner ownerNe fresh source checks
        tail execution ideal bindings candidates clock enteredAt atCursor follows players
        (compiled owner ownerNe) environment schedule reached id message next lookup accepted

/-- Initialized probability-law specialization of the finite-run conservation
theorem. Once the concrete environment branches are supplied, the real shared
message execution has exactly the extracted graph policy's residual law. -/
theorem runPolicies_deviation_law_of_environment
    (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (profile : BehavioralProfile whole)
    (focal : Player) (independent : IgnoresOwnHistory whole profile focal)
    (input : VEnv L Γ₀) (players : Player → runtime.application.PlayerPolicy)
    (compiled : ∀ actor, actor ≠ focal →
      players actor = runtime.compilePlayerPolicy whole actor (profile actor))
    (environment : runtime.application.EnvironmentPolicy)
    (plan : List (ServiceInstruction Player))
    (environmentLaw : ∀ before instruction after,
      plan = before ++ instruction :: after →
      instruction.invocation = .environment →
      ∀ execution, execution ∈ (runtime.application.runPolicies players environment
        (before.map ServiceInstruction.invocation)
        (MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application
            (State.initial whole input)))).support →
      ∀ follows : execution.native.application.Follows whole 0,
        (runtime.application.invoke players environment execution .environment).bindOnSupport
            (fun next supported => deviationContinuationAt runtime whole profile focal
              next.principalHistory next.native.application
              (runtime.invoke_follows whole 0 players environment .environment
                execution next follows supported)) =
          deviationContinuationAt runtime whole profile focal execution.principalHistory
            execution.native.application follows) :
    let initial := MessageApplication.PolicyExecution.initial runtime.application
      (MessageApplication.State.initial runtime.application (State.initial whole input))
    (runtime.application.runPolicies players environment
      (plan.map ServiceInstruction.invocation) initial).bindOnSupport
        (fun execution supported => deviationContinuationAt runtime whole profile focal
          execution.principalHistory execution.native.application
          (runtime.runPolicies_follows whole 0 players environment _ initial execution
            (State.initial_follows whole input) supported)) =
      Graph.run whole profile input := by
  dsimp only
  rw [runtime.runPolicies_deviationContinuation_of_environment whole profile focal independent
    players compiled environment plan _ (State.initial_follows whole input) environmentLaw]
  exact runtime.deviationContinuationAt_initial whole profile focal input

end Vegas.GraphRuntime

/-- info: 'Vegas.GraphRuntime.runPolicies_deviation_law_of_environment' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.GraphRuntime.runPolicies_deviation_law_of_environment
