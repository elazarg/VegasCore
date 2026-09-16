/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.BindingAcceptance
import Vegas.Pending.ContinuationAt
import Vegas.Pending.ContinuationStep
import Interaction.MessageApplicationWirePolicy
import Interaction.MessageApplicationSubmissionOrigin

/-! # Continuation laws for wire invocations -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- In an actual initialized execution, a cached preparation at the current
compiled bind cursor has exactly that bind's result type. -/
theorem preparedRaw_typed_of_initialized_bind
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (site : Nat)
    (name : VarId) (owner : Player) {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst)
    (tail : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (walk : Prefix Δ whole (.bind name owner fresh tail) site)
    (input : VEnv L Γ₀) (environment : runtime.application.EnvironmentPolicy)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerCompiled : players owner =
      runtime.compilePlayerPolicy whole owner (profile owner))
    (schedule : List (@MessageApplication.Invocation Player))
    (execution : runtime.application.PolicyExecution)
    (reached : execution ∈ (runtime.application.runPolicies
      players environment schedule
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (clock enteredAt : Nat)
    (atCursor : execution.native.application =
      .running (.bind name owner fresh tail) ideal values bindings candidates site clock enteredAt)
    (raw : Raw L) (prepared : preparedRaw (execution.principalHistory owner) site = some raw) :
    ∃ encoded : L.Val (R.result payload), raw = ⟨R.result payload, encoded⟩ := by
  unfold preparedRaw at prepared
  obtain ⟨entry, entryMem, found⟩ := List.exists_of_findSome?_eq_some prepared
  obtain ⟨beforeView, command⟩ := entry
  cases command with
  | privateCommand privateAction =>
      cases privateAction with
      | rememberDisclosure disclose => simp at found
      | prepare slot stored =>
          simp only at found
          split at found
          · rename_i slotEq
            cases found
            subst slot
            obtain ⟨front, suffix, before, after, splitSchedule, beforeMem, viewEq,
                commandMem, stepMem, residualMem⟩ :=
              runtime.application.runPolicies_initial_history_origin
                players environment schedule
                (MessageApplication.State.initial runtime.application (State.initial whole input))
                execution reached owner
                ⟨beforeView, .privateCommand (.prepare site raw)⟩ entryMem
            rw [viewEq] at commandMem
            have compiledCommand : (.privateCommand (.prepare site raw) : Command runtime) ∈
                (runtime.compilePlayerPolicy whole owner
                (profile owner) (before.principalHistory owner)
                (MessageApplication.State.observe runtime.application before.native
                  owner)).support := by
              rw [← ownerCompiled]
              exact commandMem
            have atPhase := runtime.compilePlayerPolicy_command_atPhase whole owner
              (profile owner) _
              (MessageApplication.State.observe runtime.application before.native owner) _
              compiledCommand
            simp only [Command.AtPhase] at atPhase
            have beforePhase : before.native.application.phase = site := by
              change (State.playerView before.native.application owner).publicState.pc = site
              exact atPhase.symm
            have first : after ∈ (runtime.application.invoke
                players environment before
                (.player owner)).support := by
              simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion]
              exact ⟨_, commandMem, stepMem⟩
            have combined : execution ∈ (runtime.application.runPolicies
                players environment
                (.player owner :: suffix) before).support := by
              simp only [MessageApplication.runPolicies, FinDist.support_bind,
                Set.mem_iUnion]
              exact ⟨after, first, residualMem⟩
            obtain ⟨beforeCandidates, beforeClock, beforeEntered, beforeCursor⟩ :=
              runtime.runPolicies_running_before_of_phase_eq
                (.bind name owner fresh tail) ideal values bindings candidates site clock enteredAt
                players environment (.player owner :: suffix)
                before execution atCursor combined beforePhase
            rcases before with ⟨⟨beforeApplication, beforePool, beforeReceipts⟩,
              beforeHistories, beforeEnvironmentHistory, beforeTrace⟩
            dsimp only at beforeCursor compiledCommand
            subst beforeApplication
            rw [Prefix.compilePlayerPolicy_eq_suffix walk owner (profile owner) _ _ atPhase.symm]
              at compiledCommand
            simp only [MessageApplication.State.observe, GraphRuntime.application,
              State.playerView] at compiledCommand
            simp only [compileAt, ↓reduceDIte] at compiledCommand
            split at compiledCommand
            · simp at compiledCommand
            · split at compiledCommand
              · simp at compiledCommand
              · rw [FinDist.support_map] at compiledCommand
                obtain ⟨choice, _, equality⟩ := compiledCommand
                injection equality with prepareEq
                injection prepareEq with _ rawEq
                exact ⟨(R.valueEquiv payload).symm choice, rawEq.symm⟩
          · contradiction
  | submit payload | replay payload | wait => simp at found

/-- At a compiled bind cursor, a supported wire command either leaves the
application at that cursor or installs exactly the cached bind choice. -/
theorem wireStep_bind_classify
    (runtime : GraphRuntime Player L Δ)
    (name : VarId) (owner : Player) {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst)
    (tail : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (execution after : runtime.application.PolicyExecution)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (site clock enteredAt : Nat) (encoded : L.Val (R.result payload))
    (application : execution.native.application =
      .running (.bind name owner fresh tail) ideal values bindings candidates
        site clock enteredAt)
    (invariant : PreparationInvariant runtime owner execution)
    (prepared : preparedRaw (execution.principalHistory owner) site =
      some ⟨R.result payload, encoded⟩)
    (command : WireCommand Player)
    (supported : after ∈ (runtime.application.environmentPolicyStep execution
      (command.toEnvironmentCommand runtime.application)).support) :
    after.native.application = execution.native.application ∨
      after.native.application =
        .running tail (VEnv.cons encoded ideal) (PublicValues.consSealed values)
          ((name, (owner, .prepared site)) :: bindings)
          (candidates.accept (owner, .prepared site)) (site + 1) clock clock := by
  have nativeMem : after.native ∈
      ((runtime.application.environmentPolicyStep execution
        (command.toEnvironmentCommand runtime.application)).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨after, supported, rfl⟩
  rw [runtime.application.environmentStep_native] at nativeMem
  cases command with
  | deliver observer id =>
      left
      simp only [WireCommand.toEnvironmentCommand,
        MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at nativeMem
      simpa using congrArg (fun state : runtime.application.State => state.application) nativeMem
  | wait =>
      left
      simp only [WireCommand.toEnvironmentCommand,
        MessageApplication.EnvironmentPolicyCommand.toAction,
        FinDist.mem_support_pure] at nativeMem
      exact congrArg (fun state : runtime.application.State => state.application) nativeMem
  | «include» id =>
      simp only [WireCommand.toEnvironmentCommand,
        MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at nativeMem
      cases lookup : execution.native.pool.lookup id with
      | none =>
          left
          rw [runtime.application.includePending_missing execution.native id lookup] at nativeMem
          exact congrArg (fun state => state.application) nativeMem
      | some message =>
          cases handled : runtime.handle execution.native.application message with
          | none =>
              left
              rw [runtime.application.includePending_reject execution.native id message lookup
                handled] at nativeMem
              exact congrArg (fun state => state.application) nativeMem
          | some accepted =>
              right
              exact (runtime.environmentInclude_bind_installs_prepared_choice name owner fresh tail
                execution after ideal values bindings candidates site clock enteredAt encoded
                message id accepted application invariant prepared lookup handled supported).2

/-- A wire invocation at a prepared compiled bind cursor has the exact residual
Bellman law. The continuation after each supported wire branch is defined from
that branch's preserved `Follows` witness. -/
theorem Prefix.continuationAt_bind_wire
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (site : Nat)
    (name : VarId) (owner : Player) {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst)
    (tail : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (walk : Prefix Δ whole (.bind name owner fresh tail) site)
    (execution : runtime.application.PolicyExecution)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (clock enteredAt : Nat) (encoded : L.Val (R.result payload))
    (application : execution.native.application =
      .running (.bind name owner fresh tail) ideal values bindings candidates
        site clock enteredAt)
    (follows : execution.native.application.Follows whole 0)
    (invariant : PreparationInvariant runtime owner execution)
    (prepared : preparedRaw (execution.principalHistory owner) site =
      some ⟨R.result payload, encoded⟩)
    (unique : (Γ.map Prod.fst).Nodup)
    (wire : runtime.application.WirePolicy) :
    let players := runtime.compileProfile whole profile
    let environment := runtime.application.wireEnvironment wire
    let step := runtime.application.invoke players environment execution .environment
    step.bindOnSupport (fun after supported =>
      runtime.continuationAt whole profile after.principalHistory after.native.application
        (runtime.runPolicies_follows whole 0 players environment [.environment]
          execution after follows (by
            simpa [MessageApplication.runPolicies] using supported))) =
      runtime.continuationAt whole profile execution.principalHistory
        execution.native.application follows := by
  dsimp only
  let step := runtime.application.invoke (runtime.compileProfile whole profile)
    (runtime.application.wireEnvironment wire) execution .environment
  let head := runtime.continuationAt whole profile execution.principalHistory
    execution.native.application follows
  apply (FinDist.bindOnSupport_eq_bind_of_eq_on_support (g := fun _ => head) ?_).trans
  · exact FinDist.bind_const _ _
  intro after supported
  have supportedRun : after ∈ (runtime.application.runPolicies
      (runtime.compileProfile whole profile) (runtime.application.wireEnvironment wire)
      [.environment] execution).support := by
    simpa [MessageApplication.runPolicies] using supported
  have afterFollows := runtime.runPolicies_follows whole 0
    (runtime.compileProfile whole profile) (runtime.application.wireEnvironment wire)
    [.environment] execution after follows supportedRun
  simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at supported
  obtain ⟨environmentCommand, commandMem, stepMem⟩ := supported
  simp only [MessageApplication.wireEnvironment, FinDist.support_map, Set.mem_image]
    at commandMem
  obtain ⟨wireCommand, _, rfl⟩ := commandMem
  have histories := runtime.application.environmentStep_principalHistory execution
    (wireCommand.toEnvironmentCommand runtime.application) after stepMem
  rcases runtime.wireStep_bind_classify name owner fresh tail execution after ideal values bindings
      candidates site clock enteredAt encoded application invariant prepared wireCommand
      stepMem with
    stutter | advanced
  · rw [runtime.continuationAt_running whole profile after afterFollows
      (.bind name owner fresh tail) site walk ideal values bindings candidates clock enteredAt
      (stutter.trans application)]
    rw [histories]
    exact runtime.continuationAt_running whole profile execution follows
      (.bind name owner fresh tail) site walk ideal values bindings candidates clock enteredAt
      application |>.symm
  · rw [runtime.continuationAt_running whole profile after afterFollows tail (site + 1)
      (walk.trans (.bind (.refl tail))) (VEnv.cons encoded ideal)
      (PublicValues.consSealed values) ((name, (owner, .prepared site)) :: bindings)
      (candidates.accept (owner, .prepared site)) clock clock advanced]
    rw [histories]
    dsimp only [head]
    rw [runtime.continuationAt_running whole profile execution follows
      (.bind name owner fresh tail) site walk ideal values bindings candidates clock enteredAt
      application]
    have cached : preparedChoice (execution.principalHistory owner) site payload =
        some (R.valueEquiv payload encoded) := by
      simp [preparedChoice, prepared]
    simpa using (walk.continuation_bind_advance runtime whole profile site name owner fresh tail
      ideal execution.principalHistory (R.valueEquiv payload encoded) cached unique).symm

/-- The bind wire Bellman law at every cache state of an actually initialized
execution. Only the current owner must use its compiled graph policy. -/
theorem Prefix.continuationAt_bind_wire_initialized
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (site : Nat)
    (name : VarId) (owner : Player) {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst)
    (tail : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (walk : Prefix Δ whole (.bind name owner fresh tail) site)
    (input : VEnv L Γ₀) (players : Player → runtime.application.PlayerPolicy)
    (ownerCompiled : players owner =
      runtime.compilePlayerPolicy whole owner (profile owner))
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution : runtime.application.PolicyExecution)
    (reached : execution ∈ (runtime.application.runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (clock enteredAt : Nat)
    (application : execution.native.application =
      .running (.bind name owner fresh tail) ideal values bindings candidates
        site clock enteredAt)
    (follows : execution.native.application.Follows whole 0)
    (invariant : PreparationInvariant runtime owner execution)
    (unique : (Γ.map Prod.fst).Nodup) (wire : runtime.application.WirePolicy) :
    runtime.continuationAt whole profile execution.principalHistory
        execution.native.application follows =
      (runtime.application.invoke players (runtime.application.wireEnvironment wire)
        execution .environment).bindOnSupport fun after supported =>
          runtime.continuationAt whole profile after.principalHistory after.native.application
            (runtime.invoke_follows whole 0 players (runtime.application.wireEnvironment wire)
              .environment execution after follows supported) := by
  cases cached : preparedRaw (execution.principalHistory owner) site with
  | some raw =>
      obtain ⟨encoded, rfl⟩ := runtime.preparedRaw_typed_of_initialized_bind whole profile site
        name owner fresh tail walk input environment players ownerCompiled schedule execution
        reached ideal values bindings candidates clock enteredAt application raw cached
      have law := walk.continuationAt_bind_wire runtime whole profile site name owner fresh tail
        execution ideal values bindings candidates clock enteredAt encoded application follows
        invariant cached unique wire
      simpa only [MessageApplication.invoke] using law.symm
  | none =>
      apply runtime.continuationAt_wire whole profile execution follows players wire
      intro id message next lookup handled
      exfalso
      rcases invariant with ⟨authorship, _agreement, commitments⟩
      cases message with
      | mk messageId packet =>
        cases packet with
        | opening packetSite handle raw => simp [GraphRuntime.handle, application] at handled
        | withhold packetSite => simp [GraphRuntime.handle, application] at handled
        | malformed raw => simp [GraphRuntime.handle, application] at handled
        | commitment packetSite handle =>
            have handledOriginal := handled
            simp only [GraphRuntime.handle, application] at handled
            split at handled
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
                authorship commitments ⟨messageId, .commitment site handle⟩ next id site site handle
                lookup rfl handledOriginal sameHandle
              rw [cached] at prepared
              contradiction
            · contradiction

end Vegas.GraphRuntime
