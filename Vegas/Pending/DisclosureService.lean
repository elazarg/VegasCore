/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.DisclosureAcceptance
import Vegas.Pending.ServiceLaw
import Vegas.Pending.ServiceProtection

/-! # Pre-expiry service protection for compiled disclosures -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

private theorem privateStep_bindings_eq (runtime : GraphRuntime Player L Δ)
    (state : State Player L Δ) (who : Player) (command : PrivateCommand L) :
    (runtime.privateStep state who command).publicView.bindings = state.publicView.bindings := by
  cases state
  cases command <;> rfl

private theorem tick_bindings_eq (runtime : GraphRuntime Player L Δ)
    (state next : State Player L Δ)
    (supported : next ∈ (runtime.tick state).support) :
    next.publicView.bindings = state.publicView.bindings := by
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases graph with
      | ret =>
          simp only [tick, FinDist.mem_support_pure] at supported
          subst next
          rfl
      | sample name fresh law tail =>
          simp only [tick, FinDist.support_map, Set.mem_image] at supported
          obtain ⟨value, _, rfl⟩ := supported
          rfl
      | bind name owner fresh tail =>
          simp only [tick] at supported
          split at supported <;> simp only [FinDist.mem_support_pure] at supported <;>
            subst next <;> rfl
      | resolve name owner binding fresh source checks tail =>
          simp only [tick] at supported
          split at supported <;> simp only [FinDist.mem_support_pure] at supported <;>
            subst next <;> rfl

/-- At a reached resolve cursor with a cached decision, the next compiled-owner
invocation submits the exact wire payload computed by the graph semantics.
Binding provenance rules out the otherwise possible missing-address wait. -/
theorem runPolicies_resolve_remembered_owner_submits
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ)))
    (tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner whole) (site : Nat)
    (walk : Prefix Δ whole
      (.resolve outputName owner bindingName fresh source checks tail) site)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy whole owner policy)
    (environment : runtime.application.EnvironmentPolicy)
    (execution next : runtime.application.PolicyExecution)
    (ideal : VEnv L Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (clock enteredAt : Nat) (disclose : Bool)
    (stateEq : execution.native.application =
      .running (.resolve outputName owner bindingName fresh source checks tail)
        ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt)
    (remembered : rememberedDisclosure (execution.principalHistory owner) site = some disclose)
    (unsubmitted : submittedAt (execution.principalHistory owner) site = false)
    (provenance : execution.native.application.DisciplinedBindingProvenance)
    (supported : next ∈ (runtime.application.runPolicies players environment
      [.player owner] execution).support) :
    ∃ wirePayload,
      runtime.disclosureCommand site bindingName bindings
          (acceptedResult source checks ideal disclose) = .submit wirePayload ∧
      runtime.application.SubmittedPayload wirePayload (next.principalHistory owner) := by
  have commandIsSubmit : ∃ wirePayload,
      runtime.disclosureCommand site bindingName bindings
        (acceptedResult source checks ideal disclose) = .submit wirePayload := by
    cases result : acceptedResult source checks ideal disclose with
    | failure => exact ⟨.withhold site, rfl⟩
    | success value =>
        obtain ⟨discloseEq, encoded⟩ :=
          acceptedResult_success source checks ideal disclose value result
        subst disclose
        have decoded : R.valueEquiv payload (ideal.get source) = .success value := by
          rw [encoded, Equiv.apply_symm_apply]
        obtain ⟨handle, binding, _, _⟩ := State.resolveSource_verified fresh source checks tail
          ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt decoded
          (stateEq ▸ provenance)
        refine ⟨.opening site handle
          ⟨R.result payload, (R.valueEquiv payload).symm (.success value)⟩, ?_⟩
        simp [disclosureCommand, binding]
  obtain ⟨wirePayload, commandEq⟩ := commandIsSubmit
  refine ⟨wirePayload, commandEq, ?_⟩
  simp only [MessageApplication.runPolicies, MessageApplication.invoke,
    FinDist.support_bind, Set.mem_iUnion, FinDist.mem_support_pure] at supported
  obtain ⟨middle, ⟨command, commandMem, stepMem⟩, rfl⟩ := supported
  have viewPhase : (MessageApplication.State.observe runtime.application execution.native
      owner).application.publicState.pc = site := by
    change execution.native.application.publicView.pc = site
    rw [stateEq]
    rfl
  rw [ownerCompiled, Prefix.compilePlayerPolicy_eq_suffix walk owner policy _ _ viewPhase,
    compileAt_resolve_result runtime whole outputName bindingName owner fresh source checks tail
      (walk.policyTail owner policy) _ execution.native ideal bindings candidates site clock
      enteredAt disclose stateEq remembered unsubmitted, commandEq] at commandMem
  simp only [FinDist.mem_support_pure] at commandMem
  subst command
  rw [runtime.application.playerStep_history_self owner execution _ next stepMem]
  exact ⟨⟨MessageApplication.State.observe runtime.application execution.native owner,
    .submit wirePayload⟩, by simp, rfl⟩

/-- From either cache state, two consecutive compiled-owner calls at a current
resolve cursor submit the exact semantic disclosure, provided the site had not
already submitted. -/
theorem runPolicies_resolve_two_owner_calls_submit
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ)))
    (tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner whole) (site : Nat)
    (walk : Prefix Δ whole
      (.resolve outputName owner bindingName fresh source checks tail) site)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy whole owner policy)
    (environment : runtime.application.EnvironmentPolicy)
    (execution next : runtime.application.PolicyExecution)
    (ideal : VEnv L Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (clock enteredAt : Nat)
    (stateEq : execution.native.application =
      .running (.resolve outputName owner bindingName fresh source checks tail)
        ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt)
    (unsubmitted : submittedAt (execution.principalHistory owner) site = false)
    (provenance : execution.native.application.DisciplinedBindingProvenance)
    (supported : next ∈ (runtime.application.runPolicies players environment
      [.player owner, .player owner] execution).support) :
    ∃ disclose wirePayload,
      runtime.disclosureCommand site bindingName bindings
          (acceptedResult source checks ideal disclose) = .submit wirePayload ∧
      runtime.application.SubmittedPayload wirePayload (next.principalHistory owner) := by
  have allSupported := supported
  simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion] at supported
  obtain ⟨middle, first, second⟩ := supported
  have firstSupported : middle ∈ (runtime.application.runPolicies players environment
      [.player owner] execution).support := by
    simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion]
    exact ⟨middle, first, FinDist.mem_support_pure.mpr rfl⟩
  have secondSupported : next ∈ (runtime.application.runPolicies players environment
      [.player owner] middle).support := by
    simpa only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion,
      FinDist.mem_support_pure] using second
  cases cached : rememberedDisclosure (execution.principalHistory owner) site with
  | some disclose =>
      obtain ⟨wirePayload, commandEq, submitted⟩ :=
        runPolicies_resolve_remembered_owner_submits runtime whole outputName bindingName owner
          fresh source checks tail policy site walk players ownerCompiled environment execution
          middle ideal bindings candidates clock enteredAt disclose stateEq cached unsubmitted
          provenance firstSupported
      exact ⟨disclose, wirePayload, commandEq,
        runtime.application.runPolicies_submittedPayload_preserved owner wirePayload players
          environment [.player owner]
          middle next submitted secondSupported⟩
  | none =>
      let view := MessageApplication.State.observe runtime.application execution.native owner
      have viewPhase : view.application.publicState.pc = site := by
        change execution.native.application.publicView.pc = site
        rw [stateEq]
        rfl
      have viewOwner : view.application.who = owner := rfl
      have viewContext : view.application.publicState.Γ = Γ := by
        change execution.native.application.publicView.Γ = Γ
        rw [stateEq]
        rfl
      have playerAtHead : players owner (execution.principalHistory owner) view =
          compileAt runtime owner whole
            (.resolve outputName owner bindingName fresh source checks tail)
            (walk.policyTail owner policy) site (execution.principalHistory owner) view := by
        rw [ownerCompiled]
        exact Prefix.compilePlayerPolicy_eq_suffix walk owner policy _ _ viewPhase
      have factor := runtime.runPolicies_resolve_first_kernel whole site outputName bindingName
        owner fresh source checks tail (walk.policyTail owner policy) players execution environment
        [.player owner] playerAtHead viewPhase viewOwner viewContext cached unsubmitted
      rw [factor] at allSupported
      simp only [FinDist.support_bind, Set.mem_iUnion] at allSupported
      obtain ⟨disclose, choiceMem, recorded, recordStep, remaining⟩ := allSupported
      have history := runtime.application.playerStep_history_self owner execution
        (.privateCommand (.rememberDisclosure disclose)) recorded recordStep
      have nowRemembered : rememberedDisclosure (recorded.principalHistory owner) site =
          some disclose := by
        rw [history]
        exact rememberedDisclosure_append_remember runtime _ view site disclose cached viewPhase
      have stillUnsubmitted : submittedAt (recorded.principalHistory owner) site = false := by
        rw [history]
        unfold submittedAt at unsubmitted ⊢
        rw [List.any_append, unsubmitted]
        rfl
      have nativeMem : recorded.native ∈
          ((runtime.application.playerStep owner execution
            (.privateCommand (.rememberDisclosure disclose))).map
            MessageInterface.PolicyExecution.native).support := by
        rw [FinDist.support_map]
        exact ⟨recorded, recordStep, rfl⟩
      rw [runtime.application.playerStep_native] at nativeMem
      simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at nativeMem
      have recordedState : recorded.native.application = execution.native.application := by
        rw [nativeMem]
        rfl
      have recordedExact : recorded.native.application =
          .running (.resolve outputName owner bindingName fresh source checks tail)
            ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt :=
        recordedState.trans stateEq
      have recordedProvenance := runtime.runPolicies_disciplinedBindingProvenance players
        environment [.player owner] execution recorded provenance (by
          simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion]
          refine ⟨recorded, ?_, FinDist.mem_support_pure.mpr rfl⟩
          simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion]
          refine ⟨.privateCommand (.rememberDisclosure disclose), ?_, recordStep⟩
          rw [playerAtHead, compileAt_resolve_fresh runtime whole site outputName bindingName
            owner fresh source checks tail (walk.policyTail owner policy) _ view viewPhase
            viewOwner viewContext cached unsubmitted, FinDist.support_map]
          exact ⟨disclose, choiceMem, rfl⟩)
      obtain ⟨wirePayload, commandEq, submitted⟩ :=
        runPolicies_resolve_remembered_owner_submits runtime whole outputName bindingName owner
          fresh source checks tail policy site walk players ownerCompiled environment recorded next
          ideal bindings candidates clock enteredAt disclose recordedExact nowRemembered
          stillUnsubmitted recordedProvenance remaining
      exact ⟨disclose, wirePayload, commandEq, submitted⟩

private theorem canonical_resolve_submission_of_actual_history
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (input : VEnv L Γ₀)
    (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ)))
    (tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner whole) (site : Nat)
    (walk : Prefix Δ whole
      (.resolve outputName owner bindingName fresh source checks tail) site)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy whole owner policy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution : runtime.application.PolicyExecution)
    (ideal : VEnv L Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (clock enteredAt : Nat)
    (reached : execution ∈ (runtime.application.runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (stateEq : execution.native.application =
      .running (.resolve outputName owner bindingName fresh source checks tail)
        ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt)
    (submitted : submittedAt (execution.principalHistory owner) site = true) :
    ∃ disclose wirePayload,
      runtime.disclosureCommand site bindingName bindings
          (acceptedResult source checks ideal disclose) = .submit wirePayload ∧
      runtime.application.SubmittedPayload wirePayload
        (execution.principalHistory owner) := by
  unfold submittedAt at submitted
  rw [List.any_eq_true] at submitted
  obtain ⟨entry, member, matched⟩ := submitted
  obtain ⟨front, suffix, before, after, _, beforeMem, viewEq, commandMem,
      stepMem, residual⟩ :=
    runtime.application.runPolicies_initial_history_origin players environment schedule
      (MessageApplication.State.initial runtime.application (State.initial whole input))
      execution reached owner entry member
  have atPhase := runtime.compilePlayerPolicy_command_atPhase whole owner policy
    (before.principalHistory owner) entry.beforeView entry.command (by
      rw [← ownerCompiled]
      exact commandMem)
  cases commandEq : entry.command with
  | privateCommand command | replay command | wait =>
      rw [commandEq] at matched
      contradiction
  | submit wirePayload =>
      rw [commandEq] at matched
      cases wirePayload with
      | malformed raw => contradiction
      | commitment packetSite handle | opening packetSite handle raw | withhold packetSite =>
          change decide (packetSite = site) = true at matched
          simp only [decide_eq_true_eq] at matched
          subst packetSite
          rw [commandEq] at atPhase
          rw [viewEq] at atPhase
          have beforePhase : before.native.application.phase = site := by
            simp only [Command.AtPhase] at atPhase
            have phaseAt : site = (MessageApplication.State.observe runtime.application
                before.native owner).application.publicState.pc := by
              first | exact atPhase.1 | exact atPhase
            change site = before.native.application.publicView.pc at phaseAt
            rw [State.publicView_pc] at phaseAt
            exact phaseAt.symm
          have fromBefore : execution ∈ (runtime.application.runPolicies players environment
              (.player owner :: suffix) before).support := by
            simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion]
            refine ⟨after, ?_, residual⟩
            simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion]
            refine ⟨entry.command, ?_, stepMem⟩
            simpa [viewEq] using commandMem
          obtain ⟨beforeCandidates, beforeClock, beforeEnteredAt, beforeState⟩ :=
            runtime.runPolicies_running_before_of_phase_eq
              (.resolve outputName owner bindingName fresh source checks tail)
              ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt
              players environment (.player owner :: suffix) before execution stateEq fromBefore
              beforePhase
          have localCommand : entry.command ∈
              (compileAt runtime owner whole
                (.resolve outputName owner bindingName fresh source checks tail)
                (walk.policyTail owner policy) site (before.principalHistory owner)
                (MessageApplication.State.observe runtime.application before.native
                  owner)).support := by
            rw [← walk.compilePlayerPolicy_eq_suffix owner policy]
            · rw [← ownerCompiled]
              simpa [viewEq] using commandMem
            · change before.native.application.phase = site
              exact beforePhase
          rw [commandEq] at localCommand
          obtain ⟨disclose, rememberedBefore, unsubmittedBefore⟩ :=
            compileAt_resolve_submit_cached runtime whole outputName bindingName owner fresh source
              checks tail (walk.policyTail owner policy) (before.principalHistory owner)
              before.native ideal bindings beforeCandidates site beforeClock beforeEnteredAt _
              beforeState localCommand
          have law := compileAt_resolve_result runtime whole outputName bindingName owner fresh
            source checks tail (walk.policyTail owner policy) (before.principalHistory owner)
            before.native ideal bindings beforeCandidates site beforeClock beforeEnteredAt disclose
            beforeState rememberedBefore unsubmittedBefore
          rw [law] at localCommand
          simp only [FinDist.mem_support_pure] at localCommand
          refine ⟨disclose, _, localCommand.symm, entry, member, commandEq⟩

/-- For every actual current resolve history, two owner calls leave the exact
semantic disclosure in authenticated history. This covers prior submission,
cached decisions, and a fresh disclosure cache. -/
theorem runPolicies_resolve_two_owner_calls_submitted
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (input : VEnv L Γ₀) (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline Graph.BindingOrigins.none)
    (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ)))
    (tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner whole) (site : Nat)
    (walk : Prefix Δ whole
      (.resolve outputName owner bindingName fresh source checks tail) site)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy whole owner policy)
    (environment : runtime.application.EnvironmentPolicy)
    (prefixSchedule : List (@MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (ideal : VEnv L Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (clock enteredAt : Nat)
    (reached : execution ∈ (runtime.application.runPolicies players environment prefixSchedule
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (stateEq : execution.native.application =
      .running (.resolve outputName owner bindingName fresh source checks tail)
        ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt)
    (supported : next ∈ (runtime.application.runPolicies players environment
      [.player owner, .player owner] execution).support) :
    ∃ disclose wirePayload,
      runtime.disclosureCommand site bindingName bindings
          (acceptedResult source checks ideal disclose) = .submit wirePayload ∧
      runtime.application.SubmittedPayload wirePayload (next.principalHistory owner) := by
  by_cases wasSubmitted : submittedAt (execution.principalHistory owner) site = true
  · obtain ⟨disclose, wirePayload, commandEq, prior⟩ :=
      canonical_resolve_submission_of_actual_history runtime whole input
        outputName bindingName owner fresh source checks tail policy site walk players ownerCompiled
        environment prefixSchedule execution ideal bindings candidates clock enteredAt reached
        stateEq wasSubmitted
    exact ⟨disclose, wirePayload, commandEq,
      runtime.application.runPolicies_submittedPayload_preserved owner wirePayload players
        environment [.player owner, .player owner] execution next prior supported⟩
  · have unsubmitted := Bool.eq_false_iff.mpr wasSubmitted
    have provenance := runtime.runPolicies_initial_disciplinedBindingProvenance whole input unique
      discipline players environment prefixSchedule execution reached
    exact runPolicies_resolve_two_owner_calls_submit runtime whole outputName bindingName owner
      fresh source checks tail policy site walk players ownerCompiled environment execution next
      ideal bindings candidates clock enteredAt stateEq unsubmitted provenance supported

/-- An exact semantic disclosure already present in actual authenticated
history is either past its resolve phase, or its originally allocated envelope
is still pending and remains the compiled owner's newest serial. -/
theorem resolve_submitted_pending_or_advanced
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (input : VEnv L Γ₀) (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline Graph.BindingOrigins.none)
    (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ)))
    (tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner whole) (site : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy whole owner policy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution : runtime.application.PolicyExecution)
    (ideal : VEnv L Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (clock enteredAt : Nat) (disclose : Bool) (wirePayload : Payload Player L)
    (reached : execution ∈ (runtime.application.runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (stateEq : execution.native.application =
      .running (.resolve outputName owner bindingName fresh source checks tail)
        ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt)
    (semantic : runtime.disclosureCommand site bindingName bindings
      (acceptedResult source checks ideal disclose) = .submit wirePayload)
    (submitted : runtime.application.SubmittedPayload wirePayload
      (execution.principalHistory owner)) :
    site < execution.native.application.phase ∨
      ∃ serial,
        ({ id := (owner, serial), payload := wirePayload } :
          Message Player runtime.application.Payload) ∈ execution.native.pool.pending ∧
        execution.native.pool.nextSerial owner = serial + 1 := by
  obtain ⟨entry, member, entryCommand⟩ := submitted
  obtain ⟨front, suffix, before, after, _, beforeMem, viewEq, commandMem, stepMem,
      residual⟩ :=
    runtime.application.runPolicies_initial_history_origin players environment schedule
      (MessageApplication.State.initial runtime.application (State.initial whole input))
      execution reached owner entry member
  have atPhase := runtime.compilePlayerPolicy_command_atPhase whole owner policy
    (before.principalHistory owner) entry.beforeView entry.command (by
      rw [← ownerCompiled]
      exact commandMem)
  rw [entryCommand] at atPhase
  have packetAt : Command.AtPhase runtime owner
      entry.beforeView.application.publicState.pc (.submit wirePayload) := atPhase
  have beforePhase : before.native.application.phase = site := by
    rw [viewEq] at packetAt
    cases result : acceptedResult source checks ideal disclose with
    | failure =>
        simp only [result, disclosureCommand] at semantic
        injection semantic with payloadEq
        subst wirePayload
        change site = before.native.application.phase at packetAt
        exact packetAt.symm
    | success value =>
        simp only [result, disclosureCommand] at semantic
        cases binding : lookupBinding bindings bindingName with
        | none => simp [binding] at semantic
        | some handle =>
            rw [binding] at semantic
            injection semantic with payloadEq
            subst wirePayload
            change site = before.native.application.phase at packetAt
            exact packetAt.symm
  have fromBefore : execution ∈ (runtime.application.runPolicies players environment
      (.player owner :: suffix) before).support := by
    simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion]
    refine ⟨after, ?_, residual⟩
    simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion]
    refine ⟨entry.command, ?_, stepMem⟩
    simpa [viewEq] using commandMem
  obtain ⟨beforeCandidates, beforeClock, beforeEnteredAt, beforeState⟩ :=
    runtime.runPolicies_running_before_of_phase_eq
      (.resolve outputName owner bindingName fresh source checks tail)
      ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt
      players environment (.player owner :: suffix) before execution stateEq fromBefore beforePhase
  have nativeMem : after.native ∈
      ((runtime.application.playerStep owner before (.submit wirePayload)).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨after, by simpa [entryCommand] using stepMem, rfl⟩
  rw [runtime.application.playerStep_native] at nativeMem
  simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
    FinDist.mem_support_pure] at nativeMem
  let serial := before.native.pool.nextSerial owner
  have afterApplication : after.native.application = before.native.application := by
    rw [nativeMem]
  have afterState : after.native.application =
      .running (.resolve outputName owner bindingName fresh source checks tail)
        ideal (PublicValues.ofVEnv ideal) bindings beforeCandidates site beforeClock
          beforeEnteredAt := afterApplication.trans beforeState
  have afterPending : ({ id := (owner, serial), payload := wirePayload } :
      Message Player runtime.application.Payload) ∈ after.native.pool.pending := by
    rw [nativeMem]
    simp [serial, MessagePool.submit]
  have afterCounter : after.native.pool.nextSerial owner = serial + 1 := by
    rw [nativeMem]
    simp [serial, MessagePool.submit]
  have afterSubmitted : submittedAt (after.principalHistory owner) site = true := by
    rw [runtime.application.playerStep_history_self owner before (.submit wirePayload) after
      (by simpa [entryCommand] using stepMem)]
    unfold submittedAt
    rw [List.any_append]
    cases result : acceptedResult source checks ideal disclose with
    | failure =>
        simp only [result, disclosureCommand] at semantic
        injection semantic with payloadEq
        subst wirePayload
        simp
    | success value =>
        simp only [result, disclosureCommand] at semantic
        cases binding : lookupBinding bindings bindingName with
        | none => simp [binding] at semantic
        | some handle =>
            rw [binding] at semantic
            injection semantic with payloadEq
            subst wirePayload
            simp
  have beforeProvenance := runtime.runPolicies_initial_disciplinedBindingProvenance whole input
    unique discipline players environment front before beforeMem
  have afterProvenance : after.native.application.DisciplinedBindingProvenance := by
    rw [afterApplication]
    exact beforeProvenance
  have afterFollows : after.native.application.Follows
      (.resolve outputName owner bindingName fresh source checks tail) site := by
    rw [afterState]
    exact State.running_follows _ _ _ _ _ site _ _
  cases result : acceptedResult source checks ideal disclose with
  | failure =>
      simp only [result, disclosureCommand] at semantic
      injection semantic with payloadEq
      subst wirePayload
      have protection := runtime.runPolicies_exact_pending_or_phase_advanced site owner serial
        (.withhold site) (fun state => state.Follows
          (.resolve outputName owner bindingName fresh source checks tail) site)
        players environment suffix after execution (initialValid := afterFollows)
        (atPhase := by rw [afterState]; rfl) (pending := afterPending)
        (fun application actor command follows => runtime.privateStep_follows _ site application
          actor command follows)
        (fun application next follows happened => runtime.tick_follows _ site application next
          follows happened)
        (fun application allocated follows phaseEq => by
          obtain ⟨env, values, addresses, catalog, time, entered, exactState⟩ :=
            State.follows_at_base _ site application follows (by simpa using phaseEq)
          refine ⟨advanceResolve tail env values addresses catalog site time .failure, ?_, by
            simp [advanceResolve, State.phase]⟩
          rw [exactState]
          exact runtime.handle_resolve_withhold fresh source checks tail env values addresses
            catalog site time entered allocated)
        residual
      rcases protection with advanced | ⟨same, remains⟩
      · exact Or.inl advanced
      · have counterLaw := runtime.runPolicies_compiled_submitted_counter whole owner policy
          players ownerCompiled environment suffix after execution site (serial + 1)
          (by rw [afterState]; rfl) afterSubmitted afterCounter residual
        rcases counterLaw with advanced | ⟨_, _, counter⟩
        · exact Or.inl advanced
        · exact Or.inr ⟨serial, remains, counter⟩
  | success value =>
      simp only [result, disclosureCommand] at semantic
      cases binding : lookupBinding bindings bindingName with
      | none => simp [binding] at semantic
      | some handle =>
          rw [binding] at semantic
          injection semantic with payloadEq
          subst wirePayload
          obtain ⟨discloseEq, encoded⟩ :=
            acceptedResult_success source checks ideal disclose value result
          subst disclose
          have decoded : R.valueEquiv payload (ideal.get source) = .success value := by
            rw [encoded, Equiv.apply_symm_apply]
          obtain ⟨sourceHandle, sourceBinding, ownerEq, verified⟩ :=
            State.resolveSource_verified fresh source checks tail ideal
              (PublicValues.ofVEnv ideal) bindings beforeCandidates site beforeClock
              beforeEnteredAt decoded (beforeState ▸ beforeProvenance)
          have handleEq : sourceHandle = handle := by
            rw [binding] at sourceBinding
            exact (Option.some.inj sourceBinding).symm
          subst sourceHandle
          let raw : Raw L := ⟨R.result payload, ideal.get source⟩
          have afterVerified : after.native.application.candidates.verify handle raw = true := by
            rw [afterState]
            exact verified
          let valid : State Player L Δ → Prop := fun state =>
            state.Follows (.resolve outputName owner bindingName fresh source checks tail) site ∧
              lookupBinding state.publicView.bindings bindingName = some handle ∧
              state.candidates.verify handle raw = true
          have protection := runtime.runPolicies_exact_pending_or_phase_advanced site owner serial
            (.opening site handle raw) valid players environment suffix after execution
            (initialValid := ⟨afterFollows, ⟨by rw [afterState]; exact binding,
              afterVerified⟩⟩)
            (atPhase := by rw [afterState]; rfl)
            (pending := by simpa [raw, encoded] using afterPending)
            (fun application actor command holds => ⟨runtime.privateStep_follows _ site application
              actor command holds.1, (by rw [privateStep_bindings_eq]; exact holds.2.1), (by
                cases command with
                | prepare slot prepared =>
                    rw [runtime.privateStep_prepare_candidates,
                      CommitmentCandidates.verify_eq_true_iff]
                    have lookup :=
                      (application.candidates.verify_eq_true_iff handle raw).mp holds.2.2
                    rw [application.candidates.lookup_prepare_eq_of_not_fresh handle actor
                      (.prepared slot) prepared (by rw [lookup]; simp), lookup]
                | rememberDisclosure => exact holds.2.2)⟩)
            (fun application next holds happened => ⟨runtime.tick_follows _ site application next
              holds.1 happened,
              (by rw [tick_bindings_eq runtime application next happened]; exact holds.2.1),
              (by rw [runtime.tick_candidates application next happened]; exact holds.2.2)⟩)
            (fun application allocated holds phaseEq => by
              obtain ⟨env, values, addresses, catalog, time, entered, exactState⟩ :=
                State.follows_at_base _ site application holds.1 (by simpa using phaseEq)
              refine ⟨advanceResolve tail env values addresses catalog site time
                (acceptedProposal checks values (R.valueEquiv payload raw.value)), ?_, by
                  simp [advanceResolve, State.phase]⟩
              rw [exactState] at holds ⊢
              simp only [GraphRuntime.handle, Message.sender, decide_eq_true_eq,
                Bool.and_eq_true, true_and, Option.ite_none_right_eq_some]
              constructor
              · exact ⟨⟨ownerEq, holds.2.1⟩, holds.2.2⟩
              · simp [raw])
            residual
          rcases protection with advanced | ⟨same, remains⟩
          · exact Or.inl advanced
          · have counterLaw := runtime.runPolicies_compiled_submitted_counter whole owner policy
              players ownerCompiled environment suffix after execution site (serial + 1)
              (by rw [afterState]; rfl) afterSubmitted afterCounter residual
            rcases counterLaw with advanced | ⟨_, _, counter⟩
            · exact Or.inl advanced
            · exact Or.inr ⟨serial, by simpa [raw, encoded] using remains, counter⟩

/-- A semantically submitted current resolve cannot reach its reserved newest
inclusion still at the same phase: reactions may advance it early, otherwise
the actual service cursor selects and accepts the protected newest envelope. -/
theorem resolve_reactions_then_reserved_include_advances
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (input : VEnv L Γ₀) (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline Graph.BindingOrigins.none)
    (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ)))
    (tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner whole) (site : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy whole owner policy)
    (beforeService suffixService : List (ServiceInstruction Player))
    (wire : runtime.application.WirePolicy)
    (prefixSchedule reactions : List (@MessageApplication.Invocation Player))
    (execution reacted included : runtime.application.PolicyExecution)
    (ideal : VEnv L Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (clock enteredAt : Nat) (disclose : Bool) (wirePayload : Payload Player L)
    (reached : execution ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment
        (beforeService ++ .includeLatest owner :: suffixService) wire)
      prefixSchedule (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (stateEq : execution.native.application =
      .running (.resolve outputName owner bindingName fresh source checks tail)
        ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt)
    (semantic : runtime.disclosureCommand site bindingName bindings
      (acceptedResult source checks ideal disclose) = .submit wirePayload)
    (submitted : runtime.application.SubmittedPayload wirePayload
      (execution.principalHistory owner))
    (reactionSupported : reacted ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment
        (beforeService ++ .includeLatest owner :: suffixService) wire)
      reactions execution).support)
    (cursor : reacted.environmentHistory.length =
      (beforeService.filterMap ServiceInstruction.environmentSlot).length)
    (includeSupported : included ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment
        (beforeService ++ .includeLatest owner :: suffixService) wire)
      [.environment] reacted).support) :
    site < included.native.application.phase := by
  let serviceEnvironment := runtime.serviceEnvironment
    (beforeService ++ .includeLatest owner :: suffixService) wire
  have phaseMono := runtime.runPolicies_phase_mono players serviceEnvironment reactions
    execution reacted (by simpa [serviceEnvironment] using reactionSupported)
  by_cases advanced : site < reacted.native.application.phase
  · have includeMono := runtime.runPolicies_phase_mono players serviceEnvironment [.environment]
      reacted included (by simpa [serviceEnvironment] using includeSupported)
    exact advanced.trans_le includeMono
  · have reactedPhase : reacted.native.application.phase = site := by
      have executionPhase : execution.native.application.phase = site := by
        rw [stateEq]
        rfl
      omega
    obtain ⟨reactedCandidates, reactedClock, reactedEnteredAt, reactedState⟩ :=
      runtime.runPolicies_running_eq_of_phase_eq
        (.resolve outputName owner bindingName fresh source checks tail)
        ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt
        players serviceEnvironment reactions execution reacted stateEq
        (by simpa [serviceEnvironment] using reactionSupported) reactedPhase
    have reachedReacted : reacted ∈ (runtime.application.runPolicies players serviceEnvironment
        (prefixSchedule ++ reactions)
        (MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application
            (State.initial whole input)))).support := by
      rw [runtime.application.runPolicies_append]
      simp only [FinDist.support_bind, Set.mem_iUnion]
      exact ⟨execution, by simpa [serviceEnvironment] using reached,
        by simpa [serviceEnvironment] using reactionSupported⟩
    have submittedReacted :=
      runtime.application.runPolicies_submittedPayload_preserved owner wirePayload players
        serviceEnvironment reactions execution reacted submitted
        (by simpa [serviceEnvironment] using reactionSupported)
    have pendingLaw := resolve_submitted_pending_or_advanced runtime whole input unique discipline
      outputName bindingName owner fresh source checks tail policy site players ownerCompiled
      serviceEnvironment (prefixSchedule ++ reactions) reacted ideal bindings reactedCandidates
      reactedClock reactedEnteredAt disclose wirePayload reachedReacted reactedState semantic
      submittedReacted
    rcases pendingLaw with impossible | ⟨serial, pending, counter⟩
    · omega
    · have authorship := runtime.application.runPolicies_initial_authorship players
        serviceEnvironment (prefixSchedule ++ reactions) (State.initial whole input) reacted
        reachedReacted
      have lookup := MessageApplication.Authorship.lookup_eq_of_mem_pending runtime.application
        reacted authorship ({ id := (owner, serial), payload := wirePayload } :
          Message Player runtime.application.Payload) pending
      have includedNative := runtime.runPolicies_includeLatest_pending players beforeService
        suffixService owner serial wire reacted included cursor counter ⟨_, lookup⟩
        (by simpa [serviceEnvironment] using includeSupported)
      cases result : acceptedResult source checks ideal disclose with
      | failure =>
          simp only [result, disclosureCommand] at semantic
          injection semantic with payloadEq
          subst wirePayload
          let after := advanceResolve tail ideal (PublicValues.ofVEnv ideal) bindings
            reactedCandidates site reactedClock .failure
          have accepted : runtime.handle reacted.native.application
              ({ id := (owner, serial), payload := .withhold site } :
                Message Player runtime.application.Payload) = some after := by
            rw [reactedState]
            exact runtime.handle_resolve_withhold fresh source checks tail ideal
              (PublicValues.ofVEnv ideal) bindings reactedCandidates site reactedClock
              reactedEnteredAt serial
          rw [includedNative, runtime.application.includePending_accept reacted.native
            (owner, serial) _ after lookup accepted]
          simp [after, advanceResolve, State.phase]
      | success value =>
          simp only [result, disclosureCommand] at semantic
          cases binding : lookupBinding bindings bindingName with
          | none => simp [binding] at semantic
          | some handle =>
              rw [binding] at semantic
              injection semantic with payloadEq
              subst wirePayload
              obtain ⟨discloseEq, encoded⟩ :=
                acceptedResult_success source checks ideal disclose value result
              subst disclose
              have decoded : R.valueEquiv payload (ideal.get source) = .success value := by
                rw [encoded, Equiv.apply_symm_apply]
              have provenance := runtime.runPolicies_initial_disciplinedBindingProvenance whole
                input unique discipline players serviceEnvironment (prefixSchedule ++ reactions)
                reacted reachedReacted
              obtain ⟨sourceHandle, sourceBinding, ownerEq, verified⟩ :=
                State.resolveSource_verified fresh source checks tail ideal
                  (PublicValues.ofVEnv ideal) bindings reactedCandidates site reactedClock
                  reactedEnteredAt decoded (reactedState ▸ provenance)
              have handleEq : sourceHandle = handle := by
                rw [binding] at sourceBinding
                exact (Option.some.inj sourceBinding).symm
              subst sourceHandle
              let after := advanceResolve tail ideal (PublicValues.ofVEnv ideal) bindings
                reactedCandidates site reactedClock (.success value)
              have accepted : runtime.handle reacted.native.application
                  ({ id := (owner, serial), payload := (.opening site handle
                    ⟨R.result payload, ideal.get source⟩) } :
                    Message Player runtime.application.Payload) = some after := by
                rw [reactedState]
                simpa [after, advanceResolve, result, encoded] using
                  runtime.handle_resolve_verified fresh source checks
                  tail ideal bindings reactedCandidates site reactedClock reactedEnteredAt serial
                  handle (ideal.get source) binding ownerEq verified rfl
              have acceptedWire : runtime.handle reacted.native.application
                  ({ id := (owner, serial), payload := (.opening site handle
                    ⟨R.result payload,
                      (R.valueEquiv payload).symm (.success value)⟩) } :
                    Message Player runtime.application.Payload) = some after := by
                simpa [encoded] using accepted
              rw [includedNative, runtime.application.includePending_accept reacted.native
                (owner, serial) _ after lookup acceptedWire]
              simp [after, advanceResolve, State.phase]

/-- The complete pre-expiry resolve service block advances every actually
reached current resolve: two compiled-owner calls cover every cache state,
then the real reaction prefix and reserved newest inclusion finish the phase. -/
theorem resolve_full_service_block_advances
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (input : VEnv L Γ₀) (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline Graph.BindingOrigins.none)
    (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ)))
    (tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner whole) (site : Nat)
    (walk : Prefix Δ whole
      (.resolve outputName owner bindingName fresh source checks tail) site)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy whole owner policy)
    (before reactionBlock suffix : List (ServiceInstruction Player))
    (wire : runtime.application.WirePolicy)
    (prefixSchedule : List (@MessageApplication.Invocation Player))
    (execution afterLead reacted included : runtime.application.PolicyExecution)
    (ideal : VEnv L Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (clock enteredAt : Nat)
    (reached : execution ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment
        (before ++ [.player owner, .player owner] ++ reactionBlock ++
          .includeLatest owner :: suffix) wire)
      prefixSchedule (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (stateEq : execution.native.application =
      .running (.resolve outputName owner bindingName fresh source checks tail)
        ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt)
    (cursor : execution.environmentHistory.length =
      (before.filterMap ServiceInstruction.environmentSlot).length)
    (leadSupported : afterLead ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment
        (before ++ [.player owner, .player owner] ++ reactionBlock ++
          .includeLatest owner :: suffix) wire)
      [.player owner, .player owner] execution).support)
    (reactionSupported : reacted ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment
        (before ++ [.player owner, .player owner] ++ reactionBlock ++
          .includeLatest owner :: suffix) wire)
      (reactionBlock.map ServiceInstruction.invocation) afterLead).support)
    (includeSupported : included ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment
        (before ++ [.player owner, .player owner] ++ reactionBlock ++
          .includeLatest owner :: suffix) wire)
      [.environment] reacted).support) :
    site < included.native.application.phase := by
  let lead : List (ServiceInstruction Player) := [.player owner, .player owner]
  let plan := before ++ lead ++ reactionBlock ++ .includeLatest owner :: suffix
  let serviceEnvironment := runtime.serviceEnvironment plan wire
  have leadMono := runtime.runPolicies_phase_mono players serviceEnvironment
    [.player owner, .player owner] execution afterLead
    (by simpa [serviceEnvironment, plan, lead] using leadSupported)
  by_cases advanced : site < afterLead.native.application.phase
  · have reactionMono := runtime.runPolicies_phase_mono players serviceEnvironment
      (reactionBlock.map ServiceInstruction.invocation) afterLead reacted
      (by simpa [serviceEnvironment, plan, lead] using reactionSupported)
    have includeMono := runtime.runPolicies_phase_mono players serviceEnvironment [.environment]
      reacted included (by simpa [serviceEnvironment, plan, lead] using includeSupported)
    exact advanced.trans_le (reactionMono.trans includeMono)
  · have afterLeadPhase : afterLead.native.application.phase = site := by
      have executionPhase : execution.native.application.phase = site := by
        rw [stateEq]
        rfl
      omega
    obtain ⟨leadCandidates, leadClock, leadEnteredAt, leadState⟩ :=
      runtime.runPolicies_running_eq_of_phase_eq
        (.resolve outputName owner bindingName fresh source checks tail)
        ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt
        players serviceEnvironment [.player owner, .player owner] execution afterLead stateEq
        (by simpa [serviceEnvironment, plan, lead] using leadSupported) afterLeadPhase
    have reachedLead : afterLead ∈ (runtime.application.runPolicies players serviceEnvironment
        (prefixSchedule ++ [.player owner, .player owner])
        (MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application
            (State.initial whole input)))).support := by
      rw [runtime.application.runPolicies_append]
      simp only [FinDist.support_bind, Set.mem_iUnion]
      exact ⟨execution, by simpa [serviceEnvironment, plan, lead] using reached,
        by simpa [serviceEnvironment, plan, lead] using leadSupported⟩
    obtain ⟨disclose, wirePayload, semantic, submitted⟩ :=
      runPolicies_resolve_two_owner_calls_submitted runtime whole input unique discipline
        outputName bindingName owner fresh source checks tail policy site walk players
        ownerCompiled serviceEnvironment prefixSchedule execution afterLead ideal bindings
        candidates clock enteredAt (by simpa [serviceEnvironment, plan, lead] using reached)
        stateEq (by simpa [serviceEnvironment, plan, lead] using leadSupported)
    have leadReactionSupported : reacted ∈
        (runtime.application.runPolicies players serviceEnvironment
          ((lead ++ reactionBlock).map ServiceInstruction.invocation) execution).support := by
      rw [List.map_append, runtime.application.runPolicies_append]
      simp only [FinDist.support_bind, Set.mem_iUnion]
      exact ⟨afterLead, by
          simpa [lead, ServiceInstruction.invocation, serviceEnvironment, plan] using leadSupported,
        by simpa [serviceEnvironment, plan, lead] using reactionSupported⟩
    have cursorStep := runtime.runPolicies_service_cursor players serviceEnvironment
      (lead ++ reactionBlock) execution reacted leadReactionSupported
    have reactedCursor : reacted.environmentHistory.length =
        ((before ++ lead ++ reactionBlock).filterMap
          ServiceInstruction.environmentSlot).length := by
      rw [cursor] at cursorStep
      simpa [List.filterMap_append, lead] using cursorStep
    apply resolve_reactions_then_reserved_include_advances runtime whole input unique discipline
      outputName bindingName owner fresh source checks tail policy site players ownerCompiled
      (before ++ lead ++ reactionBlock) suffix wire
      (prefixSchedule ++ [.player owner, .player owner])
      (reactionBlock.map ServiceInstruction.invocation) afterLead reacted included ideal bindings
      leadCandidates leadClock leadEnteredAt disclose wirePayload
    · simpa [serviceEnvironment, plan, lead, List.append_assoc] using reachedLead
    · exact leadState
    · exact semantic
    · exact submitted
    · simpa [serviceEnvironment, plan, lead, List.append_assoc] using reactionSupported
    · exact reactedCursor
    · simpa [serviceEnvironment, plan, lead, List.append_assoc] using includeSupported

end Vegas.GraphRuntime
