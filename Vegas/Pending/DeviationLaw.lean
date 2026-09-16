/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.DeviationFocalInvocation

/-! # Pure unilateral-deviation law for the serviced graph runtime -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

theorem servicePlan_pure_deviation_law_of_locality
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ Δ)
    (profile : BehavioralProfile whole) (inputs : FinDist (VEnv L Γ))
    (input : VEnv L Γ) (inputMem : input ∈ inputs.support)
    (unique : (Γ.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (focal : Player) (replacement : runtime.application.PlayerPolicy)
    (roster : List Player) (rounds : Nat) (wire : runtime.application.WirePolicy)
    (focalPolicy : profile focal = runtime.extractedObservationPolicy whole
      inputs
      (Profile.update
        (sig := MessageApplication.policySignature Player runtime.application)
        (runtime.compileProfile whole profile) focal replacement)
      (runtime.serviceEnvironment (runtime.servicePlan roster rounds whole 0) wire)
      ((runtime.servicePlan roster rounds whole 0).map ServiceInstruction.invocation) focal)
    (locality : ∀ {target} (suffix : Graph Player L target Δ) site
      (observation : Observation L focal target) (left right : OwnAction Player L),
      ReachedOwnAction runtime whole inputs
        (Profile.update
          (sig := MessageApplication.policySignature Player runtime.application)
          (runtime.compileProfile whole profile) focal replacement)
        (runtime.serviceEnvironment (runtime.servicePlan roster rounds whole 0) wire)
        ((runtime.servicePlan roster rounds whole 0).map ServiceInstruction.invocation)
        focal suffix site observation left →
      ReachedOwnAction runtime whole inputs
        (Profile.update
          (sig := MessageApplication.policySignature Player runtime.application)
          (runtime.compileProfile whole profile) focal replacement)
        (runtime.serviceEnvironment (runtime.servicePlan roster rounds whole 0) wire)
        ((runtime.servicePlan roster rounds whole 0).map ServiceInstruction.invocation)
        focal suffix site observation right → left = right) :
    let plan := runtime.servicePlan roster rounds whole 0
    let players := Profile.update
      (sig := MessageApplication.policySignature Player runtime.application)
      (runtime.compileProfile whole profile) focal replacement
    let environment := runtime.serviceEnvironment plan wire
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
  let plan := runtime.servicePlan roster rounds whole 0
  let players := Profile.update
    (sig := MessageApplication.policySignature Player runtime.application)
    (runtime.compileProfile whole profile) focal replacement
  let environment := runtime.serviceEnvironment plan wire
  let initial := MessageApplication.PolicyExecution.initial runtime.application
    (MessageApplication.State.initial runtime.application (State.initial whole input))
  have compiled : ∀ actor, actor ≠ focal →
      players actor = runtime.compilePlayerPolicy whole actor (profile actor) := by
    intro actor ne
    exact Profile.update_of_ne _ _ ne
  have independent : IgnoresOwnHistory whole profile focal := by
    change PolicyIgnoresOwnHistory focal whole (profile focal)
    rw [focalPolicy]
    exact runtime.extractedObservationPolicy_ignoresOwnHistory whole inputs
      players environment (plan.map ServiceInstruction.invocation) focal
  have safe := runtime.servicePlan_unilateralDeviation_expirySafe whole profile input unique
    discipline focal replacement roster rounds wire
  apply runtime.runPolicies_deviation_law_of_environment whole profile focal independent input
    players compiled environment plan
  intro before instruction after split isEnvironment execution reached follows
  have cursor : execution.environmentHistory.length =
      (before.filterMap ServiceInstruction.environmentSlot).length := by
    simpa only [MessageApplication.PolicyExecution.initial, List.length_nil, Nat.zero_add] using
      runtime.runPolicies_service_cursor players environment before _ execution reached
  have slot (environmentSlot : instruction.environmentSlot = some instruction) :
      (plan.filterMap ServiceInstruction.environmentSlot)[execution.environmentHistory.length]? =
        some instruction := by
    rw [split, cursor]
    exact ServiceInstruction.environmentSlot_at before after instruction environmentSlot
  have scheduleSplit : plan.map ServiceInstruction.invocation =
      before.map ServiceInstruction.invocation ++
        instruction.invocation :: after.map ServiceInstruction.invocation := by
    rw [split]
    simp
  obtain ⟨target, suffix, site, ideal, values, bindings, candidates, clock, enteredAt,
      walk, atCursor⟩ := (show execution.native.application.Follows whole 0 from follows)
  simp only [Nat.zero_add] at atCursor
  have focalHead : execution.native.application.IsOwnedBy (some focal) ∨
      ¬ execution.native.application.IsOwnedBy (some focal) := Classical.em _
  cases instruction with
  | player actor => cases isEnvironment
  | wire =>
      have kernel := runtime.serviceEnvironment_wire plan wire execution.environmentHistory
        (MessageApplication.State.environmentView runtime.application execution.native) (slot rfl)
      have invokeEq : runtime.application.invoke players environment execution .environment =
          runtime.application.invoke players (runtime.application.wireEnvironment wire)
            execution .environment := by
        simp only [MessageApplication.invoke]
        exact congrArg (fun law => law.bind (runtime.application.environmentPolicyStep execution))
          kernel
      rcases focalHead with owned | notOwned
      · cases suffix with
        | bind name owner fresh tail =>
            simp only [State.IsOwnedBy, atCursor, Option.some.injEq] at owned
            subst owner
            apply (FinDist.bindOnSupport_eq_bind_of_eq_on_support
              (g := fun _ => deviationContinuationAt runtime whole profile focal
                execution.principalHistory execution.native.application follows) ?_).trans
            · exact FinDist.bind_const _ _
            intro next supported
            exact walk.deviationContinuationAt_focal_bind_environment runtime whole
              inputs input inputMem players environment
              (plan.map ServiceInstruction.invocation) (before.map ServiceInstruction.invocation)
              (after.map ServiceInstruction.invocation) scheduleSplit focal locality profile
              focalPolicy site name fresh tail execution next reached supported ideal values
              bindings candidates clock enteredAt atCursor follows (walk.target_names_nodup unique)
        | resolve output owner binding fresh source checks tail =>
            simp only [State.IsOwnedBy, atCursor, Option.some.injEq] at owned
            subst owner
            apply (FinDist.bindOnSupport_eq_bind_of_eq_on_support
              (g := fun _ => deviationContinuationAt runtime whole profile focal
                execution.principalHistory execution.native.application follows) ?_).trans
            · exact FinDist.bind_const _ _
            intro next supported
            exact walk.deviationContinuationAt_focal_resolve_environment runtime whole
              inputs input inputMem unique players environment
              (plan.map ServiceInstruction.invocation) (before.map ServiceInstruction.invocation)
              (after.map ServiceInstruction.invocation) scheduleSplit focal locality profile
              focalPolicy site output binding fresh source checks tail execution next reached
              supported ideal values bindings candidates clock enteredAt atCursor follows
        | ret _ | sample _ _ _ _ => simp [State.IsOwnedBy, atCursor] at owned
      · have law := runtime.deviationContinuationAt_initialized_wire_nonfocal whole profile input
          unique discipline focal independent players compiled environment
          (before.map ServiceInstruction.invocation) execution reached notOwned wire
        dsimp only at law
        have residualEq :
            (runtime.application.invoke players environment execution .environment).bindOnSupport
                (fun next supported => deviationContinuationAt runtime whole profile focal
                  next.principalHistory next.native.application
                  (runtime.invoke_follows whole 0 players environment .environment execution next
                    follows supported)) =
              (runtime.application.invoke players (runtime.application.wireEnvironment wire)
                  execution .environment).bindOnSupport
                (fun next supported => deviationContinuationAt runtime whole profile focal
                  next.principalHistory next.native.application
                  (runtime.invoke_follows whole 0 players
                    (runtime.application.wireEnvironment wire) .environment execution next
                    follows supported)) := by
          apply FinDist.bindOnSupport_congr_measure invokeEq
          intro next _ _
          congr
        exact residualEq.trans law.symm
  | includeLatest owner =>
      let reserved : runtime.application.WirePolicy := fun _ view =>
        match runtime.application.latestSubmissionCommand owner view with
        | .«include» id => FinDist.pure (.«include» id)
        | _ => FinDist.pure .wait
      have kernel : environment execution.environmentHistory
          (MessageApplication.State.environmentView runtime.application execution.native) =
          runtime.application.wireEnvironment reserved execution.environmentHistory
            (MessageApplication.State.environmentView runtime.application execution.native) := by
        simp only [environment, serviceEnvironment, slot rfl]
        rcases runtime.application.latestSubmissionCommand_cases owner
          (MessageApplication.State.environmentView runtime.application execution.native) with
          wait | ⟨id, included⟩
        · simp [reserved, MessageApplication.wireEnvironment, wait,
            WireCommand.toEnvironmentCommand]
        · simp [reserved, MessageApplication.wireEnvironment, included,
            WireCommand.toEnvironmentCommand]
      have invokeEq : runtime.application.invoke players environment execution .environment =
          runtime.application.invoke players (runtime.application.wireEnvironment reserved)
            execution .environment := by
        simp only [MessageApplication.invoke]
        exact congrArg (fun law => law.bind (runtime.application.environmentPolicyStep execution))
          kernel
      rcases focalHead with owned | notOwned
      · cases suffix with
        | bind name phaseOwner fresh tail =>
            simp only [State.IsOwnedBy, atCursor, Option.some.injEq] at owned
            subst phaseOwner
            apply (FinDist.bindOnSupport_eq_bind_of_eq_on_support
              (g := fun _ => deviationContinuationAt runtime whole profile focal
                execution.principalHistory execution.native.application follows) ?_).trans
            · exact FinDist.bind_const _ _
            intro next supported
            exact walk.deviationContinuationAt_focal_bind_environment runtime whole
              inputs input inputMem players environment
              (plan.map ServiceInstruction.invocation) (before.map ServiceInstruction.invocation)
              (after.map ServiceInstruction.invocation) scheduleSplit focal locality profile
              focalPolicy site name fresh tail execution next reached supported ideal values
              bindings candidates clock enteredAt atCursor follows (walk.target_names_nodup unique)
        | resolve output phaseOwner binding fresh source checks tail =>
            simp only [State.IsOwnedBy, atCursor, Option.some.injEq] at owned
            subst phaseOwner
            apply (FinDist.bindOnSupport_eq_bind_of_eq_on_support
              (g := fun _ => deviationContinuationAt runtime whole profile focal
                execution.principalHistory execution.native.application follows) ?_).trans
            · exact FinDist.bind_const _ _
            intro next supported
            exact walk.deviationContinuationAt_focal_resolve_environment runtime whole
              inputs input inputMem unique players environment
              (plan.map ServiceInstruction.invocation) (before.map ServiceInstruction.invocation)
              (after.map ServiceInstruction.invocation) scheduleSplit focal locality profile
              focalPolicy site output binding fresh source checks tail execution next reached
              supported ideal values bindings candidates clock enteredAt atCursor follows
        | ret _ | sample _ _ _ _ => simp [State.IsOwnedBy, atCursor] at owned
      · have law := runtime.deviationContinuationAt_initialized_wire_nonfocal whole profile input
          unique discipline focal independent players compiled environment
          (before.map ServiceInstruction.invocation) execution reached notOwned reserved
        dsimp only at law
        have residualEq :
            (runtime.application.invoke players environment execution .environment).bindOnSupport
                (fun next supported => deviationContinuationAt runtime whole profile focal
                  next.principalHistory next.native.application
                  (runtime.invoke_follows whole 0 players environment .environment execution next
                    follows supported)) =
              (runtime.application.invoke players (runtime.application.wireEnvironment reserved)
                  execution .environment).bindOnSupport
                (fun next supported => deviationContinuationAt runtime whole profile focal
                  next.principalHistory next.native.application
                  (runtime.invoke_follows whole 0 players
                    (runtime.application.wireEnvironment reserved) .environment execution next
                    follows supported)) := by
          apply FinDist.bindOnSupport_congr_measure invokeEq
          intro next _ _
          congr
        exact residualEq.trans law.symm
  | expire phase =>
      have safeHere := safe before phase after split execution reached
      rcases safeHere with stale | sampleOrOwned
      · exact (runtime.deviationContinuationAt_environment_wait whole profile focal execution
          follows players environment (by
            have viewPhase : (MessageApplication.State.environmentView runtime.application
              execution.native).application.pc = execution.native.application.phase := by
              change execution.native.application.publicView.pc = _
              simp
            simp [environment, serviceEnvironment, slot rfl, viewPhase, stale])).symm
      · rcases sampleOrOwned with sample | owned
        · rcases sample with ⟨sampleΓ, name, payload, fresh, law, tail, sampleIdeal,
            sampleValues, sampleBindings, sampleCandidates, pc, sampleClock, sampleEntered,
            sampleCursor⟩
          by_cases current : pc = phase
          · subst phase
            have exactFollows : (State.running (.sample name fresh law tail) sampleIdeal
                sampleValues sampleBindings sampleCandidates pc sampleClock sampleEntered).Follows
                whole 0 := sampleCursor ▸ follows
            obtain ⟨sampleWalk⟩ := State.prefix_of_running_follows whole
              (.sample name fresh law tail) sampleIdeal sampleValues sampleBindings
              sampleCandidates pc sampleClock sampleEntered exactFollows
            have agreement := runtime.runPolicies_preserves_publicAgreement players environment
              (before.map ServiceInstruction.invocation) _ execution
              (State.initial_publicAgreement whole input) reached
            rw [sampleCursor] at agreement
            exact (sampleWalk.deviationContinuationAt_sample_tick runtime whole profile focal
              independent pc name fresh law tail execution sampleIdeal sampleValues sampleBindings
              sampleCandidates sampleClock sampleEntered sampleCursor follows agreement
              (sampleWalk.target_names_nodup unique) players environment (by
                have viewPhase : (MessageApplication.State.environmentView runtime.application
                  execution.native).application.pc = pc := by
                  change execution.native.application.publicView.pc = pc
                  simp [sampleCursor]
                simp [environment, serviceEnvironment, slot rfl, viewPhase])).symm
          · exact (runtime.deviationContinuationAt_environment_wait whole profile focal execution
              follows players environment (by
                have viewPhase : (MessageApplication.State.environmentView runtime.application
                  execution.native).application.pc = pc := by
                  change execution.native.application.publicView.pc = pc
                  simp [sampleCursor]
                simp [environment, serviceEnvironment, slot rfl, viewPhase, current])).symm
        · rcases focalHead with _ | notOwned
          · cases suffix with
            | bind name owner fresh tail =>
                simp only [State.IsOwnedBy, atCursor, Option.some.injEq] at owned
                subst owner
                apply (FinDist.bindOnSupport_eq_bind_of_eq_on_support
                  (g := fun _ => deviationContinuationAt runtime whole profile focal
                    execution.principalHistory execution.native.application follows) ?_).trans
                · exact FinDist.bind_const _ _
                intro next supported
                exact walk.deviationContinuationAt_focal_bind_environment runtime whole
                  inputs input inputMem players environment
                  (plan.map ServiceInstruction.invocation)
                  (before.map ServiceInstruction.invocation)
                  (after.map ServiceInstruction.invocation) scheduleSplit focal locality profile
                  focalPolicy site name fresh tail execution next reached supported ideal values
                  bindings candidates clock enteredAt atCursor follows
                  (walk.target_names_nodup unique)
            | resolve output owner binding fresh source checks tail =>
                simp only [State.IsOwnedBy, atCursor, Option.some.injEq] at owned
                subst owner
                apply (FinDist.bindOnSupport_eq_bind_of_eq_on_support
                  (g := fun _ => deviationContinuationAt runtime whole profile focal
                    execution.principalHistory execution.native.application follows) ?_).trans
                · exact FinDist.bind_const _ _
                intro next supported
                exact walk.deviationContinuationAt_focal_resolve_environment runtime whole
                  inputs input inputMem unique players environment
                  (plan.map ServiceInstruction.invocation)
                  (before.map ServiceInstruction.invocation)
                  (after.map ServiceInstruction.invocation) scheduleSplit focal locality profile
                  focalPolicy site output binding fresh source checks tail execution next reached
                  supported ideal values bindings candidates clock enteredAt atCursor follows
            | ret _ | sample _ _ _ _ => simp [State.IsOwnedBy, atCursor] at owned
          · exact (notOwned owned).elim

/-- A completed execution law is the optional-output map of its sanitized
continuations. -/
theorem deviationOutcome_map_of_continuation
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ Δ)
    (profile : BehavioralProfile whole) (focal : Player)
    (executions : FinDist runtime.application.PolicyExecution)
    (follows : ∀ execution ∈ executions.support,
      execution.native.application.Follows whole 0)
    (completed : ∀ execution ∈ executions.support,
      execution.native.application.outcome?.isSome = true) :
    executions.map (fun execution => execution.native.application.outcome?) =
      (executions.bindOnSupport fun execution supported =>
        deviationContinuationAt runtime whole profile focal execution.principalHistory
          execution.native.application (follows execution supported)).map some := by
  rw [FinDist.map_bindOnSupport]
  symm
  rw [FinDist.map_eq_bind]
  apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
  intro execution supported
  obtain ⟨output, terminal⟩ := Option.isSome_iff_exists.mp (completed execution supported)
  rw [runtime.deviationContinuationAt_terminal whole profile focal
    execution.principalHistory execution.native.application
    (follows execution supported) output terminal]
  simp only [FinDist.map_pure, terminal]

/-- A deterministic native deviation and deterministic wire response have an
exact graph-policy backtranslation over the whole initial-state law whenever
reached focal actions are observation-local. -/
theorem servicedGame_pure_deviation_law_of_locality
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ Δ)
    (profile : BehavioralProfile whole) (inputs : FinDist (VEnv L Γ))
    (unique : (Γ.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (focal : Player) (replacement : runtime.application.PlayerPolicy)
    (roster : List Player) (rounds : Nat) (wire : runtime.application.WirePolicy)
    (locality : ∀ {target} (suffix : Graph Player L target Δ) site
      (observation : Observation L focal target) (left right : OwnAction Player L),
      ReachedOwnAction runtime whole inputs
        (Profile.update
          (sig := MessageApplication.policySignature Player runtime.application)
          (runtime.compileProfile whole profile) focal replacement)
        (runtime.serviceEnvironment (runtime.servicePlan roster rounds whole 0) wire)
        ((runtime.servicePlan roster rounds whole 0).map ServiceInstruction.invocation)
        focal suffix site observation left →
      ReachedOwnAction runtime whole inputs
        (Profile.update
          (sig := MessageApplication.policySignature Player runtime.application)
          (runtime.compileProfile whole profile) focal replacement)
        (runtime.serviceEnvironment (runtime.servicePlan roster rounds whole 0) wire)
        ((runtime.servicePlan roster rounds whole 0).map ServiceInstruction.invocation)
        focal suffix site observation right → left = right) :
    ∃ alternative : BehavioralPolicy focal whole,
      ((runtime.servicedGame whole inputs roster rounds wire).play
        (Profile.update
          (sig := MessageApplication.policySignature Player runtime.application)
          (runtime.compileProfile whole profile) focal replacement)).map
            (fun execution => execution.native.application.outcome?) =
        (inputs.bind fun input => Graph.run whole
          (Profile.update (sig := Graph.gameSignature whole) profile focal alternative)
          input).map some := by
  let plan := runtime.servicePlan roster rounds whole 0
  let nativePlayers := Profile.update
    (sig := MessageApplication.policySignature Player runtime.application)
    (runtime.compileProfile whole profile) focal replacement
  let environment := runtime.serviceEnvironment plan wire
  let alternative := runtime.extractedObservationPolicy whole inputs nativePlayers
    environment (plan.map ServiceInstruction.invocation) focal
  let graphProfile := Profile.update (sig := Graph.gameSignature whole) profile focal alternative
  refine ⟨alternative, ?_⟩
  have playersEq : Profile.update
      (sig := MessageApplication.policySignature Player runtime.application)
      (runtime.compileProfile whole graphProfile) focal replacement = nativePlayers := by
    funext actor
    by_cases same : actor = focal
    · subst actor
      simp only [Profile.update_same, nativePlayers]
    · simp only [compileProfile, graphProfile, Profile.update_of_ne _ _ same, nativePlayers]
  simp only [servicedGame, FinDist.map_bind]
  apply FinDist.bind_congr
  intro input inputMem
  let initial := MessageApplication.PolicyExecution.initial runtime.application
    (MessageApplication.State.initial runtime.application (State.initial whole input))
  let executions := runtime.application.runPolicies nativePlayers environment
    (plan.map ServiceInstruction.invocation) initial
  have follows : ∀ execution ∈ executions.support,
      execution.native.application.Follows whole 0 := fun execution supported =>
    runtime.runPolicies_follows whole 0 nativePlayers environment _ initial execution
      (State.initial_follows whole input) supported
  have completed : ∀ execution ∈ executions.support,
      execution.native.application.outcome?.isSome = true := fun execution supported =>
    runtime.servicePlan_terminates whole input roster rounds nativePlayers wire
      execution supported
  change executions.map (fun execution => execution.native.application.outcome?) = _
  rw [runtime.deviationOutcome_map_of_continuation whole graphProfile focal executions
    follows completed]
  have conserved := runtime.servicePlan_pure_deviation_law_of_locality whole graphProfile
    inputs input inputMem unique discipline focal replacement roster rounds wire
    (by
      simp only [graphProfile, Profile.update_same]
      change alternative = runtime.extractedObservationPolicy whole inputs
        (Profile.update
          (sig := MessageApplication.policySignature Player runtime.application)
          (runtime.compileProfile whole graphProfile) focal replacement)
        environment (plan.map ServiceInstruction.invocation) focal
      rw [playersEq])
    (by
      rw [playersEq]
      exact locality)
  dsimp only at conserved
  rw [playersEq] at conserved
  exact congrArg (FinDist.map some) conserved

end Vegas.GraphRuntime
