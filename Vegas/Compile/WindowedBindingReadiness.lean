/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedCheckpoint
import Vegas.Compile.WindowedBindingOwner
import Vegas.Compile.WindowedBindingLocality

/-! # Generated binding polls at initialized source checkpoints

Source readout, cache freshness, policy dispatch, and service alignment are
derived from the actual checkpoint. The eligibility premise concerns public
initial inputs read by the generated reference policies; the focal replacement
remains an unrestricted native policy.
-/

noncomputable section

namespace Vegas.ApplicationPlan.WindowedCheckpoint

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
variable {rootProg : VegasCore P L rootContext}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
variable {root : ApplicationPlan rootAccounted rootFresh rootState}
variable {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
variable {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
variable {choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)}
variable {windowOf : Nat → Nat} {roster : List P} {focal : P}
variable {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {blockIndex : Nat} {name : VarId} {owner : P} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
variable {tail : VegasCore P L ((name, .sealed owner ty) :: Γ)}
variable {newName : name ∉ pending}
variable {accounted : CommitmentAccounting (insert name pending) tail}
variable {fresh : FreshBindings (.commit name owner guard tail)} {state : BuildState P L Γ}
variable {unrestricted : UnrestrictedBinding guard}
variable {nextPlan : ApplicationPlan accounted fresh.2
  (state.addCommitEvent name owner guard fresh.1).1}
variable {profile : SourceBehavioralProfile (.commit name owner guard tail)}
variable {current : CoupledAt (compileCore (.commit name owner guard tail) fresh state).graph state}
variable {execution :
  (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution}

/-- The root source profile really selects the head binding policy at this
checkpoint, for every history supplied to that policy. Completed-prefix
refinement supplies the dispatch facts; no policy-equality premise is assumed. -/
theorem binding_dispatch
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
      profile current execution) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let image := root.image deadlineOf
    let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
      .here guard tail
    ∀ history, root.liftProfile deadlineOf rootProfile owner history
        (State.observe image.application (runtime.eraseExecution execution).native owner) =
      site.bindingPolicy fresh state image (profile owner site) history
        (State.observe image.application (runtime.eraseExecution execution).native owner) := by
  intro runtime image site history
  unfold ApplicationPlan.liftProfile
  rw [checkpoint.continuation.liftProfileIn_eq_of_refines image deadlineOf current
    (runtime.eraseExecution execution).native checkpoint.refines owner history]
  have hready := SourceDecisionSite.binding_ready_at_source_prefix guard tail fresh state
    current execution.native.application.base.memory.done checkpoint.refines.memory.completed
  have hdone : (State.observe image.application
      (runtime.eraseExecution execution).native owner).application.done state.nodes.length =
        false := hready.2.1
  simp only [ApplicationPlan.liftProfileIn, hdone, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- The next binding slot has no prior private registration whenever its
current instruction cache is empty. -/
theorem binding_preparation_empty_of_cacheEmpty
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
      profile current execution)
    (hcaches :
      let runtime := root.windowed deadlineOf binding choice windowOf
      let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
        .here guard tail
      let code := site.bindingCode fresh state (site.compiledField fresh state)
      (.bind code : ApplicationInstruction P L).CacheEmpty (root.image deadlineOf)
        (runtime.eraseExecution execution)) :
    execution.native.application.base.prepared.lookup (owner, state.nextField) = none := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
    .here guard tail
  let code := site.bindingCode fresh state (site.compiledField fresh state)
  have hconsistent := checkpoint.registrationConsistent owner state.nextField
  have hcached := (runtime.registrationCache_erasePlayerEntry (root.image deadlineOf)
    state.nextField (execution.principalHistory owner)).trans hcaches.1
  have hprojection := runtime.registrationCache_erasePlayerEntry runtime.image
    state.nextField (execution.principalHistory owner)
  exact hconsistent.symm.trans (hprojection.symm.trans hcached)

/-- An unchanged owner supplies an empty cache certificate for the binding at
the current head. -/
theorem binding_head_cacheEmpty
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
      profile current execution)
    (hother : owner ≠ focal) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
      .here guard tail
    let code := site.bindingCode fresh state (site.compiledField fresh state)
    (.bind code : ApplicationInstruction P L).CacheEmpty (root.image deadlineOf)
      (runtime.eraseExecution execution) := by
  intro runtime site code
  have hhead : (ApplicationPlan.binding (newName := newName) (fresh := fresh)
      unrestricted nextPlan).instructions deadlineOf = .bind code ::
        nextPlan.instructions deadlineOf := rfl
  exact checkpoint.head_cacheEmpty (.bind code) _ hhead
    (fun heq => hother (Option.some.inj heq))

/-- An unchanged owner's next binding slot has no prior private registration.
Freshness follows from actual history and write-once storage consistency,
not from the registration command being able to overwrite a previous value. -/
theorem binding_preparation_empty
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
      profile current execution)
    (hother : owner ≠ focal) :
    execution.native.application.base.prepared.lookup (owner, state.nextField) = none :=
  checkpoint.binding_preparation_empty_of_cacheEmpty
    (checkpoint.binding_head_cacheEmpty hother)

/-- Explicit reference-policy and cache facts supply the local prerequisites
of the two-poll binding law, including at the distinguished coordinate. -/
theorem binding_polls_ready_of_policy_cacheEmpty
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
      profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (hroster : roster.Nodup) (howner : owner ∈ roster)
    (hpolicy :
      let runtime := root.windowed deadlineOf binding choice windowOf
      let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf
        focal replacement
      players owner = runtime.blockPlayer owner
        (runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile owner)))
    (hcaches :
      let runtime := root.windowed deadlineOf binding choice windowOf
      let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
        .here guard tail
      let code := site.bindingCode fresh state (site.compiledField fresh state)
      (.bind code : ApplicationInstruction P L).CacheEmpty (root.image deadlineOf)
        (runtime.eraseExecution execution)) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
      .here guard tail
    let code := site.bindingCode fresh state (site.compiledField fresh state)
    site.WindowedBindingPollsReady fresh state (root.image deadlineOf) runtime
      (.bind { code with timeout := binding code }) execution current.current.source := by
  intro runtime site code
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf
    focal replacement
  have hhead : (ApplicationPlan.binding (newName := newName) (fresh := fresh)
      unrestricted nextPlan).instructions deadlineOf = .bind code ::
        nextPlan.instructions deadlineOf := rfl
  have hready := SourceDecisionSite.binding_ready_at_source_prefix guard tail fresh state
    current execution.native.application.base.memory.done checkpoint.refines.memory.completed
  have hunbound : execution.native.application.base.memory.accepted
      (site.compiledField fresh state) = none := by
    rw [← site.bindingCode_sourceField fresh state (site.compiledField fresh state)]
    exact checkpoint.refines.accepted_eq_none_of_not_done
      (site.compiledNode fresh state) hready.1.1
  have hresolved : code.resolved execution.native.application.base.memory = false := by
    rw [BindingCode.resolved, site.bindingCode_sourceField, hunbound]
    exact hready.2.1
  have hinitialHead := checkpoint.continuation.initialControllerReadsPublic hinitial
  obtain ⟨reads, hreadout, _, hview⟩ :=
    checkpoint.continuation.windowedBlock_ownerReadout?_of_ready_source_view deadlineOf
      binding choice windowOf owner players hpolicy (runtime.blockEnvironment roster)
      (List.replicate blockIndex (WindowedApplication.blockInvocations roster)).flatten
      execution checkpoint.reached site current.current.graph.1 checkpoint.refines hready.1
      hinitialHead.1 current.current.source (BuildState.Agrees.view current.current.agrees owner)
  have hindex := checkpoint.instruction_at (.bind code) _ hhead
  have halign := checkpoint.historyAlignment hroster owner howner
  refine ⟨hresolved, hready.2.2, hcaches.1, hcaches.2, ?_, ?_, ?_, ?_, rfl⟩
  · refine ⟨reads, ?_, hview⟩
    exact (runtime.ownerReadout?_erasePlayerEntry (root.image deadlineOf) owner
      (eventGuardOf (decisionSiteState site fresh state) owner guard).choiceReads
      (execution.principalHistory owner)
      (State.observe runtime.application execution.native owner)).symm.trans hreadout
  · rw [halign.2.2.1]
    simp only [runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindex, Option.map_some, ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts]
  · exact checkpoint.activeAddress?_head (.bind code) _ hhead
  · rw [halign.1]
    omega

/-- Every local prerequisite of the generated two-poll binding law follows
from an initialized checkpoint, the unchanged owner's roster position, and
the root's public-initial-read eligibility. -/
theorem binding_polls_ready
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
      profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
      .here guard tail
    let code := site.bindingCode fresh state (site.compiledField fresh state)
    site.WindowedBindingPollsReady fresh state (root.image deadlineOf) runtime
      (.bind { code with timeout := binding code }) execution current.current.source := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf
    focal replacement
  have hpolicy : players owner = runtime.blockPlayer owner
      (runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile owner)) := by
    simp only [players, windowedPlayers, Function.update_of_ne hother, windowedReferencePlayers]
    rfl
  exact checkpoint.binding_polls_ready_of_policy_cacheEmpty hinitial hroster howner hpolicy
    (checkpoint.binding_head_cacheEmpty hother)

/-- The original compiled reference profile samples the current source
binding exactly once at an actual checkpoint and then submits its opaque
handle. All cache, readout, and dispatch obligations are derived. -/
theorem binding_polls_source_law
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
      profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal)
    (environment :
      (root.windowed deadlineOf binding choice windowOf).application.EnvironmentPolicy) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
      .here guard tail
    runtime.application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      environment [.player owner, .player owner] execution =
        (profile owner site ((current.current.source.toView owner).eraseEnv)).bind fun chosen =>
          (runtime.application.playerStep owner execution
            (.privateCommand (.register (site.compiledField fresh state) ⟨ty, chosen.1⟩))).bind
              fun registered => runtime.application.playerStep owner registered
                (.submit (.binding
                  (site.bindingCode fresh state (site.compiledField fresh state)).node
                  (owner, site.compiledField fresh state))) := by
  intro runtime site
  apply site.windowedBinding_two_invocations_source_law fresh state (root.image deadlineOf)
    runtime (profile owner site) (root.liftProfile deadlineOf rootProfile owner)
    (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
    environment _
    (.bind { site.bindingCode fresh state (site.compiledField fresh state) with
      timeout := binding (site.bindingCode fresh state (site.compiledField fresh state)) })
    execution current.current.source checkpoint.binding_dispatch
    (checkpoint.binding_polls_ready hinitial hroster howner hother)
  simp only [windowedPlayers, Function.update_of_ne hother, windowedReferencePlayers]
  rfl

/-- The generated two-poll law is unchanged when the owner's actual policy
input is unchanged. Hidden preparations of other principals need not agree. -/
theorem binding_polls_source_law_of_input_eq
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
      profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal)
    (environment :
      (root.windowed deadlineOf binding choice windowOf).application.EnvironmentPolicy)
    (middle : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hinput : (middle.principalHistory owner,
      State.observe (root.windowed deadlineOf binding choice windowOf).application
        middle.native owner) =
        (execution.principalHistory owner,
          State.observe (root.windowed deadlineOf binding choice windowOf).application
            execution.native owner)) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf
      focal replacement
    let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
      .here guard tail
    runtime.application.runPolicies players environment [.player owner, .player owner] middle =
      (profile owner site ((current.current.source.toView owner).eraseEnv)).bind fun chosen =>
        (runtime.application.playerStep owner middle
          (.privateCommand (.register (site.compiledField fresh state) ⟨ty, chosen.1⟩))).bind
            fun registered => runtime.application.playerStep owner registered
              (.submit (.binding
                (site.bindingCode fresh state (site.compiledField fresh state)).node
                  (owner, site.compiledField fresh state))) := by
  intro runtime players site
  have ready := (checkpoint.binding_polls_ready hinitial hroster howner hother).of_input_eq hinput
  apply site.windowedBinding_two_invocations_source_law fresh state (root.image deadlineOf)
    runtime (profile owner site) (root.liftProfile deadlineOf rootProfile owner)
    players environment _ _ middle current.current.source _ ready
  · simp only [players, windowedPlayers, Function.update_of_ne hother, windowedReferencePlayers]
    rfl
  · have hview : State.observe (root.image deadlineOf).application
        (runtime.eraseExecution middle).native owner =
        State.observe (root.image deadlineOf).application
          (runtime.eraseExecution execution).native owner :=
      congrArg runtime.eraseView (congrArg Prod.snd hinput)
    intro history
    rw [hview]
    exact checkpoint.binding_dispatch history

/-- Any preceding polls of other principals retain the exact source binding
kernel at the owner's two ordinary polls. The earlier raw commands and native
states remain in the joint law. Environment turns are excluded here because
delivery or inclusion may change the owner's information. -/
theorem binding_polls_source_law_after_others
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
      profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal)
    (environment :
      (root.windowed deadlineOf binding choice windowOf).application.EnvironmentPolicy)
    (before : List (@Invocation P)) (henvironment : Invocation.environment ∉ before)
    (hbefore : Invocation.player owner ∉ before) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf
      focal replacement
    let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
      .here guard tail
    runtime.application.runPolicies players environment
      (before ++ [.player owner, .player owner]) execution =
        (runtime.application.runPolicies players environment before execution).bind fun middle =>
          (profile owner site ((current.current.source.toView owner).eraseEnv)).bind fun chosen =>
            (runtime.application.playerStep owner middle
              (.privateCommand (.register (site.compiledField fresh state) ⟨ty, chosen.1⟩))).bind
                fun registered => runtime.application.playerStep owner registered
                  (.submit (.binding
                    (site.bindingCode fresh state (site.compiledField fresh state)).node
                    (owner, site.compiledField fresh state))) := by
  intro runtime players site
  rw [MessageApplication.runPolicies_append]
  apply FinDist.bind_congr
  intro middle hmiddle
  have hinput := runtime.application.runPolicies_other_input owner
    (fun state actor command _ => by cases command; rfl)
    players environment before henvironment hbefore execution middle hmiddle
  exact checkpoint.binding_polls_source_law_of_input_eq hinitial hroster howner hother
    environment middle hinput

/-- Paired initialized source checkpoints instantiate the binding inclusion
privacy theorem. Only the initial paired information invariant is supplied;
all controller prerequisites, exact sampling laws, and selected-message
freshness are derived from the actual checkpoints. This is a local segment,
not yet the complete-block or whole-prefix information theorem. -/
theorem binding_inclusion_agreement
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
      profile current execution)
    (rightCurrent :
      CoupledAt (compileCore (.commit name owner guard tail) fresh state).graph state)
    (rightExecution :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (rightCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
      profile rightCurrent rightExecution)
    (agreement : WindowedApplication.PolicyAgreement
      (root.windowed deadlineOf binding choice windowOf) focal execution rightExecution)
    (hinitial : root.InitialControllerReadsPublic)
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal)
    (leftFinal rightFinal :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hleft : leftFinal ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).application.includeLatestFrom owner)
        [.player owner, .player owner, .environment] execution).support)
    (hright : rightFinal ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).application.includeLatestFrom owner)
        [.player owner, .player owner, .environment] rightExecution).support) :
    WindowedApplication.PolicyAgreement
      (root.windowed deadlineOf binding choice windowOf) focal leftFinal rightFinal := by
  let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
    .here guard tail
  let code := site.bindingCode fresh state (site.compiledField fresh state)
  apply agreement.binding_inclusion_of_ready hother site fresh state (root.image deadlineOf)
    (profile owner site) (root.liftProfile deadlineOf rootProfile owner)
    (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement) _
    (.bind { code with timeout := binding code }) current.current.source rightCurrent.current.source
    (checkpoint.binding_polls_ready hinitial hroster howner hother)
    (rightCheckpoint.binding_polls_ready hinitial hroster howner hother)
    checkpoint.binding_dispatch rightCheckpoint.binding_dispatch
    (checkpoint.serialsBeforeNext.lookup_nextSerial_eq_none owner) leftFinal rightFinal hleft hright
  simp only [windowedPlayers, Function.update_of_ne hother, windowedReferencePlayers]

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.binding_dispatch' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.binding_dispatch

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.binding_preparation_empty_of_cacheEmpty'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.binding_preparation_empty_of_cacheEmpty

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.binding_preparation_empty'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.binding_preparation_empty

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.binding_polls_ready_of_policy_cacheEmpty'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.binding_polls_ready_of_policy_cacheEmpty

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.binding_polls_ready' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.binding_polls_ready

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.binding_polls_source_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.binding_polls_source_law

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.binding_polls_source_law_after_others'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.binding_polls_source_law_after_others

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.binding_inclusion_agreement' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.binding_inclusion_agreement
