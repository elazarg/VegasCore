/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedCheckpoint
import Vegas.Compile.WindowedConditionalOwner
import Vegas.Compile.WindowedConditionalCached
import Vegas.Compile.WindowedBlockSample
import Vegas.Compile.WindowedBlockProgress
import Vegas.Compile.ConditionalDisposition
import Vegas.Compile.ConditionalSnapshot

/-! # Conditional source choices at actual initialized checkpoints

Both conditional accounting cases use the same emitted head. Accepted binding
dispositions, fresh choice caches, and reference dispatch follow from actual
initialized execution. The replacing player's raw policy remains arbitrary.
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
variable {windowOf : Nat → Nat} {roster : List P} {focal owner : P}
variable {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {blockIndex : Nat} {name publicName : VarId} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
variable {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ)}
variable {spec : ConditionalOpening guard}
variable {accounted : CommitmentAccounting pending
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {fresh : FreshBindings
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {state : BuildState P L Γ} {plan : ApplicationPlan accounted fresh state}
variable {profile : SourceBehavioralProfile
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {current : CoupledAt
  (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
    fresh state).graph state}
variable {execution :
  (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution}

/-- Every actual conditional checkpoint has a typed accepted disposition.
Opaque dispositions use the generated owner/slot; public defaults remain
typed source values. This holds even for a deviating conditional owner. -/
theorem conditional_binding_disposition
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex plan profile current execution)
    (head : ConditionalHead spec plan)
    (horigins : (root.image deadlineOf).HasBindingOrigins) :
    let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
    let code := site.code fresh state (site.sourceField fresh state)
      (deadlineOf (site.choice.publicationNode fresh state))
    ∃ disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy),
      code.binding? execution.native.application.base.memory = some disposition ∧
      ∀ handle, disposition = .opaque handle → handle = (owner, site.sourceField fresh state) := by
  intro site code
  let runtime := root.windowed deadlineOf binding choice windowOf
  obtain ⟨rest, hhead⟩ := head.instructions deadlineOf
  have hindexOriginal := checkpoint.instruction_at (.conditional code) rest hhead
  have hindex : runtime.image.instructions[blockIndex]? = some (.conditional code) := by
    simp only [runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts]
  exact ConditionalPublicationSite.bindingDisposition_at_source_prefix guard tail spec fresh state
    (site.sourceField fresh state) (deadlineOf (site.choice.publicationNode fresh state)) current
    runtime.image execution.native.application.base checkpoint.refines checkpoint.resolvedBindings
    ((horigins.withBindingTimeouts binding).withChoiceTimeouts choice)
    (List.mem_of_getElem? hindex)

/-- A reference owner's first conditional poll has the source decision law,
encoded for the actual accepted disposition. Explicit cache freshness also
permits the owner to occupy the distinguished coordinate. -/
theorem conditional_first_poll
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex plan profile current execution)
    (head : ConditionalHead spec plan)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup) (howner : owner ∈ roster)
    (hpolicy :
      root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement owner =
        root.windowedReferencePlayers rootProfile deadlineOf binding choice windowOf owner)
    (hcaches :
      let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
      let code := site.code fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state))
      (.conditional code : ApplicationInstruction P L).CacheEmpty (root.image deadlineOf)
        ((root.windowed deadlineOf binding choice windowOf).eraseExecution execution))
    (disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy))
    (hbinding : let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
      (site.code fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state))).binding?
          execution.native.application.base.memory = some disposition) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
      replacement
    let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
    let encoding := site.choiceEncodingFor fresh state (site.sourceField fresh state)
      (deadlineOf (site.choice.publicationNode fresh state)) disposition
      (ApplicationImage.conditionalTransport spec.secretTy)
    (encoding.submission runtime.application).cachedValue runtime.application
      (execution.principalHistory owner) = none ∧
      players owner (execution.principalHistory owner)
        (State.observe runtime.application execution.native owner) =
          (profile owner site.choice.decision
            ((current.current.source.toView owner).eraseEnv)).map fun chosen =>
              .submit (encoding.encode chosen.1) := by
  intro runtime players site encoding
  let code := site.code fresh state (site.sourceField fresh state)
    (deadlineOf (site.choice.publicationNode fresh state))
  obtain ⟨actual, hactual, hcanonical⟩ := checkpoint.conditional_binding_disposition head horigins
  have heq : actual = disposition := Option.some.inj (hactual.symm.trans hbinding)
  subst actual
  obtain ⟨rest, hhead⟩ := head.instructions deadlineOf
  have hcacheOriginal : (encoding.submission (root.image deadlineOf).application).cachedValue
      (root.image deadlineOf).application
      ((execution.principalHistory owner).map runtime.erasePlayerEntry) = none := by
    convert hcaches disposition using 1
    · rfl
    · cases disposition <;> rfl
  have hcache : (encoding.submission runtime.application).cachedValue runtime.application
      (execution.principalHistory owner) = none :=
    (runtime.cachedValue_erasePlayerEntry (root.image deadlineOf) encoding
      (execution.principalHistory owner)).trans hcacheOriginal
  have hindexOriginal := checkpoint.instruction_at (.conditional code) rest hhead
  have halign := checkpoint.historyAlignment hroster owner howner
  have hindex : runtime.image.instructions[(execution.principalHistory owner).length / 3]? =
      some (.conditional code) := by
    rw [halign.2.2.1]
    simp only [runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts]
  have hsource := ProfileContinuation.windowedConditional_sample_of_unchanged_owner spec head
    checkpoint.continuation deadlineOf binding choice windowOf players (by
      intro history view command hcommand
      rw [show players owner = runtime.blockPlayer owner
          (runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile owner)) from
          hpolicy] at hcommand
      exact runtime.blockPlayer_supported owner (root.liftProfile deadlineOf rootProfile owner)
        history view command hcommand)
    (runtime.blockEnvironment roster)
    (List.replicate blockIndex (WindowedApplication.blockInvocations roster)).flatten
    execution checkpoint.reached current checkpoint.refines
    (head.initialReadsPublic (checkpoint.continuation.initialControllerReadsPublic hinitial))
    disposition hbinding hcanonical hcache (by
      rw [show players owner = runtime.blockPlayer owner
        (runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile owner)) from hpolicy]
      exact runtime.blockPlayer_normal owner _ _ _ (.conditional code) hindex
        (checkpoint.activeAddress?_head (.conditional code) rest hhead)
        (by rw [halign.1]; omega) rfl)
  exact ⟨hcache, hsource.1⟩

/-- At unchanged owner input, the ordinary polls draw exactly once from the
source kernel, submit its disposition-specific packet, and then wait. -/
theorem conditional_polls_source_law_of_input_eq
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex plan profile current execution)
    (head : ConditionalHead spec plan)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup) (howner : owner ∈ roster) (reference : checkpoint.ReferenceOwner owner)
    (disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy))
    (hbinding : let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
      (site.code fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state))).binding?
          execution.native.application.base.memory = some disposition)
    (environment :
      (root.windowed deadlineOf binding choice windowOf).application.EnvironmentPolicy)
    (middle : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hrefines : middle.native.application.base.Refines current.current.graph.1)
    (hinput : (middle.principalHistory owner,
      State.observe (root.windowed deadlineOf binding choice windowOf).application
        middle.native owner) =
        (execution.principalHistory owner,
          State.observe (root.windowed deadlineOf binding choice windowOf).application
            execution.native owner)) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
      replacement
    let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
    let encoding := site.choiceEncodingFor fresh state (site.sourceField fresh state)
      (deadlineOf (site.choice.publicationNode fresh state)) disposition
      (ApplicationImage.conditionalTransport spec.secretTy)
    runtime.application.runPolicies players environment [.player owner, .player owner] middle =
      (profile owner site.choice.decision
        ((current.current.source.toView owner).eraseEnv)).bind fun chosen =>
          (runtime.application.playerStep owner middle (.submit (encoding.encode chosen.1))).bind
            fun submitted => runtime.application.playerStep owner submitted .wait := by
  intro runtime players site encoding
  have hhistory : middle.principalHistory owner = execution.principalHistory owner :=
    congrArg Prod.fst hinput
  have hview : State.observe runtime.application middle.native owner =
      State.observe runtime.application execution.native owner := congrArg Prod.snd hinput
  have hmemory : middle.native.application.base.memory =
      execution.native.application.base.memory :=
    congrArg (fun input => input.2.application.1) hinput
  have hpolicy : players owner = runtime.blockPlayer owner
      (runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile owner)) := reference.policy
  let code := site.code fresh state (site.sourceField fresh state)
    (deadlineOf (site.choice.publicationNode fresh state))
  obtain ⟨rest, hhead⟩ := head.instructions deadlineOf
  obtain ⟨hcache, hfirst⟩ := checkpoint.conditional_first_poll head hinitial horigins hroster
    howner hpolicy (reference.head_cacheEmpty (.conditional code) rest hhead rfl)
    disposition hbinding
  have hindexOriginal := checkpoint.instruction_at (.conditional code) rest hhead
  have hindex : runtime.image.instructions[blockIndex]? = some (.conditional code) := by
    simp only [runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts]
  have halign := checkpoint.historyAlignment hroster owner howner
  change players owner (execution.principalHistory owner)
      (State.observe runtime.application execution.native owner) =
    (profile owner site.choice.decision
      ((current.current.source.toView owner).eraseEnv)).map
        (fun chosen => .submit (encoding.encode chosen.1)) at hfirst
  change runtime.application.runPolicies players environment [.player owner, .player owner]
    middle = _
  simp only [MessageApplication.runPolicies, MessageApplication.invoke, FinDist.bind_pure]
  rw [hhistory, hview, hfirst, FinDist.bind_map, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro chosen _
  apply FinDist.bind_congr
  intro submitted hsubmitted
  have hcacheNext := (encoding.submission runtime.application).playerStep_cachedValue_of_none
    runtime.application owner middle submitted chosen.1 (by rw [hhistory]; exact hcache)
    hsubmitted
  have hrefinesNext := (runtime.playerStep_refines owner middle submitted
    (.submit (encoding.encode chosen.1)) current.current.graph.1 hrefines hsubmitted).1
  have hmemoryNext : submitted.native.application.base.memory =
      execution.native.application.base.memory :=
    (congrArg Prod.fst (runtime.playerStep_publicState owner middle submitted
      (.submit (encoding.encode chosen.1)) hsubmitted)).trans hmemory
  have hlength : (submitted.principalHistory owner).length = blockIndex * 3 + 1 := by
    rw [runtime.application.playerStep_history_self owner middle
      (.submit (encoding.encode chosen.1)) submitted hsubmitted]
    simp only [List.length_append, List.length_cons, List.length_nil, hhistory, halign.1]
    omega
  have hwait := ProfileContinuation.windowedConditional_wait_of_cached spec head
    checkpoint.continuation deadlineOf binding choice windowOf players hpolicy submitted current
    hrefinesNext disposition (by rw [hmemoryNext]; exact hbinding) chosen.1 hcacheNext
    (.conditional code)
    (by rw [hlength]; convert hindex using 1; congr 1; omega)
    (by rw [hmemoryNext]; exact checkpoint.activeAddress?_head (.conditional code) rest hhead)
    (by rw [hlength]; omega) rfl
  rw [hwait, FinDist.pure_bind]

/-- Preceding polls by other principals preserve the exact conditional
source draw and its submit-then-wait law. No delivery or inclusion is performed
in this prefix, but the replacing player's raw polling actions are unrestricted. -/
theorem conditional_polls_source_law_after_others
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex plan profile current execution)
    (head : ConditionalHead spec plan)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup) (howner : owner ∈ roster) (reference : checkpoint.ReferenceOwner owner)
    (disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy))
    (hbinding : let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
      (site.code fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state))).binding?
          execution.native.application.base.memory = some disposition)
    (environment :
      (root.windowed deadlineOf binding choice windowOf).application.EnvironmentPolicy)
    (before : List (@Invocation P)) (henvironment : Invocation.environment ∉ before)
    (hbefore : Invocation.player owner ∉ before) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
      replacement
    let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
    let encoding := site.choiceEncodingFor fresh state (site.sourceField fresh state)
      (deadlineOf (site.choice.publicationNode fresh state)) disposition
      (ApplicationImage.conditionalTransport spec.secretTy)
    runtime.application.runPolicies players environment
      (before ++ [.player owner, .player owner]) execution =
        (runtime.application.runPolicies players environment before execution).bind fun middle =>
          (profile owner site.choice.decision
            ((current.current.source.toView owner).eraseEnv)).bind fun chosen =>
              (runtime.application.playerStep owner middle
                (.submit (encoding.encode chosen.1))).bind fun submitted =>
                  runtime.application.playerStep owner submitted .wait := by
  intro runtime players site encoding
  rw [MessageApplication.runPolicies_append]
  apply FinDist.bind_congr
  intro middle hmiddle
  have hinput := runtime.application.runPolicies_other_input owner
    (fun state actor command _ => by cases command; rfl)
    players environment before henvironment hbefore execution middle hmiddle
  have hrefines := runtime.runPolicies_players_refines players environment before henvironment
    execution middle checkpoint.refines hmiddle
  exact checkpoint.conditional_polls_source_law_of_input_eq head hinitial horigins hroster
    howner reference disposition hbinding environment middle hrefines hinput

/-- A legal successful choice of a reference owner opens the exact frozen
source binding. Snapshot equality follows from real registration provenance,
not from an extra source-to-runtime invariant supplied by the caller. -/
theorem conditional_legal_choice_frozen
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex plan profile current execution)
    (hpolicy :
      root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement owner =
        root.windowedReferencePlayers rootProfile deadlineOf binding choice windowOf owner)
    (haccepted : execution.native.application.base.memory.accepted (state.fieldOf spec.binding) =
      some (.opaque (owner, state.fieldOf spec.binding)))
    (chosen : L.Val ty)
    (hlegal : evalGuard guard chosen ((current.current.source.toView owner).eraseEnv) = true) :
    ∀ value, spec.encoding chosen = some value →
      (execution.native.application.base.frozen (state.fieldOf spec.binding)).bind
        (fun typed => typed.as? spec.secretTy) = some value := by
  exact ConditionalPublicationSite.legal_choice_frozen guard tail spec fresh state current
    (root.windowed deadlineOf binding choice windowOf).image
    ((execution.principalHistory owner).map fun entry =>
      show (root.windowed deadlineOf binding choice windowOf).image.application.PlayerEntry from
        (root.windowed deadlineOf binding choice windowOf).erasePlayerEntry entry)
    execution.native.application.base checkpoint.refines
    (checkpoint.registeredBindings owner hpolicy)
    haccepted chosen hlegal

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.conditional_binding_disposition'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.conditional_binding_disposition

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.conditional_first_poll'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.conditional_first_poll

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.conditional_polls_source_law_of_input_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.conditional_polls_source_law_of_input_eq

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.conditional_polls_source_law_after_others'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.conditional_polls_source_law_after_others

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.conditional_legal_choice_frozen'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.conditional_legal_choice_frozen
