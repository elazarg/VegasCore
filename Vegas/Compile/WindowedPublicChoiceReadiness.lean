/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedCheckpoint
import Vegas.Compile.WindowedPublicChoiceOwner
import Vegas.Compile.WindowedPublicChoiceCached
import Vegas.Compile.WindowedBlockSample
import Vegas.Compile.WindowedBlockProgress

/-! # Generated public-choice polls at actual source checkpoints

The unchanged owner's first ordinary poll samples the source kernel and submits
its public value. Cache freshness, source readout, and block alignment are
derived from the initialized checkpoint, not supplied as policy-law premises.
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
variable {blockIndex : Nat} {name publicName : VarId} {owner : P} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
variable {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ)}
variable {newName : name ∉ pending} {unresolved : name ∈ insert name pending}
variable {accounted : CommitmentAccounting ((insert name pending).erase name) tail}
variable {fresh : FreshBindings
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {state : BuildState P L Γ}
variable {publicGuard :
  (PublicChoiceSite.atHead name publicName owner guard tail).PubliclyValidatable fresh state}
variable {nextPlan : ApplicationPlan accounted fresh.2.2
  (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
    publicName owner .here fresh.2.1).1}
variable {profile : SourceBehavioralProfile
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {current : CoupledAt
  (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
    fresh state).graph state}
variable {execution :
  (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution}

/-- A reference owner's first ordinary command has exactly the encoded
source decision law when its cache is fresh. The owner may occupy the
distinguished coordinate; its source policy may randomize. -/
theorem publicChoice_first_poll
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.publicChoice (newName := newName) (unresolved := unresolved)
        publicGuard nextPlan) profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (hroster : roster.Nodup) (howner : owner ∈ roster)
    (hpolicy :
      root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement owner =
        root.windowedReferencePlayers rootProfile deadlineOf binding choice windowOf owner)
    (hcaches :
      (.publicChoice ((PublicChoiceSite.atHead name publicName owner guard tail).code fresh state) :
        ApplicationInstruction P L).CacheEmpty (root.image deadlineOf)
          ((root.windowed deadlineOf binding choice windowOf).eraseExecution execution)) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
      replacement
    let encoding := ApplicationImage.choiceEncoding (P := P) (state.nodes.length + 1) ty
    (encoding.submission runtime.application).cachedValue runtime.application
      (execution.principalHistory owner) = none ∧
      players owner (execution.principalHistory owner)
        (State.observe runtime.application execution.native owner) =
          (profile owner (.here guard (.reveal publicName owner name .here tail))
            ((current.current.source.toView owner).eraseEnv)).map fun chosen =>
              .submit (encoding.encode chosen.1) := by
  intro runtime players encoding
  let site := PublicChoiceSite.atHead name publicName owner guard tail
  let code := site.code fresh state
  let instruction : ApplicationInstruction P L := .publicChoice { code with timeout := choice code }
  have hhead : (ApplicationPlan.publicChoice (newName := newName) (unresolved := unresolved)
      (fresh := fresh) publicGuard nextPlan).instructions deadlineOf =
        .publicChoice code :: nextPlan.instructions deadlineOf := rfl
  have hcache : (encoding.submission runtime.application).cachedValue runtime.application
      (execution.principalHistory owner) = none :=
    (runtime.cachedValue_erasePlayerEntry (root.image deadlineOf) encoding
      (execution.principalHistory owner)).trans hcaches
  have hindexOriginal := checkpoint.instruction_at (.publicChoice code) _ hhead
  have halign := checkpoint.historyAlignment hroster owner howner
  have hindex : runtime.image.instructions[(execution.principalHistory owner).length / 3]? =
      some instruction := by
    rw [halign.2.2.1]
    simp only [runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts, instruction]
  have hinitialHead := checkpoint.continuation.initialControllerReadsPublic hinitial
  have hsource := checkpoint.continuation.windowedPublicChoice_sample_of_unchanged_owner
    deadlineOf binding choice windowOf players hpolicy (runtime.blockEnvironment roster)
    (List.replicate blockIndex (WindowedApplication.blockInvocations roster)).flatten
    execution checkpoint.reached current checkpoint.refines hinitialHead.1 hcache
    instruction hindex (checkpoint.activeAddress?_head (.publicChoice code) _ hhead)
    (by rw [halign.1]; omega) rfl
  exact ⟨hcache, hsource.1⟩

/-- At reference-owner input and source refinement, the two ordinary polls
sample once, submit the chosen public value, then wait. This retains the exact
native execution law, including the submitted packet and both local entries. -/
theorem publicChoice_polls_source_law_of_input_eq
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.publicChoice (newName := newName) (unresolved := unresolved)
        publicGuard nextPlan) profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (hroster : roster.Nodup) (howner : owner ∈ roster)
    (reference : checkpoint.ReferenceOwner owner)
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
    let encoding := ApplicationImage.choiceEncoding (P := P) (state.nodes.length + 1) ty
    runtime.application.runPolicies players environment [.player owner, .player owner] middle =
      (profile owner (.here guard (.reveal publicName owner name .here tail))
        ((current.current.source.toView owner).eraseEnv)).bind fun chosen =>
          (runtime.application.playerStep owner middle (.submit (encoding.encode chosen.1))).bind
            fun submitted => runtime.application.playerStep owner submitted .wait := by
  intro runtime players encoding
  have hhistory : middle.principalHistory owner = execution.principalHistory owner :=
    congrArg Prod.fst hinput
  have hview : State.observe runtime.application middle.native owner =
      State.observe runtime.application execution.native owner := congrArg Prod.snd hinput
  have hmemory : middle.native.application.base.memory =
      execution.native.application.base.memory :=
    congrArg (fun input => input.2.application.1) hinput
  have hpolicy : players owner = runtime.blockPlayer owner
      (runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile owner)) :=
    reference.policy
  let site := PublicChoiceSite.atHead name publicName owner guard tail
  let code := site.code fresh state
  let instruction : ApplicationInstruction P L := .publicChoice { code with timeout := choice code }
  have hhead : (ApplicationPlan.publicChoice (newName := newName) (unresolved := unresolved)
      (fresh := fresh) publicGuard nextPlan).instructions deadlineOf =
        .publicChoice code :: nextPlan.instructions deadlineOf := rfl
  have hindexOriginal := checkpoint.instruction_at (.publicChoice code) _ hhead
  have hindex : runtime.image.instructions[blockIndex]? = some instruction := by
    simp only [runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts, instruction]
  have halign := checkpoint.historyAlignment hroster owner howner
  obtain ⟨hcache, hfirst⟩ := checkpoint.publicChoice_first_poll hinitial hroster howner hpolicy
    (reference.head_cacheEmpty (.publicChoice code) _ hhead rfl)
  change players owner (execution.principalHistory owner)
      (State.observe runtime.application execution.native owner) =
    (profile owner (.here guard (.reveal publicName owner name .here tail))
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
  have hwait := checkpoint.continuation.windowedPublicChoice_wait_of_cached
    deadlineOf binding choice windowOf players hpolicy submitted current hrefinesNext chosen.1
    hcacheNext instruction
    (by rw [hlength]; convert hindex using 1; congr 1; omega)
    (by rw [hmemoryNext]; exact checkpoint.activeAddress?_head (.publicChoice code) _ hhead)
    (by rw [hlength]; omega) rfl
  rw [hwait, FinDist.pure_bind]

/-- Other principals' preceding raw polls preserve the exact source kernel
and sample-once submission law. They may register, submit, replay, or randomize;
there are no delivery or inclusion turns in this polling prefix. -/
theorem publicChoice_polls_source_law_after_others
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.publicChoice (newName := newName) (unresolved := unresolved)
        publicGuard nextPlan) profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (hroster : roster.Nodup) (howner : owner ∈ roster)
    (reference : checkpoint.ReferenceOwner owner)
    (environment :
      (root.windowed deadlineOf binding choice windowOf).application.EnvironmentPolicy)
    (before : List (@Invocation P)) (henvironment : Invocation.environment ∉ before)
    (hbefore : Invocation.player owner ∉ before) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
      replacement
    let encoding := ApplicationImage.choiceEncoding (P := P) (state.nodes.length + 1) ty
    runtime.application.runPolicies players environment
      (before ++ [.player owner, .player owner]) execution =
        (runtime.application.runPolicies players environment before execution).bind fun middle =>
          (profile owner (.here guard (.reveal publicName owner name .here tail))
            ((current.current.source.toView owner).eraseEnv)).bind fun chosen =>
              (runtime.application.playerStep owner middle
                (.submit (encoding.encode chosen.1))).bind fun submitted =>
                  runtime.application.playerStep owner submitted .wait := by
  intro runtime players encoding
  rw [MessageApplication.runPolicies_append]
  apply FinDist.bind_congr
  intro middle hmiddle
  have hinput := runtime.application.runPolicies_other_input owner
    (fun state actor command _ => by cases command; rfl)
    players environment before henvironment hbefore execution middle hmiddle
  have hrefines := runtime.runPolicies_players_refines players environment before henvironment
    execution middle checkpoint.refines hmiddle
  exact checkpoint.publicChoice_polls_source_law_of_input_eq hinitial hroster howner reference
    environment middle hrefines hinput

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_first_poll'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_first_poll

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_polls_source_law_of_input_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_polls_source_law_of_input_eq

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_polls_source_law_after_others'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_polls_source_law_after_others
