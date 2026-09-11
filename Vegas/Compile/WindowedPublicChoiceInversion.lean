/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationSampleOnce
import Vegas.Compile.SourceAdequacy
import Vegas.Compile.WindowedNormalSuffix
import Vegas.Compile.WindowedPublicChoiceSubmission
import Vegas.Compile.WindowedPublicChoiceReadiness

/-! # Support inversion for ordinary public-choice polls -/

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
variable {replacement :
  (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {blockIndex : Nat} {name publicName : VarId} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
variable {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ)}
variable {newName : name ∉ pending} {unresolved : name ∈ insert name pending}
variable {accounted : CommitmentAccounting ((insert name pending).erase name) tail}
variable {fresh : FreshBindings
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {state : BuildState P L Γ}

/-- A supported complete ordinary public-choice poll determines a supported
source value and the corresponding concrete submit/wait branch. -/
theorem publicChoice_ordinary_support_value
    (publicGuard :
      (PublicChoiceSite.atHead name publicName owner guard tail).PubliclyValidatable fresh state)
    (nextPlan : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1)
    (profile : SourceBehavioralProfile
      (.commit name owner guard (.reveal publicName owner name .here tail)))
    (current : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state)
    (execution polled :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      roster focal replacement blockIndex (.publicChoice (newName := newName)
        (unresolved := unresolved) publicGuard nextPlan) profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal)
    (beforeRoster afterRoster : List P)
    (hsplit : roster = beforeRoster ++ owner :: afterRoster)
    (hpolled : polled ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (roster.flatMap fun actor => [.player actor, .player actor]) execution).support) :
    ∃ value,
      value ∈ ((profile owner (.here guard (.reveal publicName owner name .here tail))
        ((current.current.source.toView owner).eraseEnv)).map Subtype.val).support ∧
      polled ∈ (let runtime := root.windowed deadlineOf binding choice windowOf
        let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
          replacement
        let environment := runtime.blockEnvironment roster
        (runtime.application.runPolicies players environment
          (beforeRoster.flatMap fun actor => [.player actor, .player actor]) execution).bind
            fun middle =>
              (runtime.application.playerStep owner middle
                (.submit (.choice (state.nodes.length + 1) ⟨ty, value⟩))).bind fun submitted =>
                  (runtime.application.playerStep owner submitted .wait).bind fun waited =>
                    runtime.application.runPolicies players environment
                      (afterRoster.flatMap fun actor => [.player actor, .player actor])
                        waited).support := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf
    focal replacement
  let environment := runtime.blockEnvironment roster
  let before := beforeRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  let site := PublicChoiceSite.atHead name publicName owner guard tail
  let kernel := (profile owner (.here guard (.reveal publicName owner name .here tail))
    ((current.current.source.toView owner).eraseEnv)).map Subtype.val
  have hbeforeOwner : Invocation.player owner ∉ before := by
    have hnot : owner ∉ beforeRoster := by
      intro hmem
      exact (List.nodup_append.mp (hsplit ▸ hroster)).2.2 owner hmem owner (by simp) rfl
    simp [before, hnot]
  apply runtime.application.ordinary_submit_wait_support_value owner
    (fun value : L.Val ty => .choice (state.nodes.length + 1) ⟨ty, value⟩)
    players environment roster beforeRoster afterRoster hsplit execution polled kernel
  · intro middle hmiddle
    have hinput := runtime.application.runPolicies_other_input owner
      (fun state actor command _ => by cases command; rfl)
      players environment before (by simp [before]) hbeforeOwner execution middle hmiddle
    have hrefines := runtime.runPolicies_players_refines players environment before
      (by simp [before]) execution middle checkpoint.refines hmiddle
    change runtime.application.runPolicies players environment
      [.player owner, .player owner] middle = _
    simpa only [kernel, FinDist.bind_map, ApplicationImage.choiceEncoding] using
      checkpoint.publicChoice_polls_source_law_of_input_eq hinitial hroster howner hother
        environment middle hrefines hinput
  · exact hpolled

/-- A complete public-choice block identifies the source value recorded by
its successor checkpoint with the actual supported ordinary submission. -/
theorem publicChoice_block_support_at_source
    (publicGuard :
      (PublicChoiceSite.atHead name publicName owner guard tail).PubliclyValidatable fresh state)
    (nextPlan : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1)
    (profile : SourceBehavioralProfile
      (.commit name owner guard (.reveal publicName owner name .here tail)))
    (current : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      roster focal replacement blockIndex (.publicChoice (newName := newName)
        (unresolved := unresolved) publicGuard nextPlan) profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal)
    (beforeRoster afterRoster : List P)
    (hsplit : roster = beforeRoster ++ owner :: afterRoster)
    (value : L.Val ty)
    (sourceNext : CoupledAt
      (compileCore tail fresh.2.2
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1).graph
      (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1)
    (hsource : sourceNext.current.source = (current.current.source.cons value).cons value)
    (hrefines : final.native.application.base.Refines sourceNext.current.graph.1)
    (hfinal : final ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) execution).support) :
    ∃ polled,
      value ∈ ((profile owner (.here guard (.reveal publicName owner name .here tail))
          ((current.current.source.toView owner).eraseEnv)).map Subtype.val).support ∧
        polled ∈ (let runtime := root.windowed deadlineOf binding choice windowOf
          let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
            replacement
          let environment := runtime.blockEnvironment roster
          (runtime.application.runPolicies players environment
            (beforeRoster.flatMap fun actor => [.player actor, .player actor]) execution).bind
              fun middle =>
                (runtime.application.playerStep owner middle
                  (.submit (.choice (state.nodes.length + 1) ⟨ty, value⟩))).bind fun submitted =>
                    (runtime.application.playerStep owner submitted .wait).bind fun waited =>
                      runtime.application.runPolicies players environment
                        (afterRoster.flatMap fun actor => [.player actor, .player actor])
                          waited).support ∧
        ∃ included,
          included ∈ ((root.windowed deadlineOf binding choice windowOf).application.invoke
            (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
            ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
            polled .environment).support ∧
          final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
            (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
            ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
            (.environment :: roster.flatMap
              (fun actor => [Invocation.player actor, .environment])) included).support := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let environment := runtime.blockEnvironment roster
  let site := PublicChoiceSite.atHead name publicName owner guard tail
  let code := site.code fresh state
  let timed : PublicChoiceCode P L := { code with timeout := choice code }
  let polls := roster.flatMap fun actor => [Invocation.player actor, .player actor]
  let suffix := Invocation.environment ::
    roster.flatMap fun actor => [Invocation.player actor, .environment]
  have hdecompose : WindowedApplication.blockInvocations roster =
      polls ++ (.environment :: suffix) := by
    simp only [WindowedApplication.blockInvocations, polls, suffix, List.append_assoc,
      List.cons_append, List.nil_append]
  rw [hdecompose, MessageApplication.runPolicies_append] at hfinal
  simp only [FinDist.support_bind, Set.mem_iUnion, MessageApplication.runPolicies] at hfinal
  obtain ⟨polled, hpolled, included, hincluded, hremaining⟩ := hfinal
  obtain ⟨drawn, hdrawn, hbranch⟩ := checkpoint.publicChoice_ordinary_support_value
    publicGuard nextPlan profile current execution polled hinitial hroster howner hother
    beforeRoster afterRoster hsplit hpolled
  obtain ⟨chosen, hchosen, hlookup, hhandle, hinclude, hinactive⟩ :=
    checkpoint.publicChoice_ordinary_inclusion hinitial hroster howner hother
      polled included hpolled hincluded
  have hpacket := runtime.application.runPolicies_submit_wait_branch_packet owner players
    environment
    (beforeRoster.flatMap fun actor => [Invocation.player actor, .player actor])
    (afterRoster.flatMap fun actor => [Invocation.player actor, .player actor])
    (by simp) (by
      have hnot : owner ∉ beforeRoster := by
        intro hmem
        exact (List.nodup_append.mp (hsplit ▸ hroster)).2.2 owner hmem owner (by simp) rfl
      simp [hnot])
    (by simp) (by
      have hnot := (List.nodup_cons.mp (List.nodup_append.mp (hsplit ▸ hroster)).2.1).1
      simp [hnot]) execution polled checkpoint.serialsBeforeNext
    (.choice (state.nodes.length + 1) ⟨ty, drawn⟩) hbranch
  have hdrawnChosen : drawn = chosen.1 := by
    have := Option.some.inj (hpacket.2.symm.trans hlookup)
    have hpayload := congrArg Message.payload this
    injection hpayload with _ htyped
    cases htyped
    rfl
  subst drawn
  -- The accepted publication persists through the inactive suffix.  The
  -- successor refinement identifies its public field with the recorded source
  -- head, forcing the submitted value to be `value`.
  have hhead : (ApplicationPlan.publicChoice (newName := newName)
      (unresolved := unresolved) (fresh := fresh) publicGuard nextPlan).instructions deadlineOf =
        .publicChoice
          ((PublicChoiceSite.atHead name publicName owner guard tail).code fresh state) ::
          nextPlan.instructions deadlineOf := rfl
  have hnormal : included ∈ (runtime.application.runPolicies players environment
      (polls ++ [.environment]) execution).support := by
    rw [MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨polled, hpolled, by
      simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hincluded⟩
  have hpublic := checkpoint.after_normal_publicState _ _ hhead included final hinactive
    hnormal hremaining
  have hmemory : final.native.application.base.memory =
      included.native.application.base.memory := congrArg Prod.fst hpublic
  have hpublicationField : timed.publicationField = state.nextField + 1 := by
    simp only [timed, code, site, PublicChoiceSite.code, PublicChoiceSite.atHead,
      PublicChoiceSite.runtimeSite, Graph.publicChoice, Graph.nodeTarget, BuildState.nextField]
    change (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
      fresh state).initialFields.length + (state.nodes.length + 1) =
        state.initialFields.length + state.nextNode + 1
    rw [compileCore_initialFields]
    simp [BuildState.nextNode]
    omega
  have hfinalStore : Store.getAs final.native.application.base.memory.store
      (state.nextField + 1) ty = some chosen.1 := by
    rw [hmemory]
    simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
      EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind,
      FinDist.mem_support_pure] at hinclude
    subst included
    rw [runtime.application.includePending_accept polled.native
      (owner, execution.native.pool.nextSerial owner) _ _ hlookup hhandle]
    change Store.getAs
      (polled.native.application.base.publish timed chosen.1).memory.store
        (state.nextField + 1) ty = some chosen.1
    rw [← hpublicationField]
    simp only [ApplicationImage.State.publish, ApplicationImage.Memory.publish, Store.getAs,
      Store.set_eq]
    simp [timed, code, site, PublicChoiceSite.code, PublicChoiceSite.compiledGuard,
      TypedValue.as?]
    rfl
  have hrecorded : Store.getAs final.native.application.base.memory.store
      (state.nextField + 1) ty = some value := by
    let added := ((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
      publicName owner .here fresh.2.1
    have hspec := compileCore_fieldOf_spec tail fresh.2.2 added.1 (VHasVar.here)
    obtain ⟨fieldSpec, hfield, hty, hownerField⟩ := hspec
    have hpublicField : (compileCore tail fresh.2.2 added.1).graph.fieldRefPublic
        ⟨added.1.fieldOf VHasVar.here, ty⟩ := by
      exact ⟨fieldSpec, hfield, hty, hownerField⟩
    have hrepresented := hrefines.memory.publicFields _ hpublicField
    have hagrees := sourceNext.current.agrees VHasVar.here
    rw [hagrees] at hrepresented
    have hsourceValue := congrArg (fun env => env.get VHasVar.here) hsource
    simp only [VEnv.get, VEnv.cons] at hsourceValue
    have hfieldEq : added.1.fieldOf VHasVar.here = state.nextField + 1 := by
      simp [added, BuildState.nextField, BuildState.nextNode]
      omega
    rw [hfieldEq] at hrepresented
    exact hrepresented.trans (congrArg some hsourceValue)
  have hvalue : chosen.1 = value := Option.some.inj (hfinalStore.symm.trans hrecorded)
  rw [hvalue] at hdrawn hbranch
  exact ⟨polled, hdrawn, hbranch, included, hincluded, hremaining⟩

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_ordinary_support_value'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_ordinary_support_value

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_block_support_at_source'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_block_support_at_source
