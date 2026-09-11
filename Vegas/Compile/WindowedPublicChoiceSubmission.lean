/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedPublicChoiceReadiness
import Vegas.Compile.WindowedOwnerFrame
import Vegas.Compile.WindowedNormalService
import Vegas.Compile.WindowedPublicChoiceAdmission
import Interaction.MessageApplicationSampleOnce

/-! # Source-legal public submissions under actual ordinary service -/

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

/-- The generated reference owner leaves exactly one fresh public submission.
The retained draw belongs to the actual source kernel; arbitrary other-player
polls preserve its serial and pending packet. -/
theorem publicChoice_ordinary_submission
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.publicChoice (newName := newName) (unresolved := unresolved)
        publicGuard nextPlan) profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (hroster : roster.Nodup) (howner : owner ∈ roster)
    (reference : checkpoint.ReferenceOwner owner)
    (polled : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hpolled : polled ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (roster.flatMap fun actor => [Invocation.player actor, .player actor]) execution).support) :
    ∃ chosen ∈ (profile owner (.here guard (.reveal publicName owner name .here tail))
        ((current.current.source.toView owner).eraseEnv)).support,
      polled.native.pool.nextSerial owner = execution.native.pool.nextSerial owner + 1 ∧
      polled.native.pool.lookup (owner, execution.native.pool.nextSerial owner) =
        some ⟨(owner, execution.native.pool.nextSerial owner),
          .choice (state.nodes.length + 1) ⟨ty, chosen.1⟩⟩ := by
  obtain ⟨beforeRoster, afterRoster, rfl⟩ := List.mem_iff_append.mp howner
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let environment := runtime.blockEnvironment (beforeRoster ++ owner :: afterRoster)
  let before := beforeRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  let after := afterRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  have hbeforeOwner : owner ∉ beforeRoster := by
    intro hmem
    exact (List.nodup_append.mp hroster).2.2 owner hmem owner (by simp) rfl
  have hafterOwner : owner ∉ afterRoster :=
    (List.nodup_cons.mp (List.nodup_append.mp hroster).2.1).1
  have hbefore : Invocation.player owner ∉ before := by simp [before, hbeforeOwner]
  have hafter : Invocation.player owner ∉ after := by simp [after, hafterOwner]
  have hdecompose :
      (beforeRoster ++ owner :: afterRoster).flatMap
        (fun actor => [Invocation.player actor, Invocation.player actor]) =
      (before ++ [.player owner, .player owner]) ++ after := by
    simp only [before, after, List.flatMap_append, List.flatMap_cons, List.append_assoc]
  rw [hdecompose] at hpolled
  exact runtime.application.runPolicies_submit_wait_packet owner players environment before after
    (by simp [before]) hbefore (by simp [after]) hafter execution polled
    checkpoint.serialsBeforeNext
    (profile owner (.here guard (.reveal publicName owner name .here tail))
      ((current.current.source.toView owner).eraseEnv))
    (fun chosen => .choice (state.nodes.length + 1) ⟨ty, chosen.1⟩)
    (checkpoint.publicChoice_polls_source_law_after_others hinitial hroster
      (by simp) reference environment before (by simp [before]) hbefore) hpolled

/-- Normal service includes the reference owner's source-supported public
choice and finishes this publication instruction. The selected identifier and
native acceptance are consequences of actual polling, not service premises. -/
theorem publicChoice_ordinary_inclusion
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.publicChoice (newName := newName) (unresolved := unresolved)
        publicGuard nextPlan) profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (hroster : roster.Nodup) (howner : owner ∈ roster)
    (reference : checkpoint.ReferenceOwner owner)
    (polled included :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hpolled : polled ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (roster.flatMap fun actor => [Invocation.player actor, .player actor]) execution).support)
    (hincluded : included ∈
      ((root.windowed deadlineOf binding choice windowOf).application.invoke
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        polled .environment).support) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let site := PublicChoiceSite.atHead name publicName owner guard tail
    let code := site.code fresh state
    let timed : PublicChoiceCode P L := { code with timeout := choice code }
    ∃ chosen ∈ (profile owner (.here guard (.reveal publicName owner name .here tail))
        ((current.current.source.toView owner).eraseEnv)).support,
      polled.native.pool.lookup (owner, execution.native.pool.nextSerial owner) =
          some ⟨(owner, execution.native.pool.nextSerial owner),
            .choice timed.endpoint.publicationNode ⟨ty, chosen.1⟩⟩ ∧
        runtime.handle polled.native.application
            ⟨(owner, execution.native.pool.nextSerial owner),
              .choice timed.endpoint.publicationNode ⟨ty, chosen.1⟩⟩ =
          some (runtime.advanceTo polled.native.application
            (polled.native.application.base.publish timed chosen.1)) ∧
        included ∈ (runtime.application.environmentPolicyStep polled
            (.include (owner, execution.native.pool.nextSerial owner))).support ∧
          runtime.image.activeAddress? included.native.application.base.memory ≠
            some timed.endpoint.publicationNode := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let polls := roster.flatMap fun actor => [Invocation.player actor, .player actor]
  let site := PublicChoiceSite.atHead name publicName owner guard tail
  let code := site.code fresh state
  let timed : PublicChoiceCode P L := { code with timeout := choice code }
  have hhead : (ApplicationPlan.publicChoice (newName := newName) (unresolved := unresolved)
      (fresh := fresh) publicGuard nextPlan).instructions deadlineOf =
        .publicChoice code :: nextPlan.instructions deadlineOf := rfl
  obtain ⟨chosen, hchosen, hserial, hlookup⟩ := checkpoint.publicChoice_ordinary_submission hinitial
    hroster howner reference polled hpolled
  have hpublic := runtime.runPolicies_players_publicState players (runtime.blockEnvironment roster)
    polls (by simp [polls]) execution polled hpolled
  have hmemory : polled.native.application.base.memory =
      execution.native.application.base.memory := congrArg Prod.fst hpublic
  have hactivationEq : polled.native.application.active =
      execution.native.application.active := congrArg Prod.snd hpublic
  have hactive : runtime.image.activeAddress? polled.native.application.base.memory =
      some timed.endpoint.publicationNode := by
    rw [hmemory]
    exact checkpoint.activeAddress?_head (.publicChoice code) _ hhead
  have hindexOriginal := checkpoint.instruction_at (.publicChoice code) _ hhead
  have hlookupOriginal := root.image_lookup_of_mem deadlineOf (.publicChoice code)
    (List.mem_of_getElem? hindexOriginal)
  have hcode : runtime.image.lookup timed.endpoint.publicationNode =
      some (.publicChoice timed) := by
    change (root.image deadlineOf).lookup code.endpoint.publicationNode =
      some (.publicChoice code) at hlookupOriginal
    simp only [runtime, windowed, ApplicationImage.lookup_withChoiceTimeouts,
      ApplicationImage.lookup_withBindingTimeouts, timed, hlookupOriginal, Option.map_some,
      ApplicationInstruction.withBindingTimeouts, ApplicationInstruction.withChoiceTimeouts]
  have hcommand := checkpoint.blockEnvironment_after_ordinary_polls
    (.publicChoice code) _ hhead rfl hpolled hserial _ hlookup
  change runtime.blockEnvironment roster polled.environmentHistory
      (State.environmentView runtime.application polled.native) =
        FinDist.pure (.include (owner, execution.native.pool.nextSerial owner)) at hcommand
  change included ∈ (runtime.application.invoke players (runtime.blockEnvironment roster)
    polled .environment).support at hincluded
  simp only [MessageApplication.invoke, hcommand, FinDist.pure_bind] at hincluded
  have hincludedStep := hincluded
  obtain ⟨activation, hactivation, hkey, _⟩ :=
    checkpoint.active_origin_clock (.publicChoice code) _ hhead
  have hrefines := runtime.runPolicies_players_refines players (runtime.blockEnvironment roster)
    polls (by simp [polls]) execution polled checkpoint.refines hpolled
  have hadmission := runtime.handle_source_publicChoice_and_include_inactive guard tail fresh
    state current publicGuard polled.native.application activation
    (execution.native.pool.nextSerial owner) chosen.1 (choice code) hrefines chosen.2
    (hactivationEq.trans hactivation) (by rw [hkey]; exact hactive)
    (by rw [hkey]; exact hcode) polled.native.pool polled.native.receipts
    (by rw [hkey]; exact hlookup)
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind,
    FinDist.mem_support_pure] at hincluded
  subst included
  rw [hkey] at hadmission
  have hinactive := hadmission.2
  refine ⟨chosen, hchosen, hlookup, hadmission.1, hincludedStep, hinactive⟩

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_ordinary_submission'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_ordinary_submission

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_ordinary_inclusion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_ordinary_inclusion
