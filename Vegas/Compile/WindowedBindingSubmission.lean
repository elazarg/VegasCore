/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBindingReadiness
import Vegas.Compile.WindowedOwnerFrame
import Vegas.Compile.WindowedNormalService
import Vegas.Compile.WindowedBindingAdmission

/-! # Canonical binding packets after actual ordinary polling

The generated unchanged owner registers a source draw and submits its opaque
handle. Earlier and later raw polls by other players retain the owner's serial
and the submitted lookup, even though they may add unrelated pool traffic.
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

/-- Every supported ordinary polling segment leaves the reference owner's
generated binding packet pending at its fresh serial. Other players may issue
arbitrary randomized raw commands before and after these two owner polls. -/
theorem binding_ordinary_submission
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      focal replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
      profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (hroster : roster.Nodup) (howner : owner ∈ roster)
    (reference : checkpoint.ReferenceOwner owner)
    (polled : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hpolled : polled ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (roster.flatMap fun actor => [Invocation.player actor, .player actor]) execution).support) :
    polled.native.pool.nextSerial owner = execution.native.pool.nextSerial owner + 1 ∧
      polled.native.pool.lookup (owner, execution.native.pool.nextSerial owner) =
        some ⟨(owner, execution.native.pool.nextSerial owner),
          .binding state.nodes.length (owner, state.nextField)⟩ := by
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
  rw [hdecompose, MessageApplication.runPolicies_append] at hpolled
  simp only [FinDist.support_bind, Set.mem_iUnion] at hpolled
  obtain ⟨submitted, hsubmitted, hafterRun⟩ := hpolled
  rw [checkpoint.binding_polls_source_law_after_others hinitial hroster
    (by simp) reference environment before (by simp [before]) hbefore] at hsubmitted
  simp only [FinDist.support_bind, Set.mem_iUnion] at hsubmitted
  obtain ⟨middle, hmiddle, chosen, _, registered, hregistered, hsubmitted⟩ := hsubmitted
  have hbeforeFrame := runtime.runPolicies_other_frame owner players environment before
    (by simp [before]) hbefore execution middle hmiddle
  have hserials := runtime.application.runPolicies_serialsBeforeNext players environment before
    execution middle checkpoint.serialsBeforeNext hmiddle
  have hafterFrame := runtime.runPolicies_other_frame owner players environment after
    (by simp [after]) hafter submitted polled hafterRun
  have hsubmittedPool : submitted.native.pool =
      (middle.native.pool.submit owner
        (.binding state.nodes.length (owner, state.nextField))).2 := by
    simp only [MessageApplication.playerStep, PlayerCommand.toAction,
      MessageApplication.advance, MessageApplication.step, FinDist.pure_bind,
      FinDist.mem_support_pure] at hregistered hsubmitted
    subst registered
    subst submitted
    rfl
  refine ⟨?_, ?_⟩
  · rw [hafterFrame.2.2.1, hsubmittedPool]
    simp only [MessagePool.submit, if_pos, hbeforeFrame.2.2.1]
  · apply hafterFrame.2.2.2
    rw [hsubmittedPool, ← hbeforeFrame.2.2.1]
    exact hserials.lookup_submit owner _

/-- The ordinary service slot includes and accepts the reference owner's
actual generated packet. Readiness, freshness, and the selected identifier
are derived from the source checkpoint and supported preceding polls. No
timeout selector, successful-opening assumption, or unchanged relay is needed. -/
theorem binding_ordinary_inclusion
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      focal replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
      profile current execution)
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
    included ∈ ((root.windowed deadlineOf binding choice windowOf).application.environmentPolicyStep
      polled (.include (owner, execution.native.pool.nextSerial owner))).support ∧
      (root.windowed deadlineOf binding choice windowOf).image.activeAddress?
        included.native.application.base.memory ≠ some state.nodes.length ∧
      let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
        .here guard tail
      let code := site.bindingCode fresh state (site.compiledField fresh state)
      included.native.application.base = polled.native.application.base.bind
        { code with timeout := binding code } (owner, site.compiledField fresh state) := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let polls := roster.flatMap fun actor => [Invocation.player actor, .player actor]
  let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
    .here guard tail
  let code := site.bindingCode fresh state (site.compiledField fresh state)
  let timed : BindingCode P L := { code with timeout := binding code }
  have hhead : (ApplicationPlan.binding (newName := newName) (fresh := fresh)
      unrestricted nextPlan).instructions deadlineOf =
        .bind code :: nextPlan.instructions deadlineOf := rfl
  obtain ⟨hserial, hlookup⟩ := checkpoint.binding_ordinary_submission hinitial hroster
    howner reference polled hpolled
  have hpublic := runtime.runPolicies_players_publicState players (runtime.blockEnvironment roster)
    polls (by simp [polls]) execution polled hpolled
  have hmemory : polled.native.application.base.memory =
      execution.native.application.base.memory := congrArg Prod.fst hpublic
  have hactivationEq : polled.native.application.active =
      execution.native.application.active := congrArg Prod.snd hpublic
  have hactive : runtime.image.activeAddress? polled.native.application.base.memory =
      some timed.node := by
    rw [hmemory]
    exact checkpoint.activeAddress?_head (.bind code) _ hhead
  have hindexOriginal := checkpoint.instruction_at (.bind code) _ hhead
  have hlookupOriginal := root.image_lookup_of_mem deadlineOf (.bind code)
    (List.mem_of_getElem? hindexOriginal)
  have hcode : runtime.image.lookup timed.node = some (.bind timed) := by
    change (root.image deadlineOf).lookup code.node = some (.bind code) at hlookupOriginal
    simp only [runtime, windowed, ApplicationImage.lookup_withChoiceTimeouts,
      ApplicationImage.lookup_withBindingTimeouts, timed, hlookupOriginal, Option.map_some,
      ApplicationInstruction.withBindingTimeouts, ApplicationInstruction.withChoiceTimeouts]
  have hcommand := checkpoint.blockEnvironment_after_ordinary_polls
    (.bind code) _ hhead rfl hpolled hserial _ hlookup
  change runtime.blockEnvironment roster polled.environmentHistory
      (State.environmentView runtime.application polled.native) =
        FinDist.pure (.include (owner, execution.native.pool.nextSerial owner)) at hcommand
  change included ∈ (runtime.application.invoke players (runtime.blockEnvironment roster)
    polled .environment).support at hincluded
  simp only [MessageApplication.invoke, hcommand, FinDist.pure_bind] at hincluded
  refine ⟨hincluded, ?_⟩
  obtain ⟨activation, hactivation, hkey, _⟩ := checkpoint.active_origin_clock (.bind code) _ hhead
  have hready := SourceDecisionSite.binding_ready_at_source_prefix guard tail fresh state
    current execution.native.application.base.memory.done checkpoint.refines.memory.completed
  have haccepted : polled.native.application.base.memory.accepted timed.sourceField = none := by
    rw [hmemory]
    exact checkpoint.refines.accepted_eq_none_of_not_done
      (site.compiledNode fresh state) hready.1.1
  have hadmission := runtime.handle_canonical_binding_and_include_inactive
    polled.native.application activation timed (execution.native.pool.nextSerial owner)
    (hactivationEq.trans hactivation) hactive hkey hcode haccepted
    (by rw [hmemory]; exact hready.2.1) (by rw [hmemory]; exact hready.2.2)
    polled.native.pool polled.native.receipts hlookup
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind,
    FinDist.mem_support_pure] at hincluded
  subst included
  refine ⟨hadmission.2, ?_⟩
  rw [runtime.application.includePending_accept polled.native
    (owner, execution.native.pool.nextSerial owner) _ _ hlookup hadmission.1]
  rfl

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.binding_ordinary_submission'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.binding_ordinary_submission

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.binding_ordinary_inclusion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.binding_ordinary_inclusion
