/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedSubmitWaitPairing
import Vegas.Compile.WindowedPublicChoiceReadiness
import Vegas.Compile.WindowedPublicChoiceSubmission
import Vegas.Compile.WindowedNormalSuffix

/-! # Paired ordinary polls of an unchanged public-choice owner -/

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

/-- Complete ordinary polling preserves focal information when two actual
public-choice controllers take the same supported source draw. The source
kernels and source views may otherwise differ. -/
theorem publicChoice_ordinary_agreement_of_same_draw
    (publicGuard :
      (PublicChoiceSite.atHead name publicName owner guard tail).PubliclyValidatable fresh state)
    (nextPlan : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1)
    (profile : SourceBehavioralProfile
      (.commit name owner guard (.reveal publicName owner name .here tail)))
    (leftCurrent rightCurrent : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state)
    (left right :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (leftCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      roster focal replacement blockIndex (.publicChoice (newName := newName)
        (unresolved := unresolved) publicGuard nextPlan) profile leftCurrent left)
    (rightCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      roster focal replacement blockIndex (.publicChoice (newName := newName)
        (unresolved := unresolved) publicGuard nextPlan) profile rightCurrent right)
    (agreement : WindowedApplication.PolicyAgreement
      (root.windowed deadlineOf binding choice windowOf) focal left right)
    (hinitial : root.InitialControllerReadsPublic)
    (command : List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
      (root.windowed deadlineOf binding choice windowOf).application.View →
        (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal)
    (beforeRoster afterRoster : List P)
    (hsplit : roster = beforeRoster ++ owner :: afterRoster)
    (value : L.Val ty)
    (hleftValue : value ∈ ((profile owner
      (.here guard (.reveal publicName owner name .here tail))
      ((leftCurrent.current.source.toView owner).eraseEnv)).map Subtype.val).support)
    (hrightValue : value ∈ ((profile owner
      (.here guard (.reveal publicName owner name .here tail))
      ((rightCurrent.current.source.toView owner).eraseEnv)).map Subtype.val).support)
    (polledLeft polledRight :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hleft : polledLeft ∈ (let runtime := root.windowed deadlineOf binding choice windowOf
      let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
        replacement
      let environment := runtime.blockEnvironment roster
      (runtime.application.runPolicies players environment
        (beforeRoster.flatMap fun actor => [.player actor, .player actor]) left).bind fun middle =>
          (runtime.application.playerStep owner middle
            (.submit (.choice (state.nodes.length + 1) ⟨ty, value⟩))).bind fun submitted =>
              (runtime.application.playerStep owner submitted .wait).bind fun waited =>
                runtime.application.runPolicies players environment
                  (afterRoster.flatMap fun actor => [.player actor, .player actor]) waited).support)
    (hright : polledRight ∈ (let runtime := root.windowed deadlineOf binding choice windowOf
      let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
        replacement
      let environment := runtime.blockEnvironment roster
      (runtime.application.runPolicies players environment
        (beforeRoster.flatMap fun actor => [.player actor, .player actor]) right).bind fun middle =>
          (runtime.application.playerStep owner middle
            (.submit (.choice (state.nodes.length + 1) ⟨ty, value⟩))).bind fun submitted =>
              (runtime.application.playerStep owner submitted .wait).bind fun waited =>
                runtime.application.runPolicies players environment
                  (afterRoster.flatMap fun actor => [.player actor, .player actor])
                    waited).support) :
    WindowedApplication.PolicyAgreement
        (root.windowed deadlineOf binding choice windowOf) focal polledLeft polledRight ∧
      polledLeft ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (roster.flatMap fun actor => [.player actor, .player actor]) left).support ∧
      polledRight ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (roster.flatMap fun actor => [.player actor, .player actor]) right).support := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf
    focal replacement
  let environment := runtime.blockEnvironment roster
  let base := fun actor => runtime.liftPlayerPolicy
    (root.liftProfile deadlineOf rootProfile actor)
  let before := beforeRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  let site := PublicChoiceSite.atHead name publicName owner guard tail
  let code := site.code fresh state
  let instruction : ApplicationInstruction P L := .publicChoice { code with timeout := choice code }
  have hsplitNodup := List.nodup_append.mp (hsplit ▸ hroster)
  have hbeforeOwnerSet : owner ∉ beforeRoster := by
    intro hmem
    exact hsplitNodup.2.2 owner hmem owner (by simp) rfl
  have hbeforeOwner : Invocation.player owner ∉ before := by
    simp [before, hbeforeOwnerSet]
  have hfocal : players focal = fun history view => FinDist.pure (command history view) := by
    simp [players, windowedPlayers, hpure]
  have hothers : ∀ actor, actor ≠ focal →
      players actor = runtime.blockPlayer actor (base actor) := by
    intro actor hactor
    simp only [players, base, windowedPlayers, Function.update_of_ne hactor,
      windowedReferencePlayers]
    rfl
  have hhead : (ApplicationPlan.publicChoice (newName := newName) (unresolved := unresolved)
      (fresh := fresh) publicGuard nextPlan).instructions deadlineOf =
        .publicChoice code :: nextPlan.instructions deadlineOf := rfl
  have hindexOriginal := leftCheckpoint.instruction_at (.publicChoice code) _ hhead
  have hindex : runtime.image.instructions[blockIndex]? = some instruction := by
    simp only [runtime, instruction, windowed, ApplicationPlan.image,
      ApplicationImage.withChoiceTimeouts, ApplicationImage.withBindingTimeouts,
      List.getElem?_map, hindexOriginal, Option.map_some,
      ApplicationInstruction.withBindingTimeouts, ApplicationInstruction.withChoiceTimeouts]
  have hlengths : ∀ actor, (left.principalHistory actor).length =
      (right.principalHistory actor).length := by
    intro actor
    have hl := runtime.application.runPolicies_principalHistory_length actor players environment
      (List.replicate blockIndex (WindowedApplication.blockInvocations roster)).flatten
      (root.windowedInitialExecution deadlineOf binding choice windowOf) left leftCheckpoint.reached
    have hr := runtime.application.runPolicies_principalHistory_length actor players environment
      (List.replicate blockIndex (WindowedApplication.blockInvocations roster)).flatten
      (root.windowedInitialExecution deadlineOf binding choice windowOf) right
      rightCheckpoint.reached
    exact hl.trans hr.symm
  apply agreement.ordinary_submit_wait_of_same_input owner hother
    (fun value : L.Val ty => .choice (state.nodes.length + 1) ⟨ty, value⟩)
    command base players hfocal hothers instruction (by rfl) roster hroster
    beforeRoster afterRoster hsplit environment blockIndex hlengths (by
      intro actor hactor
      exact (leftCheckpoint.historyAlignment hroster actor hactor).1) hindex
    ((profile owner (.here guard (.reveal publicName owner name .here tail))
      ((leftCurrent.current.source.toView owner).eraseEnv)).map Subtype.val)
    ((profile owner (.here guard (.reveal publicName owner name .here tail))
      ((rightCurrent.current.source.toView owner).eraseEnv)).map Subtype.val)
    (by
      intro middle hmiddle
      have hinput := runtime.application.runPolicies_other_input owner
        (fun state actor command _ => by cases command; rfl)
        players environment before (by simp [before]) hbeforeOwner left middle hmiddle
      have hrefines := runtime.runPolicies_players_refines players environment before
        (by simp [before]) left middle leftCheckpoint.refines hmiddle
      change runtime.application.runPolicies players environment
        [.player owner, .player owner] middle = _
      simpa only [FinDist.bind_map, ApplicationImage.choiceEncoding] using
        leftCheckpoint.publicChoice_polls_source_law_of_input_eq hinitial hroster howner hother
          environment middle hrefines hinput)
    (by
      intro middle hmiddle
      have hinput := runtime.application.runPolicies_other_input owner
        (fun state actor command _ => by cases command; rfl)
        players environment before (by simp [before]) hbeforeOwner right middle hmiddle
      have hrefines := runtime.runPolicies_players_refines players environment before
        (by simp [before]) right middle rightCheckpoint.refines hmiddle
      change runtime.application.runPolicies players environment
        [.player owner, .player owner] middle = _
      simpa only [FinDist.bind_map, ApplicationImage.choiceEncoding] using
        rightCheckpoint.publicChoice_polls_source_law_of_input_eq hinitial hroster howner hother
          environment middle hrefines hinput)
    value hleftValue hrightValue polledLeft polledRight hleft hright

/-- Complete generated public-choice blocks taking the same supported source
value preserve focal information. Actual source laws, normal admission, and
the inactive clock/relay suffix supply both complete-block support witnesses;
no successful-inclusion or final-inactivity premise is assumed. -/
theorem publicChoice_block_agreement_of_same_draw
    (publicGuard :
      (PublicChoiceSite.atHead name publicName owner guard tail).PubliclyValidatable fresh state)
    (nextPlan : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1)
    (profile : SourceBehavioralProfile
      (.commit name owner guard (.reveal publicName owner name .here tail)))
    (leftCurrent rightCurrent : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state)
    (left right :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (leftCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      roster focal replacement blockIndex (.publicChoice (newName := newName)
        (unresolved := unresolved) publicGuard nextPlan) profile leftCurrent left)
    (rightCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      roster focal replacement blockIndex (.publicChoice (newName := newName)
        (unresolved := unresolved) publicGuard nextPlan) profile rightCurrent right)
    (agreement : WindowedApplication.PolicyAgreement
      (root.windowed deadlineOf binding choice windowOf) focal left right)
    (hinitial : root.InitialControllerReadsPublic)
    (command : List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
      (root.windowed deadlineOf binding choice windowOf).application.View →
        (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal)
    (beforeRoster afterRoster : List P)
    (hsplit : roster = beforeRoster ++ owner :: afterRoster)
    (value : L.Val ty)
    (hleftValue : value ∈ ((profile owner
      (.here guard (.reveal publicName owner name .here tail))
      ((leftCurrent.current.source.toView owner).eraseEnv)).map Subtype.val).support)
    (hrightValue : value ∈ ((profile owner
      (.here guard (.reveal publicName owner name .here tail))
      ((rightCurrent.current.source.toView owner).eraseEnv)).map Subtype.val).support)
    (polledLeft polledRight :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hleft : polledLeft ∈ (let runtime := root.windowed deadlineOf binding choice windowOf
      let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
        replacement
      let environment := runtime.blockEnvironment roster
      (runtime.application.runPolicies players environment
        (beforeRoster.flatMap fun actor => [.player actor, .player actor]) left).bind fun middle =>
          (runtime.application.playerStep owner middle
            (.submit (.choice (state.nodes.length + 1) ⟨ty, value⟩))).bind fun submitted =>
              (runtime.application.playerStep owner submitted .wait).bind fun waited =>
                runtime.application.runPolicies players environment
                  (afterRoster.flatMap fun actor => [.player actor, .player actor]) waited).support)
    (hright : polledRight ∈ (let runtime := root.windowed deadlineOf binding choice windowOf
      let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
        replacement
      let environment := runtime.blockEnvironment roster
      (runtime.application.runPolicies players environment
        (beforeRoster.flatMap fun actor => [.player actor, .player actor]) right).bind fun middle =>
          (runtime.application.playerStep owner middle
            (.submit (.choice (state.nodes.length + 1) ⟨ty, value⟩))).bind fun submitted =>
              (runtime.application.playerStep owner submitted .wait).bind fun waited =>
                runtime.application.runPolicies players environment
                  (afterRoster.flatMap fun actor => [.player actor, .player actor])
                    waited).support)
    (finalLeft finalRight :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hfinalLeft : finalLeft ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (.environment :: .environment :: roster.flatMap
          (fun actor => [Invocation.player actor, .environment])) polledLeft).support)
    (hfinalRight : finalRight ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (.environment :: .environment :: roster.flatMap
          (fun actor => [Invocation.player actor, .environment])) polledRight).support) :
    WindowedApplication.PolicyAgreement
        (root.windowed deadlineOf binding choice windowOf) focal finalLeft finalRight ∧
      finalLeft ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) left).support ∧
      finalRight ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) right).support := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let polls := roster.flatMap fun actor => [Invocation.player actor, .player actor]
  let suffix := Invocation.environment ::
    roster.flatMap fun actor => [Invocation.player actor, .environment]
  let code := (PublicChoiceSite.atHead name publicName owner guard tail).code fresh state
  have hhead : (ApplicationPlan.publicChoice (newName := newName) (unresolved := unresolved)
      (fresh := fresh) publicGuard nextPlan).instructions deadlineOf =
        .publicChoice code :: nextPlan.instructions deadlineOf := rfl
  obtain ⟨polledAgreement, hpolledLeft, hpolledRight⟩ :=
    publicChoice_ordinary_agreement_of_same_draw publicGuard nextPlan profile
      leftCurrent rightCurrent left right leftCheckpoint rightCheckpoint agreement hinitial
      command hpure hroster howner hother beforeRoster afterRoster hsplit value
      hleftValue hrightValue polledLeft polledRight hleft hright
  change finalLeft ∈ (runtime.application.runPolicies players (runtime.blockEnvironment roster)
    (.environment :: suffix) polledLeft).support at hfinalLeft
  change finalRight ∈ (runtime.application.runPolicies players (runtime.blockEnvironment roster)
    (.environment :: suffix) polledRight).support at hfinalRight
  simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion]
    at hfinalLeft hfinalRight
  obtain ⟨includedLeft, hincludedLeft, hfinalLeft⟩ := hfinalLeft
  obtain ⟨includedRight, hincludedRight, hfinalRight⟩ := hfinalRight
  obtain ⟨hleftInclude, hinactive⟩ := leftCheckpoint.publicChoice_ordinary_inclusion hinitial
    hroster howner hother polledLeft includedLeft hpolledLeft hincludedLeft
  obtain ⟨hrightInclude, _⟩ := rightCheckpoint.publicChoice_ordinary_inclusion hinitial
    hroster howner hother polledRight includedRight hpolledRight hincludedRight
  have hserial : left.native.pool.nextSerial owner = right.native.pool.nextSerial owner :=
    congrArg (fun pool => pool.nextSerial owner) agreement.pool
  rw [← hserial] at hrightInclude
  obtain ⟨chosen, _, _, hlookup⟩ := leftCheckpoint.publicChoice_ordinary_submission hinitial
    hroster howner hother polledLeft hpolledLeft
  have includedAgreement : WindowedApplication.PolicyAgreement runtime focal
      includedLeft includedRight := by
    apply polledAgreement.environmentPolicyStep_include (owner, left.native.pool.nextSerial owner)
      _ includedLeft includedRight hleftInclude hrightInclude
    intro message hmessage hopen
    rw [hlookup] at hmessage
    cases hmessage
    exact False.elim hopen
  have hnormalLeft : includedLeft ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) (polls ++ [.environment]) left).support := by
    rw [MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    refine ⟨polledLeft, hpolledLeft, ?_⟩
    simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hincludedLeft
  have hnormalRight : includedRight ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) (polls ++ [.environment]) right).support := by
    rw [MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    refine ⟨polledRight, hpolledRight, ?_⟩
    simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hincludedRight
  have hdecompose : WindowedApplication.blockInvocations roster =
      (polls ++ [.environment]) ++ suffix := by
    simp only [WindowedApplication.blockInvocations, polls, suffix,
      List.append_assoc, List.cons_append, List.nil_append]
  refine ⟨?_, ?_, ?_⟩
  · exact leftCheckpoint.after_normal_agreement rightCheckpoint (.publicChoice code)
      (nextPlan.instructions deadlineOf) hhead command hpure hroster
      includedLeft includedRight finalLeft finalRight includedAgreement hinactive
      hnormalLeft hnormalRight hfinalLeft hfinalRight
  · rw [hdecompose, MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨includedLeft, hnormalLeft, hfinalLeft⟩
  · rw [hdecompose, MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨includedRight, hnormalRight, hfinalRight⟩


end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_ordinary_agreement_of_same_draw'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_ordinary_agreement_of_same_draw

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_block_agreement_of_same_draw'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_block_agreement_of_same_draw
