/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBindingPairing
import Vegas.Compile.WindowedBindingReadiness
import Vegas.Compile.WindowedBindingSubmission
import Vegas.Compile.WindowedNormalSuffix

/-! # Paired ordinary polls of an unchanged binding owner -/

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
variable {blockIndex : Nat} {name : VarId} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
variable {tail : VegasCore P L ((name, .sealed owner ty) :: Γ)}
variable {newName : name ∉ pending}
variable {accounted : CommitmentAccounting (insert name pending) tail}
variable {fresh : FreshBindings (.commit name owner guard tail)} {state : BuildState P L Γ}

/-- Complete ordinary polling preserves focal information at a binding owned
by an unchanged nonfocal player. The owner's private source draws may differ. -/
private theorem binding_ordinary_agreement
    (unrestricted : UnrestrictedBinding guard)
    (nextPlan : ApplicationPlan accounted fresh.2
      (state.addCommitEvent name owner guard fresh.1).1)
    (profile : SourceBehavioralProfile (.commit name owner guard tail))
    (leftCurrent rightCurrent :
      CoupledAt (compileCore (.commit name owner guard tail) fresh state).graph state)
    (left right :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (leftCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      roster focal replacement blockIndex
      (.binding (newName := newName) unrestricted nextPlan) profile leftCurrent left)
    (rightCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      roster focal replacement blockIndex
      (.binding (newName := newName) unrestricted nextPlan) profile rightCurrent right)
    (agreement : WindowedApplication.PolicyAgreement
      (root.windowed deadlineOf binding choice windowOf) focal left right)
    (hinitial : root.InitialControllerReadsPublic)
    (command : List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
      (root.windowed deadlineOf binding choice windowOf).application.View →
        (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal)
    (leftFinal rightFinal :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hleft : leftFinal ∈ ((root.windowed deadlineOf binding choice windowOf).application
      |>.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (roster.flatMap fun actor => [Invocation.player actor, .player actor]) left).support)
    (hright : rightFinal ∈ ((root.windowed deadlineOf binding choice windowOf).application
      |>.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (roster.flatMap fun actor => [Invocation.player actor, .player actor]) right).support) :
    WindowedApplication.PolicyAgreement
      (root.windowed deadlineOf binding choice windowOf) focal leftFinal rightFinal := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf
    focal replacement
  let base := fun actor => runtime.liftPlayerPolicy
    (root.liftProfile deadlineOf rootProfile actor)
  let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
    .here guard tail
  let code := site.bindingCode fresh state (site.compiledField fresh state)
  let instruction : ApplicationInstruction P L := .bind { code with timeout := binding code }
  obtain ⟨beforeRoster, afterRoster, hsplit⟩ := List.mem_iff_append.mp howner
  have hsplitNodup := List.nodup_append.mp (hsplit ▸ hroster)
  have hbeforeNodup := hsplitNodup.1
  have hafterNodup := (List.nodup_cons.mp hsplitNodup.2.1).2
  have hbeforeOwnerSet : owner ∉ beforeRoster := by
    intro hmem
    exact hsplitNodup.2.2 owner hmem owner (by simp) rfl
  have hafterOwnerSet : owner ∉ afterRoster := (List.nodup_cons.mp hsplitNodup.2.1).1
  let before := beforeRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  let after := afterRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  have hschedule : roster.flatMap (fun actor => [Invocation.player actor, .player actor]) =
      (before ++ [.player owner, .player owner]) ++ after := by
    simp [hsplit, before, after, List.append_assoc]
  rw [hschedule, MessageApplication.runPolicies_append] at hleft hright
  simp only [FinDist.support_bind, Set.mem_iUnion] at hleft hright
  obtain ⟨leftSubmitted, hleftPrefix, hleftAfter⟩ := hleft
  obtain ⟨rightSubmitted, hrightPrefix, hrightAfter⟩ := hright
  have hfocal : players focal = fun history view => FinDist.pure (command history view) := by
    simp [players, windowedPlayers, hpure]
  have hothers : ∀ actor, actor ≠ focal →
      players actor = runtime.blockPlayer actor (base actor) := by
    intro actor hactor
    simp only [players, base, windowedPlayers, Function.update_of_ne hactor,
      windowedReferencePlayers]
    rfl
  have hhead : (ApplicationPlan.binding (newName := newName) (fresh := fresh)
      unrestricted nextPlan).instructions deadlineOf =
        .bind code :: nextPlan.instructions deadlineOf := by rfl
  have hindexOriginal := leftCheckpoint.instruction_at (.bind code) _ hhead
  have hindex : runtime.image.instructions[blockIndex]? = some instruction := by
    simp only [runtime, instruction, windowed, ApplicationPlan.image,
      ApplicationImage.withChoiceTimeouts, ApplicationImage.withBindingTimeouts,
      List.getElem?_map, hindexOriginal, Option.map_some,
      ApplicationInstruction.withBindingTimeouts, ApplicationInstruction.withChoiceTimeouts]
  have hlengths : ∀ actor, (left.principalHistory actor).length =
      (right.principalHistory actor).length := by
    intro actor
    have hl := runtime.application.runPolicies_principalHistory_length actor players
      (runtime.blockEnvironment roster)
      (List.replicate blockIndex (WindowedApplication.blockInvocations roster)).flatten
      (root.windowedInitialExecution deadlineOf binding choice windowOf) left leftCheckpoint.reached
    have hr := runtime.application.runPolicies_principalHistory_length actor players
      (runtime.blockEnvironment roster)
      (List.replicate blockIndex (WindowedApplication.blockInvocations roster)).flatten
      (root.windowedInitialExecution deadlineOf binding choice windowOf) right
      rightCheckpoint.reached
    exact hl.trans hr.symm
  have hbeforePlayers : ∀ invocation ∈ before, ∃ actor, invocation = .player actor := by
    intro invocation hinv
    rcases List.mem_flatMap.mp hinv with ⟨actor, _, hpair⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
    rcases hpair with rfl | rfl <;> exact ⟨actor, rfl⟩
  have hbeforeOwner : Invocation.player owner ∉ before := by
    simp [before, hbeforeOwnerSet]
  have hpaired := agreement.binding_polls_after_gated_prefix owner hother code command base players
    hfocal hothers instruction before hbeforePlayers (by
      intro actor hmem _
      have hne : actor ≠ owner := by
        intro heq; subst actor; exact hbeforeOwner hmem
      change some owner ≠ some actor
      exact fun heq => hne (Option.some.inj heq).symm)
    (runtime.blockEnvironment roster) hlengths (by
      intro actor index hlo hhi
      have hcount := WindowedApplication.ordinaryPolls_player_count beforeRoster
        hbeforeNodup actor
      change before.countP (WindowedApplication.PolicyAgreement.playerCountFor actor) =
        (if actor ∈ beforeRoster then 2 else 0) at hcount
      rw [hcount] at hhi
      split at hhi
      · rename_i hactor
        have hstart := (leftCheckpoint.historyAlignment hroster actor
          (by rw [hsplit]; exact List.mem_append_left _ hactor)).1
        have : index / 3 = blockIndex := by omega
        rw [this]; exact hindex
      · omega)
    ((profile owner site ((leftCurrent.current.source.toView owner).eraseEnv)).map Subtype.val)
    ((profile owner site ((rightCurrent.current.source.toView owner).eraseEnv)).map Subtype.val)
    (by
      intro middle hmiddle
      have hinput := runtime.application.runPolicies_other_input owner
        (fun state actor command _ => by cases command; rfl)
        players (runtime.blockEnvironment roster) before (by simp [before]) hbeforeOwner
        left middle hmiddle
      simp only [FinDist.bind_map]
      exact leftCheckpoint.binding_polls_source_law_of_input_eq hinitial hroster howner
        (leftCheckpoint.referenceOwner_of_ne owner hother)
        (runtime.blockEnvironment roster) middle hinput)
    (by
      intro middle hmiddle
      have hinput := runtime.application.runPolicies_other_input owner
        (fun state actor command _ => by cases command; rfl)
        players (runtime.blockEnvironment roster) before (by simp [before]) hbeforeOwner
        right middle hmiddle
      simp only [FinDist.bind_map]
      exact rightCheckpoint.binding_polls_source_law_of_input_eq hinitial hroster howner
        (rightCheckpoint.referenceOwner_of_ne owner hother)
        (runtime.blockEnvironment roster) middle hinput)
    leftSubmitted rightSubmitted hleftPrefix hrightPrefix
  have hsubmittedLengths : ∀ actor, (leftSubmitted.principalHistory actor).length =
      (rightSubmitted.principalHistory actor).length := by
    intro actor
    have hl := runtime.application.runPolicies_principalHistory_length actor players
      (runtime.blockEnvironment roster) (before ++ [.player owner, .player owner])
      left leftSubmitted hleftPrefix
    have hr := runtime.application.runPolicies_principalHistory_length actor players
      (runtime.blockEnvironment roster) (before ++ [.player owner, .player owner])
      right rightSubmitted hrightPrefix
    rw [hl, hr, hlengths]
  apply hpaired.1.runPolicies_players_gated command base players hfocal hothers instruction after
    (by
      intro invocation hinv
      rcases List.mem_flatMap.mp hinv with ⟨actor, _, hpair⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
      rcases hpair with rfl | rfl <;> exact ⟨actor, rfl⟩)
    (by
      intro actor hmem _
      have hne : actor ≠ owner := by
        intro heq; subst actor
        have : owner ∈ afterRoster := by simpa [after] using hmem
        exact hafterOwnerSet this
      change some owner ≠ some actor
      exact fun heq => hne (Option.some.inj heq).symm)
    (runtime.blockEnvironment roster) hsubmittedLengths
    (by
      intro actor index hlo hhi
      have hcount := WindowedApplication.ordinaryPolls_player_count afterRoster
        hafterNodup actor
      change after.countP (WindowedApplication.PolicyAgreement.playerCountFor actor) =
        (if actor ∈ afterRoster then 2 else 0) at hcount
      rw [hcount] at hhi
      split at hhi
      · rename_i hactor
        have hnotBefore : actor ∉ beforeRoster := by
          intro hmem
          exact hsplitNodup.2.2 actor hmem actor (List.mem_cons_of_mem _ hactor) rfl
        have hownerNe : owner ≠ actor := by
          intro heq
          exact hafterOwnerSet (heq ▸ hactor)
        have htotal : (leftSubmitted.principalHistory actor).length = 3 * blockIndex := by
          have hl := runtime.application.runPolicies_principalHistory_length actor players
            (runtime.blockEnvironment roster) (before ++ [.player owner, .player owner])
            left leftSubmitted hleftPrefix
          rw [hl]
          have hcountBefore := WindowedApplication.ordinaryPolls_player_count beforeRoster
            hbeforeNodup actor
          change before.countP (WindowedApplication.PolicyAgreement.playerCountFor actor) = _
            at hcountBefore
          simp only [List.countP_append, List.countP_cons, List.countP_nil,
            hownerNe, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
          change (left.principalHistory actor).length +
            before.countP (WindowedApplication.PolicyAgreement.playerCountFor actor) = _
          rw [hcountBefore, if_neg hnotBefore, Nat.add_zero]
          exact (leftCheckpoint.historyAlignment hroster actor
            (by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hactor))).1
        rw [htotal] at hlo hhi
        have : index / 3 = blockIndex := by omega
        rw [this]; exact hindex
      · omega)
    leftFinal rightFinal hleftAfter hrightAfter

/-- An unchanged owner's complete binding block preserves the focal player's
information. Actual controller laws provide the opaque packet, normal service
accepts it, and the remaining clock and relay slots are inactive. The two
private source draws need not coincide; the focal raw policy is unrestricted
apart from being fixed and pure. -/
theorem binding_block_agreement
    (unrestricted : UnrestrictedBinding guard)
    (nextPlan : ApplicationPlan accounted fresh.2
      (state.addCommitEvent name owner guard fresh.1).1)
    (profile : SourceBehavioralProfile (.commit name owner guard tail))
    (leftCurrent rightCurrent :
      CoupledAt (compileCore (.commit name owner guard tail) fresh state).graph state)
    (left right :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (leftCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      roster focal replacement blockIndex
      (.binding (newName := newName) unrestricted nextPlan) profile leftCurrent left)
    (rightCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      roster focal replacement blockIndex
      (.binding (newName := newName) unrestricted nextPlan) profile rightCurrent right)
    (agreement : WindowedApplication.PolicyAgreement
      (root.windowed deadlineOf binding choice windowOf) focal left right)
    (hinitial : root.InitialControllerReadsPublic)
    (command : List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
      (root.windowed deadlineOf binding choice windowOf).application.View →
        (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal)
    (leftFinal rightFinal :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hleft : leftFinal ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) left).support)
    (hright : rightFinal ∈ ((root.windowed deadlineOf binding choice windowOf).application
      |>.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) right).support) :
    WindowedApplication.PolicyAgreement
      (root.windowed deadlineOf binding choice windowOf) focal leftFinal rightFinal := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let polls := roster.flatMap fun actor => [Invocation.player actor, .player actor]
  let suffix := Invocation.environment ::
    roster.flatMap fun actor => [Invocation.player actor, .environment]
  let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
    .here guard tail
  let code := site.bindingCode fresh state (site.compiledField fresh state)
  have hdecompose : WindowedApplication.blockInvocations roster =
      polls ++ (.environment :: suffix) := by
    simp only [WindowedApplication.blockInvocations, polls, suffix, List.append_assoc,
      List.cons_append, List.nil_append]
  rw [hdecompose, MessageApplication.runPolicies_append] at hleft hright
  simp only [FinDist.support_bind, Set.mem_iUnion] at hleft hright
  obtain ⟨polledLeft, hpolledLeft, hremainingLeft⟩ := hleft
  obtain ⟨polledRight, hpolledRight, hremainingRight⟩ := hright
  simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion]
    at hremainingLeft hremainingRight
  obtain ⟨includedLeft, hincludedLeft, hfinalLeft⟩ := hremainingLeft
  obtain ⟨includedRight, hincludedRight, hfinalRight⟩ := hremainingRight
  have polledAgreement := binding_ordinary_agreement unrestricted nextPlan profile
    leftCurrent rightCurrent left right leftCheckpoint rightCheckpoint agreement hinitial command
    hpure hroster howner hother polledLeft polledRight hpolledLeft hpolledRight
  obtain ⟨hleftInclude, hinactive, _⟩ := leftCheckpoint.binding_ordinary_inclusion hinitial
    hroster howner (leftCheckpoint.referenceOwner_of_ne owner hother)
    polledLeft includedLeft hpolledLeft hincludedLeft
  obtain ⟨hrightInclude, _⟩ := rightCheckpoint.binding_ordinary_inclusion hinitial
    hroster howner (rightCheckpoint.referenceOwner_of_ne owner hother)
    polledRight includedRight hpolledRight hincludedRight
  have hserial : left.native.pool.nextSerial owner = right.native.pool.nextSerial owner :=
    congrArg (fun pool => pool.nextSerial owner) agreement.pool
  rw [← hserial] at hrightInclude
  have hlookup := (leftCheckpoint.binding_ordinary_submission hinitial
    hroster howner (leftCheckpoint.referenceOwner_of_ne owner hother)
    polledLeft hpolledLeft).2
  have includedAgreement : WindowedApplication.PolicyAgreement runtime focal
      includedLeft includedRight := by
    apply polledAgreement.environmentPolicyStep_include (owner, left.native.pool.nextSerial owner)
      _ includedLeft includedRight hleftInclude hrightInclude
    intro message hmessage hopen
    rw [hlookup] at hmessage
    cases hmessage
    exact False.elim hopen
  apply leftCheckpoint.after_normal_agreement rightCheckpoint (.bind code)
    (nextPlan.instructions deadlineOf) rfl command hpure hroster
    includedLeft includedRight leftFinal rightFinal includedAgreement hinactive _ _
    hfinalLeft hfinalRight
  · rw [MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    refine ⟨polledLeft, hpolledLeft, ?_⟩
    simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hincludedLeft
  · rw [MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    refine ⟨polledRight, hpolledRight, ?_⟩
    simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hincludedRight

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.binding_block_agreement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.binding_block_agreement
