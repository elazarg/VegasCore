/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedSubmitWaitPairing
import Vegas.Compile.WindowedConditionalInclusion
import Vegas.Compile.WindowedConditionalInversion
import Vegas.Compile.WindowedConditionalPrivacy
import Vegas.Compile.WindowedNormalSuffix

/-! # Complete comparison of unchanged conditional-disclosure blocks -/

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

/-- The two conditional accounting forms have the same ordinary-poll
comparison. Source kernels may differ, while the supported public optional
result and prior focal information agree. -/
theorem conditional_ordinary_agreement_of_same_result
    (head : ConditionalHead spec plan)
    (leftCurrent rightCurrent : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state)
    (left right :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (leftCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      roster focal replacement blockIndex plan profile leftCurrent left)
    (rightCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      roster focal replacement blockIndex plan profile rightCurrent right)
    (agreement : WindowedApplication.PolicyAgreement
      (root.windowed deadlineOf binding choice windowOf) focal left right)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (command : List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
      (root.windowed deadlineOf binding choice windowOf).application.View →
        (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal)
    (beforeRoster afterRoster : List P)
    (hsplit : roster = beforeRoster ++ owner :: afterRoster)
    (disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy))
    (hbinding : let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
      (site.code fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state))).binding?
          left.native.application.base.memory = some disposition)
    (result : Option (L.Val spec.secretTy))
    (hleftResult : result ∈ ((profile owner
      (.here guard (.reveal publicName owner name .here tail))
      ((leftCurrent.current.source.toView owner).eraseEnv)).map
        (fun chosen => spec.encoding chosen.1)).support)
    (hrightResult : result ∈ ((profile owner
      (.here guard (.reveal publicName owner name .here tail))
      ((rightCurrent.current.source.toView owner).eraseEnv)).map
        (fun chosen => spec.encoding chosen.1)).support)
    (polledLeft polledRight :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hleft : polledLeft ∈ (let runtime := root.windowed deadlineOf binding choice windowOf
      let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
        replacement
      let environment := runtime.blockEnvironment roster
      let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
      let payload := ApplicationImage.Payload.conditional (site.choice.publicationNode fresh state)
        (site.sourceRequestPayload fresh state (site.sourceField fresh state)
          (deadlineOf (site.choice.publicationNode fresh state)) disposition result)
      (runtime.application.runPolicies players environment
        (beforeRoster.flatMap fun actor => [.player actor, .player actor]) left).bind fun middle =>
          (runtime.application.playerStep owner middle (.submit payload)).bind fun submitted =>
            (runtime.application.playerStep owner submitted .wait).bind fun waited =>
              runtime.application.runPolicies players environment
                (afterRoster.flatMap fun actor => [.player actor, .player actor]) waited).support)
    (hright : polledRight ∈ (let runtime := root.windowed deadlineOf binding choice windowOf
      let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
        replacement
      let environment := runtime.blockEnvironment roster
      let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
      let payload := ApplicationImage.Payload.conditional (site.choice.publicationNode fresh state)
        (site.sourceRequestPayload fresh state (site.sourceField fresh state)
          (deadlineOf (site.choice.publicationNode fresh state)) disposition result)
      (runtime.application.runPolicies players environment
        (beforeRoster.flatMap fun actor => [.player actor, .player actor]) right).bind fun middle =>
          (runtime.application.playerStep owner middle (.submit payload)).bind fun submitted =>
            (runtime.application.playerStep owner submitted .wait).bind fun waited =>
              runtime.application.runPolicies players environment
                (afterRoster.flatMap fun actor => [.player actor, .player actor]) waited).support) :
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
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let environment := runtime.blockEnvironment roster
  let base := fun actor => runtime.liftPlayerPolicy
    (root.liftProfile deadlineOf rootProfile actor)
  let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
  let code := site.code fresh state (site.sourceField fresh state)
    (deadlineOf (site.choice.publicationNode fresh state))
  let payload := fun result => ApplicationImage.Payload.conditional
    (P := P) (L := L) (site.choice.publicationNode fresh state)
    (site.sourceRequestPayload fresh state (site.sourceField fresh state)
      (deadlineOf (site.choice.publicationNode fresh state)) disposition result)
  let encoding := site.choiceEncodingFor fresh state (site.sourceField fresh state)
    (deadlineOf (site.choice.publicationNode fresh state)) disposition
    (ApplicationImage.conditionalTransport spec.secretTy)
  let before := beforeRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  have hrightBinding : code.binding? right.native.application.base.memory =
      some disposition := by
    rw [← agreement.state.base.memory]
    exact hbinding
  have hfocal : players focal = fun history view => FinDist.pure (command history view) := by
    simp [players, windowedPlayers, hpure]
  have hothers : ∀ actor, actor ≠ focal →
      players actor = runtime.blockPlayer actor (base actor) := by
    intro actor hactor
    simp only [players, base, windowedPlayers, Function.update_of_ne hactor,
      windowedReferencePlayers]
    rfl
  obtain ⟨rest, hhead⟩ := head.instructions deadlineOf
  have hindexOriginal := leftCheckpoint.instruction_at (.conditional code) rest hhead
  have hindex : runtime.image.instructions[blockIndex]? = some (.conditional code) := by
    simp only [runtime, windowed, ApplicationPlan.image, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, List.getElem?_map, hindexOriginal, Option.map_some,
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
  have hbeforeOwner : Invocation.player owner ∉ before := by
    have hnot : owner ∉ beforeRoster := by
      intro hmem
      exact (List.nodup_append.mp (hsplit ▸ hroster)).2.2 owner hmem owner (by simp) rfl
    simp [before, hnot]
  have hencode (chosen : L.Val ty) : encoding.encode chosen = payload (spec.encoding chosen) :=
    site.choiceEncodingFor_encode fresh state (site.sourceField fresh state)
      (deadlineOf (site.choice.publicationNode fresh state)) disposition chosen
  let leftKernel : FinDist (Option (L.Val spec.secretTy)) :=
    (profile owner (.here guard (.reveal publicName owner name .here tail))
      ((leftCurrent.current.source.toView owner).eraseEnv)).map
        (fun chosen => spec.encoding chosen.1)
  let rightKernel : FinDist (Option (L.Val spec.secretTy)) :=
    (profile owner (.here guard (.reveal publicName owner name .here tail))
      ((rightCurrent.current.source.toView owner).eraseEnv)).map
        (fun chosen => spec.encoding chosen.1)
  apply agreement.ordinary_submit_wait_of_same_input (A := Option (L.Val spec.secretTy))
    owner hother payload
    command base players hfocal hothers (.conditional code) rfl roster hroster
    beforeRoster afterRoster hsplit environment blockIndex hlengths
    (fun actor hactor => (leftCheckpoint.historyAlignment hroster actor hactor).1) hindex
    leftKernel rightKernel
    (by
      intro middle hmiddle
      have hinput := runtime.application.runPolicies_other_input owner
        (fun state actor command _ => by cases command; rfl)
        players environment before (by simp [before]) hbeforeOwner left middle hmiddle
      have hrefines := runtime.runPolicies_players_refines players environment before
        (by simp [before]) left middle leftCheckpoint.refines hmiddle
      have hlaw := leftCheckpoint.conditional_polls_source_law_of_input_eq head hinitial horigins
        hroster howner hother disposition hbinding environment middle hrefines hinput
      change runtime.application.runPolicies players environment [.player owner, .player owner]
        middle = (profile owner site.choice.decision
          ((leftCurrent.current.source.toView owner).eraseEnv)).bind
            (fun chosen => (runtime.application.playerStep owner middle
              (.submit (encoding.encode chosen.1))).bind
                (fun submitted => runtime.application.playerStep owner submitted .wait)) at hlaw
      dsimp only [leftKernel]
      rw [FinDist.bind_map, hlaw]
      apply FinDist.bind_congr
      intro chosen _
      rw [hencode])
    (by
      intro middle hmiddle
      have hinput := runtime.application.runPolicies_other_input owner
        (fun state actor command _ => by cases command; rfl)
        players environment before (by simp [before]) hbeforeOwner right middle hmiddle
      have hrefines := runtime.runPolicies_players_refines players environment before
        (by simp [before]) right middle rightCheckpoint.refines hmiddle
      have hlaw := rightCheckpoint.conditional_polls_source_law_of_input_eq head hinitial horigins
        hroster howner hother disposition hrightBinding environment middle hrefines hinput
      change runtime.application.runPolicies players environment [.player owner, .player owner]
        middle = (profile owner site.choice.decision
          ((rightCurrent.current.source.toView owner).eraseEnv)).bind
            (fun chosen => (runtime.application.playerStep owner middle
              (.submit (encoding.encode chosen.1))).bind
                (fun submitted => runtime.application.playerStep owner submitted .wait)) at hlaw
      dsimp only [rightKernel]
      rw [FinDist.bind_map, hlaw]
      apply FinDist.bind_congr
      intro chosen _
      rw [hencode])
    result hleftResult hrightResult polledLeft polledRight hleft hright

/-- Both source-accounting forms of unchanged conditional disclosure preserve
focal information through a complete block when they draw the same supported
public optional result. Normal acceptance is derived separately on both sides
from source legality and actual frozen-binding provenance. The replacing
player retains its entire raw command language. -/
theorem conditional_block_agreement_of_same_result
    (head : ConditionalHead spec plan)
    (leftCurrent rightCurrent : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state)
    (left right :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (leftCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      roster focal replacement blockIndex plan profile leftCurrent left)
    (rightCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      roster focal replacement blockIndex plan profile rightCurrent right)
    (agreement : WindowedApplication.PolicyAgreement
      (root.windowed deadlineOf binding choice windowOf) focal left right)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (command : List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
      (root.windowed deadlineOf binding choice windowOf).application.View →
        (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal)
    (beforeRoster afterRoster : List P)
    (hsplit : roster = beforeRoster ++ owner :: afterRoster)
    (disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy))
    (hbinding : let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
      (site.code fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state))).binding?
          left.native.application.base.memory = some disposition)
    (result : Option (L.Val spec.secretTy))
    (hleftResult : result ∈ ((profile owner
      (.here guard (.reveal publicName owner name .here tail))
      ((leftCurrent.current.source.toView owner).eraseEnv)).map
        (fun chosen => spec.encoding chosen.1)).support)
    (hrightResult : result ∈ ((profile owner
      (.here guard (.reveal publicName owner name .here tail))
      ((rightCurrent.current.source.toView owner).eraseEnv)).map
        (fun chosen => spec.encoding chosen.1)).support)
    (polledLeft polledRight :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hleft : polledLeft ∈ (let runtime := root.windowed deadlineOf binding choice windowOf
      let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
        replacement
      let environment := runtime.blockEnvironment roster
      let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
      let payload := ApplicationImage.Payload.conditional (site.choice.publicationNode fresh state)
        (site.sourceRequestPayload fresh state (site.sourceField fresh state)
          (deadlineOf (site.choice.publicationNode fresh state)) disposition result)
      (runtime.application.runPolicies players environment
        (beforeRoster.flatMap fun actor => [.player actor, .player actor]) left).bind fun middle =>
          (runtime.application.playerStep owner middle (.submit payload)).bind fun submitted =>
            (runtime.application.playerStep owner submitted .wait).bind fun waited =>
              runtime.application.runPolicies players environment
                (afterRoster.flatMap fun actor => [.player actor, .player actor]) waited).support)
    (hright : polledRight ∈ (let runtime := root.windowed deadlineOf binding choice windowOf
      let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
        replacement
      let environment := runtime.blockEnvironment roster
      let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
      let payload := ApplicationImage.Payload.conditional (site.choice.publicationNode fresh state)
        (site.sourceRequestPayload fresh state (site.sourceField fresh state)
          (deadlineOf (site.choice.publicationNode fresh state)) disposition result)
      (runtime.application.runPolicies players environment
        (beforeRoster.flatMap fun actor => [.player actor, .player actor]) right).bind fun middle =>
          (runtime.application.playerStep owner middle (.submit payload)).bind fun submitted =>
            (runtime.application.playerStep owner submitted .wait).bind fun waited =>
              runtime.application.runPolicies players environment
                (afterRoster.flatMap fun actor => [.player actor, .player actor]) waited).support)
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
  let environment := runtime.blockEnvironment roster
  let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
  let code := site.code fresh state (site.sourceField fresh state)
    (deadlineOf (site.choice.publicationNode fresh state))
  let polls := roster.flatMap fun actor => [Invocation.player actor, .player actor]
  let suffix := Invocation.environment ::
    roster.flatMap fun actor => [Invocation.player actor, .environment]
  obtain ⟨rest, hhead⟩ := head.instructions deadlineOf
  have hrightBinding : code.binding? right.native.application.base.memory =
      some disposition := by
    rw [← agreement.state.base.memory]
    exact hbinding
  obtain ⟨polledAgreement, hpolledLeft, hpolledRight⟩ :=
    conditional_ordinary_agreement_of_same_result head leftCurrent rightCurrent left right
      leftCheckpoint rightCheckpoint agreement hinitial horigins command hpure hroster howner
      hother beforeRoster afterRoster hsplit disposition hbinding result hleftResult hrightResult
      polledLeft polledRight hleft hright
  change finalLeft ∈ (runtime.application.runPolicies players environment
    (.environment :: suffix) polledLeft).support at hfinalLeft
  change finalRight ∈ (runtime.application.runPolicies players environment
    (.environment :: suffix) polledRight).support at hfinalRight
  simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion]
    at hfinalLeft hfinalRight
  obtain ⟨includedLeft, hincludedLeft, hfinalLeft⟩ := hfinalLeft
  obtain ⟨includedRight, hincludedRight, hfinalRight⟩ := hfinalRight
  obtain ⟨leftDisposition, leftChosen, _, hleftBinding, hleftLookup, hleftHandle,
    hleftInclude, hinactive⟩ :=
      leftCheckpoint.conditional_ordinary_inclusion head hinitial horigins hroster howner hother
        polledLeft includedLeft hpolledLeft hincludedLeft
  obtain ⟨rightDisposition, rightChosen, _, hrightBinding', hrightLookup, hrightHandle,
    hrightInclude, _⟩ :=
      rightCheckpoint.conditional_ordinary_inclusion head hinitial horigins hroster howner hother
        polledRight includedRight hpolledRight hincludedRight
  have hleftDisposition : leftDisposition = disposition :=
    Option.some.inj (hleftBinding.symm.trans hbinding)
  have hrightDisposition : rightDisposition = disposition :=
    Option.some.inj (hrightBinding'.symm.trans hrightBinding)
  subst leftDisposition
  subst rightDisposition
  have hserial : left.native.pool.nextSerial owner = right.native.pool.nextSerial owner :=
    congrArg (fun pool => pool.nextSerial owner) agreement.pool
  rw [← hserial] at hrightLookup hrightHandle hrightInclude
  have hmessage := Option.some.inj (hleftLookup.symm.trans
    ((congrArg (fun pool => pool.lookup (owner, left.native.pool.nextSerial owner))
      polledAgreement.pool).trans hrightLookup))
  have hpayload := congrArg Message.payload hmessage
  injection hpayload with _ hrequest
  have hresult := site.sourceRequestPayload_injective fresh state
    (site.sourceField fresh state) (deadlineOf (site.choice.publicationNode fresh state))
    disposition hrequest
  have includedAgreement : WindowedApplication.PolicyAgreement runtime focal
      includedLeft includedRight := by
    apply polledAgreement.environmentPolicyStep_include_conditional code
      (spec.encoding leftChosen.1) (owner, left.native.pool.nextSerial owner)
      _ hleftLookup hleftHandle _ includedLeft includedRight hleftInclude hrightInclude
    rw [hmessage]
    rw [hresult]
    exact hrightHandle
  have hnormalLeft : includedLeft ∈ (runtime.application.runPolicies players environment
      (polls ++ [.environment]) left).support := by
    rw [MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    refine ⟨polledLeft, hpolledLeft, ?_⟩
    simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hincludedLeft
  have hnormalRight : includedRight ∈ (runtime.application.runPolicies players environment
      (polls ++ [.environment]) right).support := by
    rw [MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    refine ⟨polledRight, hpolledRight, ?_⟩
    simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hincludedRight
  have hdecompose : WindowedApplication.blockInvocations roster =
      (polls ++ [.environment]) ++ suffix := by
    simp only [WindowedApplication.blockInvocations, polls, suffix,
      List.append_assoc, List.cons_append, List.nil_append]
  refine ⟨?_, ?_, ?_⟩
  · exact leftCheckpoint.after_normal_agreement rightCheckpoint (.conditional code)
      rest hhead command hpure hroster includedLeft includedRight finalLeft finalRight
      includedAgreement hinactive hnormalLeft hnormalRight hfinalLeft hfinalRight
  · rw [hdecompose, MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨includedLeft, hnormalLeft, hfinalLeft⟩
  · rw [hdecompose, MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨includedRight, hnormalRight, hfinalRight⟩

/-- Actual complete executions with the same recorded public source result
preserve focal information across either conditional head. The checkpoints
and supported runs supply the binding disposition, source draw, and ordinary
submission branches; none is an additional execution premise. -/
theorem conditional_block_agreement_at_source
    (head : ConditionalHead spec plan)
    (leftCurrent rightCurrent : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state)
    (left right finalLeft finalRight :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (leftCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      roster focal replacement blockIndex plan profile leftCurrent left)
    (rightCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      roster focal replacement blockIndex plan profile rightCurrent right)
    (agreement : WindowedApplication.PolicyAgreement
      (root.windowed deadlineOf binding choice windowOf) focal left right)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (command : List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
      (root.windowed deadlineOf binding choice windowOf).application.View →
        (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal)
    (result : Option (L.Val spec.secretTy))
    (recordedLeft recordedRight : CoupledAt
      (compileCore tail fresh.2.2
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1).graph
      (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1)
    (hsourceLeft : recordedLeft.current.source =
      (leftCurrent.current.source.cons (spec.encoding.symm result)).cons
        (spec.encoding.symm result))
    (hsourceRight : recordedRight.current.source =
      (rightCurrent.current.source.cons (spec.encoding.symm result)).cons
        (spec.encoding.symm result))
    (hrefinesLeft : finalLeft.native.application.base.Refines recordedLeft.current.graph.1)
    (hrefinesRight : finalRight.native.application.base.Refines recordedRight.current.graph.1)
    (hfinalLeft : finalLeft ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) left).support)
    (hfinalRight : finalRight ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) right).support) :
    WindowedApplication.PolicyAgreement
      (root.windowed deadlineOf binding choice windowOf) focal finalLeft finalRight := by
  obtain ⟨beforeRoster, afterRoster, hsplit⟩ := List.mem_iff_append.mp howner
  obtain ⟨leftDisposition, hbindingLeft, hresultLeft, polledLeft, hbranchLeft,
      includedLeft, hincludedLeft, hsuffixLeft⟩ :=
    conditional_block_support_at_source head leftCurrent left finalLeft leftCheckpoint
      hinitial horigins hroster howner hother beforeRoster afterRoster hsplit
      result recordedLeft hsourceLeft hrefinesLeft hfinalLeft
  obtain ⟨rightDisposition, hbindingRight, hresultRight, polledRight, hbranchRight,
      includedRight, hincludedRight, hsuffixRight⟩ :=
    conditional_block_support_at_source head rightCurrent right finalRight rightCheckpoint
      hinitial horigins hroster howner hother beforeRoster afterRoster hsplit
      result recordedRight hsourceRight hrefinesRight hfinalRight
  have hdisposition : rightDisposition = leftDisposition := by
    rw [← agreement.state.base.memory] at hbindingRight
    exact Option.some.inj (hbindingRight.symm.trans hbindingLeft)
  subst rightDisposition
  apply (conditional_block_agreement_of_same_result head leftCurrent rightCurrent left right
    leftCheckpoint rightCheckpoint agreement hinitial horigins command hpure hroster howner
    hother beforeRoster afterRoster hsplit leftDisposition hbindingLeft result
    hresultLeft hresultRight polledLeft polledRight hbranchLeft hbranchRight
    finalLeft finalRight ?_ ?_).1
  · change finalLeft ∈ (((root.windowed deadlineOf binding choice windowOf).application.invoke
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      polledLeft .environment).bind _).support
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨includedLeft, hincludedLeft, hsuffixLeft⟩
  · change finalRight ∈ (((root.windowed deadlineOf binding choice windowOf).application.invoke
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      polledRight .environment).bind _).support
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨includedRight, hincludedRight, hsuffixRight⟩

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.conditional_block_agreement_of_same_result'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.conditional_block_agreement_of_same_result


/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.conditional_ordinary_agreement_of_same_result'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.conditional_ordinary_agreement_of_same_result

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.conditional_block_agreement_at_source'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.conditional_block_agreement_at_source
