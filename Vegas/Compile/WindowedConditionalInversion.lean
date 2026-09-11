/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationSampleOnce
import Vegas.Compile.SourceAdequacy
import Vegas.Compile.WindowedConditionalInclusion
import Vegas.Compile.WindowedConditionalReadiness
import Vegas.Compile.WindowedNormalSuffix

/-! # Support inversion for conditional-disclosure blocks -/

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
variable {spec : ConditionalOpening guard}
variable {accounted : CommitmentAccounting pending
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {fresh : FreshBindings
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {state : BuildState P L Γ} {plan : ApplicationPlan accounted fresh state}
variable {profile : SourceBehavioralProfile
  (.commit name owner guard (.reveal publicName owner name .here tail))}

/-- A fixed guarded source draw in the exact ordinary conditional branch is
the value published by the completed native block. -/
theorem conditional_fixed_branch_publication
    (head : ConditionalHead spec plan)
    (current : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      roster focal replacement blockIndex plan profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal)
    (beforeRoster afterRoster : List P)
    (hsplit : roster = beforeRoster ++ owner :: afterRoster)
    (disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy))
    (hbinding : let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
      (site.code fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state))).binding?
          execution.native.application.base.memory = some disposition)
    (chosen : { value // evalGuard guard value
      ((current.current.source.toView owner).eraseEnv) = true })
    (hchosen : chosen ∈ (profile owner
      (.here guard (.reveal publicName owner name .here tail))
      ((current.current.source.toView owner).eraseEnv)).support)
    (hbranch : final ∈
      (let runtime := root.windowed deadlineOf binding choice windowOf
       let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
         replacement
       let environment := runtime.blockEnvironment roster
       let before := beforeRoster.flatMap fun actor => [.player actor, .player actor]
       let remaining :=
         (afterRoster.flatMap fun actor => [.player actor, .player actor]) ++
           [.environment, .environment] ++
             roster.flatMap fun actor => [.player actor, .environment]
       let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
       let payload := ApplicationImage.Payload.conditional
         (site.choice.publicationNode fresh state)
         (site.sourceRequestPayload fresh state (site.sourceField fresh state)
           (deadlineOf (site.choice.publicationNode fresh state)) disposition
           (spec.encoding chosen.1))
       (runtime.application.runPolicies players environment before execution).bind fun middle =>
         (runtime.application.playerStep owner middle (.submit payload)).bind fun submitted =>
           (runtime.application.playerStep owner submitted .wait).bind fun waited =>
             runtime.application.runPolicies players environment remaining waited).support) :
    Store.getAs final.native.application.base.memory.store (state.nextField + 1) ty =
      some chosen.1 := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let environment := runtime.blockEnvironment roster
  let before := beforeRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  let after := afterRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  let suffix := Invocation.environment ::
    roster.flatMap fun actor => [Invocation.player actor, .environment]
  let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
  let code := site.code fresh state (site.sourceField fresh state)
    (deadlineOf (site.choice.publicationNode fresh state))
  let payload := fun (result : Option (L.Val spec.secretTy)) =>
    ApplicationImage.Payload.conditional
    (P := P) (L := L) code.endpoint.publicationNode
    (site.sourceRequestPayload fresh state (site.sourceField fresh state)
      (deadlineOf (site.choice.publicationNode fresh state)) disposition result)
  dsimp only at hbranch
  simp only [List.append_assoc] at hbranch
  change final ∈ ((runtime.application.runPolicies players environment before execution).bind
    fun middle => (runtime.application.playerStep owner middle
      (.submit (payload (spec.encoding chosen.1)))).bind fun submitted =>
        (runtime.application.playerStep owner submitted .wait).bind fun waited =>
          runtime.application.runPolicies players environment (after ++ .environment :: suffix)
            waited).support at hbranch
  simp only [FinDist.support_bind, Set.mem_iUnion] at hbranch
  obtain ⟨middle, hmiddle, submitted, hsubmitted, waited, hwaited, hremaining⟩ := hbranch
  rw [MessageApplication.runPolicies_append] at hremaining
  simp only [FinDist.support_bind, Set.mem_iUnion, MessageApplication.runPolicies] at hremaining
  obtain ⟨polled, hafter, included, hincluded, hfinal⟩ := hremaining
  have hbeforeEnvironment : Invocation.environment ∉ before := by simp [before]
  have hbeforeOwner : Invocation.player owner ∉ before := by
    have hnot : owner ∉ beforeRoster := by
      intro hmem
      exact (List.nodup_append.mp (hsplit ▸ hroster)).2.2 owner hmem owner (by simp) rfl
    simp [before, hnot]
  have hafterEnvironment : Invocation.environment ∉ after := by simp [after]
  have hafterOwner : Invocation.player owner ∉ after := by
    have hnot := (List.nodup_cons.mp (List.nodup_append.mp (hsplit ▸ hroster)).2.1).1
    simp [after, hnot]
  have hpacket := runtime.application.runPolicies_submit_wait_branch_packet owner players
    environment before after hbeforeEnvironment hbeforeOwner hafterEnvironment hafterOwner
    execution polled checkpoint.serialsBeforeNext (payload (spec.encoding chosen.1)) (by
      simp only [FinDist.support_bind, Set.mem_iUnion]
      exact ⟨middle, hmiddle, submitted, hsubmitted, waited, hwaited, hafter⟩)
  have hpolls := checkpoint.conditional_polls_source_law_after_others head hinitial horigins
    hroster howner hother disposition hbinding environment before hbeforeEnvironment hbeforeOwner
  have hbeforePair : waited ∈ (runtime.application.runPolicies players environment
      (before ++ [.player owner, .player owner]) execution).support := by
    rw [hpolls]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    refine ⟨middle, hmiddle, chosen, hchosen, submitted, ?_, hwaited⟩
    have hencode : (site.choiceEncodingFor fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state)) disposition
        (ApplicationImage.conditionalTransport spec.secretTy)).encode chosen.1 =
          payload (spec.encoding chosen.1) :=
      site.choiceEncodingFor_encode fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state)) disposition chosen.1
    exact (congrArg (fun message => submitted ∈
      (runtime.application.playerStep owner middle (.submit message)).support) hencode).mpr
        hsubmitted
  have hpollSchedule : roster.flatMap (fun actor =>
      [Invocation.player actor, .player actor]) =
      (before ++ [.player owner, .player owner]) ++ after := by
    simp [hsplit, before, after, List.append_assoc]
  have hpolled : polled ∈ (runtime.application.runPolicies players environment
      (roster.flatMap fun actor => [.player actor, .player actor]) execution).support := by
    rw [hpollSchedule, MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨waited, hbeforePair, hafter⟩
  obtain ⟨includedDisposition, accepted, _, hbinding', hlookup, hhandle, hinclude, hinactive⟩ :=
    checkpoint.conditional_ordinary_inclusion head hinitial horigins hroster howner hother
      polled included hpolled hincluded
  have hdisposition : includedDisposition = disposition :=
    Option.some.inj (hbinding'.symm.trans hbinding)
  subst includedDisposition
  have haccepted : spec.encoding chosen.1 = spec.encoding accepted.1 := by
    have hmessage := Option.some.inj (hpacket.2.symm.trans hlookup)
    have hpayload := congrArg Message.payload hmessage
    injection hpayload with _ hrequest
    exact site.sourceRequestPayload_injective fresh state (site.sourceField fresh state)
      (deadlineOf (site.choice.publicationNode fresh state)) disposition hrequest
  have hchosenValue : chosen.1 = accepted.1 := spec.encoding.injective haccepted
  have hchosenSubtype : accepted = chosen := Subtype.ext hchosenValue.symm
  subst accepted
  obtain ⟨rest, hhead⟩ := head.instructions deadlineOf
  have hnormal : included ∈ (runtime.application.runPolicies players environment
      ((roster.flatMap fun actor => [.player actor, .player actor]) ++ [.environment])
      execution).support := by
    rw [MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨polled, hpolled, by
      simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hincluded⟩
  have hpublic := checkpoint.after_normal_frame (.conditional code) rest hhead
    included final hinactive hnormal hfinal
  have hmemory : final.native.application.base.memory =
      included.native.application.base.memory := congrArg Prod.fst hpublic
  have hpublicationField : code.publicationField = state.nextField + 1 := by
    simp only [code, site, ConditionalPublicationSite.code,
      ConditionalPublicationSite.atHead, PublicChoiceSite.atHead,
      Graph.nodeTarget, BuildState.nextField]
    change (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
      fresh state).initialFields.length + (state.nodes.length + 1) =
        state.initialFields.length + state.nextNode + 1
    rw [compileCore_initialFields]
    simp [BuildState.nextNode]
    omega
  rw [hmemory]
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind,
    FinDist.mem_support_pure] at hinclude
  subst included
  rw [runtime.application.includePending_accept polled.native
    (owner, execution.native.pool.nextSerial owner) _ _ hlookup hhandle]
  change Store.getAs
    (polled.native.application.base.publishConditional code (spec.encoding chosen.1)).memory.store
      (state.nextField + 1) ty = some chosen.1
  rw [← hpublicationField]
  simp only [ApplicationImage.State.publishConditional, Store.getAs, Store.set_eq]
  change (⟨ty, spec.encoding.symm (spec.encoding chosen.1)⟩ : TypedValue L).as? ty =
    some chosen.1
  unfold TypedValue.as?
  simp only [↓reduceDIte, cast_eq, Equiv.symm_apply_apply]

/-- A supported complete ordinary conditional poll determines a supported
encoded source result and its concrete conditional submit/wait branch. -/
theorem conditional_ordinary_support_result
    (head : ConditionalHead spec plan)
    (current : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state)
    (execution polled :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      roster focal replacement blockIndex plan profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal)
    (beforeRoster afterRoster : List P)
    (hsplit : roster = beforeRoster ++ owner :: afterRoster)
    (disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy))
    (hbinding : let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
      (site.code fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state))).binding?
          execution.native.application.base.memory = some disposition)
    (hpolled : polled ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (roster.flatMap fun actor => [.player actor, .player actor]) execution).support) :
    ∃ result,
      result ∈ ((profile owner (.here guard (.reveal publicName owner name .here tail))
        ((current.current.source.toView owner).eraseEnv)).map
          (fun chosen => spec.encoding chosen.1)).support ∧
      polled ∈ (let runtime := root.windowed deadlineOf binding choice windowOf
        let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
          replacement
        let environment := runtime.blockEnvironment roster
        let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
        let payload := ApplicationImage.Payload.conditional
          (site.choice.publicationNode fresh state)
          (site.sourceRequestPayload fresh state (site.sourceField fresh state)
            (deadlineOf (site.choice.publicationNode fresh state)) disposition result)
        (runtime.application.runPolicies players environment
          (beforeRoster.flatMap fun actor => [.player actor, .player actor]) execution).bind
            fun middle =>
              (runtime.application.playerStep owner middle (.submit payload)).bind fun submitted =>
                (runtime.application.playerStep owner submitted .wait).bind fun waited =>
                  runtime.application.runPolicies players environment
                    (afterRoster.flatMap fun actor => [.player actor, .player actor])
                      waited).support := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf
    focal replacement
  let environment := runtime.blockEnvironment roster
  let before := beforeRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
  let code := site.code fresh state (site.sourceField fresh state)
    (deadlineOf (site.choice.publicationNode fresh state))
  let payload := fun (result : Option (L.Val spec.secretTy)) =>
    ApplicationImage.Payload.conditional
    (P := P) (L := L) (site.choice.publicationNode fresh state)
    (site.sourceRequestPayload fresh state (site.sourceField fresh state)
      (deadlineOf (site.choice.publicationNode fresh state)) disposition result)
  let encoding := site.choiceEncodingFor fresh state (site.sourceField fresh state)
    (deadlineOf (site.choice.publicationNode fresh state)) disposition
    (ApplicationImage.conditionalTransport spec.secretTy)
  let kernel : FinDist (Option (L.Val spec.secretTy)) :=
    (profile owner site.choice.decision
      ((current.current.source.toView owner).eraseEnv)).map
        (fun chosen => spec.encoding chosen.1)
  have hbeforeOwner : Invocation.player owner ∉ before := by
    have hnot : owner ∉ beforeRoster := by
      intro hmem
      exact (List.nodup_append.mp (hsplit ▸ hroster)).2.2 owner hmem owner (by simp) rfl
    simp [before, hnot]
  have hencode (chosen : L.Val ty) : encoding.encode chosen = payload (spec.encoding chosen) :=
    site.choiceEncodingFor_encode fresh state (site.sourceField fresh state)
      (deadlineOf (site.choice.publicationNode fresh state)) disposition chosen
  apply runtime.application.ordinary_submit_wait_support_value
    (Choice := Option (L.Val spec.secretTy)) owner payload players environment roster
    beforeRoster afterRoster hsplit execution polled kernel
  · intro middle hmiddle
    have hinput := runtime.application.runPolicies_other_input owner
      (fun state actor command _ => by cases command; rfl)
      players environment before (by simp [before]) hbeforeOwner execution middle hmiddle
    have hrefines := runtime.runPolicies_players_refines players environment before
      (by simp [before]) execution middle checkpoint.refines hmiddle
    have hlaw := checkpoint.conditional_polls_source_law_of_input_eq head hinitial horigins
      hroster howner hother disposition hbinding environment middle hrefines hinput
    change runtime.application.runPolicies players environment [.player owner, .player owner]
      middle = (profile owner site.choice.decision
        ((current.current.source.toView owner).eraseEnv)).bind
          (fun chosen => (runtime.application.playerStep owner middle
            (.submit (encoding.encode chosen.1))).bind
              (fun submitted => runtime.application.playerStep owner submitted .wait)) at hlaw
    rw [FinDist.bind_map, hlaw]
    apply FinDist.bind_congr
    intro chosen _
    rw [hencode]
  · exact hpolled

/-- A complete conditional block identifies the optional source result in its
successor checkpoint with the actual supported ordinary publication. -/
theorem conditional_block_support_at_source
    (head : ConditionalHead spec plan)
    (current : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      roster focal replacement blockIndex plan profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal)
    (beforeRoster afterRoster : List P)
    (hsplit : roster = beforeRoster ++ owner :: afterRoster)
    (result : Option (L.Val spec.secretTy))
    (sourceNext : CoupledAt
      (compileCore tail fresh.2.2
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1).graph
      (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1)
    (hsource : sourceNext.current.source =
      (current.current.source.cons (spec.encoding.symm result)).cons
        (spec.encoding.symm result))
    (hrefines : final.native.application.base.Refines sourceNext.current.graph.1)
    (hfinal : final ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) execution).support) :
    let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
    let code := site.code fresh state (site.sourceField fresh state)
      (deadlineOf (site.choice.publicationNode fresh state))
    ∃ disposition,
      code.binding? execution.native.application.base.memory = some disposition ∧
      result ∈ ((profile owner site.choice.decision
        ((current.current.source.toView owner).eraseEnv)).map
          (fun chosen => spec.encoding chosen.1)).support ∧
      ∃ polled,
        polled ∈ (let runtime := root.windowed deadlineOf binding choice windowOf
          let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
            replacement
          let environment := runtime.blockEnvironment roster
          let payload := ApplicationImage.Payload.conditional code.endpoint.publicationNode
            (site.sourceRequestPayload fresh state (site.sourceField fresh state)
              (deadlineOf (site.choice.publicationNode fresh state)) disposition result)
          (runtime.application.runPolicies players environment
            (beforeRoster.flatMap fun actor => [.player actor, .player actor]) execution).bind
              fun middle =>
                (runtime.application.playerStep owner middle (.submit payload)).bind
                  fun submitted =>
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
  intro site code
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let environment := runtime.blockEnvironment roster
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
  obtain ⟨disposition, hbinding, _⟩ :=
    checkpoint.conditional_binding_disposition head horigins
  obtain ⟨drawn, hdrawnMap, hbranch⟩ := checkpoint.conditional_ordinary_support_result
    head current execution polled hinitial horigins hroster howner hother beforeRoster
    afterRoster hsplit disposition hbinding hpolled
  have hdrawn := hdrawnMap
  rw [FinDist.support_map] at hdrawn
  obtain ⟨chosen, hchosen, rfl⟩ := hdrawn
  let payload : Option (L.Val spec.secretTy) → ApplicationImage.Payload P L :=
    fun result => ApplicationImage.Payload.conditional
    (P := P) (L := L) code.endpoint.publicationNode
    (site.sourceRequestPayload fresh state (site.sourceField fresh state)
      (deadlineOf (site.choice.publicationNode fresh state)) disposition result)
  have hfixedBranch : final ∈
      (let before := beforeRoster.flatMap fun actor => [.player actor, .player actor]
       let remaining :=
         (afterRoster.flatMap fun actor => [.player actor, .player actor]) ++
           [.environment, .environment] ++
             roster.flatMap fun actor => [.player actor, .environment]
       (runtime.application.runPolicies players environment before execution).bind fun middle =>
         (runtime.application.playerStep owner middle
           (.submit (payload (spec.encoding chosen.1)))).bind fun submitted =>
             (runtime.application.playerStep owner submitted .wait).bind fun waited =>
               runtime.application.runPolicies players environment remaining waited).support := by
    dsimp only
    have hpollBranch := hbranch
    dsimp only at hpollBranch
    simp only [FinDist.support_bind, Set.mem_iUnion] at hpollBranch
    obtain ⟨middle, hmiddle, submitted, hsubmitted, waited, hwaited, hafter⟩ := hpollBranch
    simp only [FinDist.support_bind, Set.mem_iUnion]
    refine ⟨middle, hmiddle, submitted, hsubmitted, waited, hwaited, ?_⟩
    simp only [List.append_assoc]
    change final ∈ (runtime.application.runPolicies players environment
      ((afterRoster.flatMap fun actor => [.player actor, .player actor]) ++
        .environment :: suffix) waited).support
    rw [MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion, MessageApplication.runPolicies]
    exact ⟨polled, hafter, included, hincluded, hremaining⟩
  have hfinalStore := checkpoint.conditional_fixed_branch_publication head current execution final
    hinitial horigins hroster howner hother beforeRoster afterRoster hsplit disposition hbinding
    chosen hchosen hfixedBranch
  have hrecorded : Store.getAs final.native.application.base.memory.store
      (state.nextField + 1) ty = some (spec.encoding.symm result) := by
    let added := ((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
      publicName owner .here fresh.2.1
    obtain ⟨fieldSpec, hfield, hty, hownerField⟩ :=
      compileCore_fieldOf_spec tail fresh.2.2 added.1 (VHasVar.here)
    have hpublicField : (compileCore tail fresh.2.2 added.1).graph.fieldRefPublic
        ⟨added.1.fieldOf VHasVar.here, ty⟩ :=
      ⟨fieldSpec, hfield, hty, hownerField⟩
    have hrepresented := hrefines.memory.publicFields _ hpublicField
    rw [sourceNext.current.agrees VHasVar.here] at hrepresented
    have hsourceValue := congrArg (fun env => env.get VHasVar.here) hsource
    simp only [VEnv.get, VEnv.cons] at hsourceValue
    have hfieldEq : added.1.fieldOf VHasVar.here = state.nextField + 1 := by
      simp [added, BuildState.nextField, BuildState.nextNode]
      omega
    rw [hfieldEq] at hrepresented
    exact hrepresented.trans (congrArg some hsourceValue)
  have hresult : spec.encoding chosen.1 = result := by
    apply spec.encoding.symm.injective
    simpa using Option.some.inj (hfinalStore.symm.trans hrecorded)
  have hdrawnResult : result ∈ ((profile owner site.choice.decision
      ((current.current.source.toView owner).eraseEnv)).map
        (fun selected => spec.encoding selected.1)).support := by
    rw [← hresult]
    exact hdrawnMap
  have hbranchResult : polled ∈
      ((runtime.application.runPolicies players environment
        (beforeRoster.flatMap fun actor => [.player actor, .player actor]) execution).bind
          fun middle => (runtime.application.playerStep owner middle
            (.submit (payload result))).bind fun submitted =>
              (runtime.application.playerStep owner submitted .wait).bind fun waited =>
                runtime.application.runPolicies players environment
                  (afterRoster.flatMap fun actor => [.player actor, .player actor])
                    waited).support := by
    rw [← hresult]
    exact hbranch
  exact ⟨disposition, hbinding, hdrawnResult, polled, hbranchResult, included, hincluded,
    hremaining⟩
end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.conditional_fixed_branch_publication'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.conditional_fixed_branch_publication

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.conditional_ordinary_support_result'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.conditional_ordinary_support_result

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.conditional_block_support_at_source'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.conditional_block_support_at_source
