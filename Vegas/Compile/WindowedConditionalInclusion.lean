/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedConditionalAdmission
import Vegas.Compile.WindowedConditionalSubmission
import Vegas.Compile.WindowedNormalService

/-! # Ordinary inclusion of unchanged conditional submissions -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

private theorem playerStep_frozen (runtime : WindowedApplication P L) (who : P)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.PlayerCommand)
    (hnext : next ∈ (runtime.application.playerStep who execution command).support) :
    next.native.application.base.frozen = execution.native.application.base.frozen := by
  have hnative : next.native ∈
      ((runtime.application.playerStep who execution command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [runtime.application.playerStep_native] at hnative
  cases command with
  | privateCommand command =>
      cases command with
      | register slot value =>
          simp only [PlayerCommand.toAction, MessageApplication.step, application,
            FinDist.mem_support_pure] at hnative
          rw [hnative]
          rfl
  | submit payload | replay id | wait =>
      simp only [PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at hnative
      rw [hnative]

private theorem runPolicies_players_frozen (runtime : WindowedApplication P L)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@Invocation P)) (hplayers : Invocation.environment ∉ schedule)
    (execution next : runtime.application.PolicyExecution)
    (hnext : next ∈
      (runtime.application.runPolicies players environment schedule execution).support) :
    next.native.application.base.frozen = execution.native.application.base.frozen := by
  induction schedule generalizing execution with
  | nil =>
      simp only [MessageApplication.runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      rfl
  | cons invocation rest ih =>
      simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      cases invocation with
      | environment => exact False.elim (hplayers (List.mem_cons_self ..))
      | player who =>
          simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, _, hstep⟩ := hmiddle
          exact (ih (fun hmem => hplayers (List.mem_cons_of_mem _ hmem)) middle hnext).trans
            (runtime.playerStep_frozen who execution middle command hstep)

end Vegas.WindowedApplication

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

/-- Normal service accepts the actual source-supported packet emitted by an
unchanged conditional owner. The accepted disposition, frozen opening value,
and inactivity are derived from the initialized checkpoint. -/
theorem conditional_ordinary_inclusion
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex plan profile current execution)
    (head : ConditionalHead spec plan)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal)
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
    let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
    let code := site.code fresh state (site.sourceField fresh state)
      (deadlineOf (site.choice.publicationNode fresh state))
    ∃ disposition chosen,
      chosen ∈ (profile owner site.choice.decision
        ((current.current.source.toView owner).eraseEnv)).support ∧
      code.binding? execution.native.application.base.memory = some disposition ∧
      polled.native.pool.lookup (owner, execution.native.pool.nextSerial owner) =
        some ⟨(owner, execution.native.pool.nextSerial owner),
          .conditional code.endpoint.publicationNode
            (site.sourceRequestPayload fresh state (site.sourceField fresh state)
              (deadlineOf (site.choice.publicationNode fresh state)) disposition
              (spec.encoding chosen.1))⟩ ∧
      runtime.handle polled.native.application
          ⟨(owner, execution.native.pool.nextSerial owner),
            .conditional code.endpoint.publicationNode
              (site.sourceRequestPayload fresh state (site.sourceField fresh state)
                (deadlineOf (site.choice.publicationNode fresh state)) disposition
                (spec.encoding chosen.1))⟩ =
        some (runtime.advanceTo polled.native.application
          (polled.native.application.base.publishConditional code (spec.encoding chosen.1))) ∧
      included ∈ (runtime.application.environmentPolicyStep polled
        (.include (owner, execution.native.pool.nextSerial owner))).support ∧
      runtime.image.activeAddress? included.native.application.base.memory ≠
        some code.endpoint.publicationNode := by
  intro runtime site code
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let polls := roster.flatMap fun actor => [Invocation.player actor, .player actor]
  obtain ⟨disposition, hbinding, hcanonical⟩ :=
    checkpoint.conditional_binding_disposition head horigins
  obtain ⟨chosen, hchosen, hserial, hlookup⟩ :=
    checkpoint.conditional_ordinary_submission head hinitial horigins hroster howner hother
      disposition hbinding polled hpolled
  obtain ⟨rest, hhead⟩ := head.instructions deadlineOf
  have hpublic := runtime.runPolicies_players_publicState players
    (runtime.blockEnvironment roster) polls (by simp [polls]) execution polled hpolled
  have hmemory : polled.native.application.base.memory =
      execution.native.application.base.memory := congrArg Prod.fst hpublic
  have hactivationEq : polled.native.application.active =
      execution.native.application.active := congrArg Prod.snd hpublic
  have hrefines := runtime.runPolicies_players_refines players (runtime.blockEnvironment roster)
    polls (by simp [polls]) execution polled checkpoint.refines hpolled
  have hfrozenEq := runtime.runPolicies_players_frozen players (runtime.blockEnvironment roster)
    polls (by simp [polls]) execution polled hpolled
  have hbindingPolled : code.binding? polled.native.application.base.memory =
      some disposition := by rw [hmemory, hbinding]
  have hlegal := chosen.2
  have hfrozenInitial : ∀ handle value, disposition = .opaque handle →
      spec.encoding chosen.1 = some value →
      (execution.native.application.base.frozen (state.fieldOf spec.binding)).bind
        (fun typed => typed.as? spec.secretTy) = some value := by
    intro handle value hopaque hvalue
    subst disposition
    have hhandle := hcanonical handle rfl
    subst handle
    have haccepted := (code.binding?_opaque_iff execution.native.application.base.memory
      (owner, state.fieldOf spec.binding)).1 hbinding
    exact checkpoint.conditional_legal_choice_frozen (by
      simp only [windowedPlayers, Function.update_of_ne hother])
      haccepted chosen.1 hlegal value hvalue
  obtain ⟨activation, hactivation, hkey, _⟩ :=
    checkpoint.active_origin_clock (.conditional code) rest hhead
  have hactive : runtime.image.activeAddress? polled.native.application.base.memory =
      some activation.key := by
    rw [hmemory, hkey]
    exact checkpoint.activeAddress?_head (.conditional code) rest hhead
  have hindexOriginal := checkpoint.instruction_at (.conditional code) rest hhead
  have hlookupOriginal := root.image_lookup_of_mem deadlineOf (.conditional code)
    (List.mem_of_getElem? hindexOriginal)
  have hcode : runtime.image.lookup activation.key = some (.conditional code) := by
    rw [hkey]
    change runtime.image.lookup code.endpoint.publicationNode = some (.conditional code)
    change (root.image deadlineOf).lookup code.endpoint.publicationNode =
      some (.conditional code) at hlookupOriginal
    simp only [runtime, windowed, ApplicationImage.lookup_withChoiceTimeouts,
      ApplicationImage.lookup_withBindingTimeouts, hlookupOriginal, Option.map_some,
      ApplicationInstruction.withBindingTimeouts, ApplicationInstruction.withChoiceTimeouts]
  have hcommand := checkpoint.blockEnvironment_after_ordinary_polls
    (.conditional code) rest hhead rfl hpolled hserial _ hlookup
  change runtime.blockEnvironment roster polled.environmentHistory
      (State.environmentView runtime.application polled.native) =
        FinDist.pure (.include (owner, execution.native.pool.nextSerial owner)) at hcommand
  change included ∈ (runtime.application.invoke players (runtime.blockEnvironment roster)
    polled .environment).support at hincluded
  simp only [MessageApplication.invoke, hcommand, FinDist.pure_bind] at hincluded
  have hincludedStep := hincluded
  have hadmission := runtime.handle_source_conditional_and_include_inactive guard tail spec fresh
    state (site.sourceField fresh state) (deadlineOf (site.choice.publicationNode fresh state))
    current (head.publiclyValidatable) polled.native.application activation
    (execution.native.pool.nextSerial owner) hrefines disposition hbindingPolled hcanonical
    chosen.1 hlegal (by
      intro handle value hopaque hvalue
      rw [hfrozenEq]
      exact hfrozenInitial handle value hopaque hvalue)
    (hactivationEq.trans hactivation) hactive hcode polled.native.pool polled.native.receipts
    (by rw [hkey]; exact hlookup)
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind,
    FinDist.mem_support_pure] at hincluded
  subst included
  refine ⟨disposition, chosen, hchosen, hbinding, hlookup, ?_, hincludedStep, ?_⟩
  · rw [hkey] at hadmission
    exact hadmission.1
  · rw [hkey] at hadmission
    exact hadmission.2

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.conditional_ordinary_inclusion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.conditional_ordinary_inclusion
