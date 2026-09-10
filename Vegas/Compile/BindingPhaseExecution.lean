/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.BindingImageExecution
import Vegas.Compile.BindingSourceCoupling
import Interaction.MessagePoolFreshness
import Vegas.Compile.ApplicationOrderPhase

/-! # Exact execution of a generated opaque-binding phase

Two owner invocations register one source-kernel draw and submit its opaque
handle.  A following environment invocation includes that freshly allocated
envelope.  The law retains the complete policy execution and couples every
supported draw to the exact one-commit source successor.
-/

noncomputable section

namespace Vegas.SourceDecisionSite

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The exact three-invocation law for a generated opaque binding: private
registration, canonical handle submission, and service of the fresh envelope.

The environment premise is the local service boundary.  It does not constrain
unrelated traffic outside this phase and does not assert general progress. -/
theorem binding_phase_source_law
    {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (fresh : FreshBindings (.commit name who guard tail))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard tail) fresh build).graph build)
    (image : ApplicationImage P L)
    (sourcePolicy :
      (visible : Env L.Val (eraseVCtx (viewVCtx who Γ))) →
        FinDist { value : L.Val ty // evalGuard guard value visible = true })
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (execution : image.application.PolicyExecution)
    (hrefines : execution.native.application.Refines current.current.graph.1)
    (hconsistent : image.RegistrationConsistent execution)
    (hcode : image.lookup
      ((.here guard tail : SourceDecisionSite who
        (.commit name who guard tail) Γ name ty guard).bindingCode fresh build
          ((.here guard tail : SourceDecisionSite who
            (.commit name who guard tail) Γ name ty guard).compiledField fresh build)).node =
        some (.bind
      ((.here guard tail : SourceDecisionSite who
        (.commit name who guard tail) Γ name ty guard).bindingCode fresh build
          ((.here guard tail : SourceDecisionSite who
            (.commit name who guard tail) Γ name ty guard).compiledField fresh build))))
    (reads : ReadEnv L
      (eventGuardOf build who guard).choiceReads)
    (hpolicy : ∀ history,
      players who history
          (MessageApplication.State.observe image.application execution.native who) =
        (.here guard tail : SourceDecisionSite who
          (.commit name who guard tail) Γ name ty guard).bindingPolicy
            fresh build image sourcePolicy history
            (MessageApplication.State.observe image.application execution.native who))
    (henvironment : ∀ chosen ∈
        (sourcePolicy ((current.current.source.toView who).eraseEnv)).support,
      ∀ registered ∈ (image.application.playerStep who execution
        (.privateCommand (.register
          ((.here guard tail : SourceDecisionSite who
            (.commit name who guard tail) Γ name ty guard).compiledField fresh build)
          ⟨ty, chosen.1⟩))).support,
      ∀ submitted ∈ (image.application.playerStep who registered
        (.submit (.binding
          ((.here guard tail : SourceDecisionSite who
            (.commit name who guard tail) Γ name ty guard).bindingCode fresh build
              ((.here guard tail : SourceDecisionSite who
                (.commit name who guard tail) Γ name ty guard).compiledField fresh build)).node
          (who, (.here guard tail : SourceDecisionSite who
            (.commit name who guard tail) Γ name ty guard).compiledField fresh build)))).support,
      environment submitted.environmentHistory
          (MessageApplication.State.environmentView image.application submitted.native) =
        FinDist.pure (.include
          (who, execution.native.pool.nextSerial who)))
    (hlookupFresh : execution.native.pool.lookup
      (who, execution.native.pool.nextSerial who) = none)
    (hcache : image.registrationCache
      ((.here guard tail : SourceDecisionSite who
        (.commit name who guard tail) Γ name ty guard).compiledField fresh build)
      (execution.principalHistory who) = none)
    (hsubmitted : ChoiceEncoding.cachedValue image.application
      (((.here guard tail : SourceDecisionSite who
          (.commit name who guard tail) Γ name ty guard).bindingCode fresh build
            ((.here guard tail : SourceDecisionSite who
              (.commit name who guard tail) Γ name ty guard).compiledField fresh build)).encoding
        |>.submission image.application)
      (execution.principalHistory who) = none)
    (hreadout : image.ownerReadout? who
      (eventGuardOf build who guard).choiceReads
      (execution.principalHistory who)
      (MessageApplication.State.observe image.application execution.native who) = some reads)
    (hview : viewEnvOfReadEnv build who reads =
      (current.current.source.toView who).eraseEnv) :
    let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
      .here guard tail
    let field := site.compiledField fresh build
    let code := site.bindingCode fresh build field
    let id := (who, execution.native.pool.nextSerial who)
    (image.application.runPolicies players environment
        [.player who, .player who, .environment] execution =
      (sourcePolicy ((current.current.source.toView who).eraseEnv)).bind fun chosen =>
        (image.application.playerStep who execution
          (.privateCommand (.register field ⟨ty, chosen.1⟩))).bind fun registered =>
          (image.application.playerStep who registered
            (.submit (.binding code.node (who, field)))).bind fun submitted =>
            image.application.environmentPolicyStep submitted (.include id)) ∧
    (∀ chosen ∈ (sourcePolicy
        ((current.current.source.toView who).eraseEnv)).support,
      ∀ registered ∈ (image.application.playerStep who execution
        (.privateCommand (.register field ⟨ty, chosen.1⟩))).support,
      ∀ submitted ∈ (image.application.playerStep who registered
        (.submit (.binding code.node (who, field)))).support,
      ∀ included ∈ (image.application.environmentPolicyStep submitted
        (.include id)).support,
      ∃ next : CoupledAt
          (compileCore (.commit name who guard tail) fresh build).graph
          (build.addCommitEvent name who guard fresh.1).1,
        next.current.source = current.current.source.cons chosen.1 ∧
        included.native.application.Refines next.current.graph.1 ∧
        ApplicationImage.AcceptedSnapshot field (.opaque (who, field))
          (some ⟨ty, chosen.1⟩) included.native.application) ∧
    (image.activeAddress? execution.native.application.memory = some code.node →
      image.orderedApplication.runPolicies players environment
          [.player who, .player who, .environment] execution =
        image.application.runPolicies players environment
          [.player who, .player who, .environment] execution) := by
  dsimp only
  let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
    .here guard tail
  let field := site.compiledField fresh build
  let code := site.bindingCode fresh build field
  let id := (who, execution.native.pool.nextSerial who)
  have hreadyData := binding_ready_at_source_prefix guard tail fresh build current
    execution.native.application.memory.done hrefines.memory.completed
  have hnotDone : execution.native.application.memory.done code.node = false :=
    hreadyData.2.1
  have hrequires : code.requires.all execution.native.application.memory.done = true :=
    hreadyData.2.2
  have hready := hreadyData.1
  have hfield : code.sourceField =
      (compileCore (.commit name who guard tail) fresh build).graph.nodeTarget
        (site.compiledNode fresh build) := rfl
  have haccepted : execution.native.application.memory.accepted code.sourceField = none := by
    apply hrefines.bindings.accepted_eq_none_of_store_eq_none code.sourceField
    cases hstored : current.current.graph.1.store code.sourceField with
    | none => rfl
    | some typed =>
        have hpresent : Store.getAs current.current.graph.1.store code.sourceField typed.ty =
            some typed.value := by
          simp [Store.getAs, hstored, TypedValue.as?]
        have habsent := reachable_getAs_nodeTarget_eq_none hrefines.reachable
          (site.compiledNode fresh build) hready.1 typed.ty
        rw [hfield, habsent] at hpresent
        contradiction
  have hresolved : code.resolved execution.native.application.memory = false := by
    simp [BindingCode.resolved, haccepted, hnotDone]
  have htwo := site.bindingPolicy_two_invocations_source_law fresh build image
    sourcePolicy players environment execution hpolicy current.current.source reads
    hresolved hrequires hcache hsubmitted hreadout hview
  refine ⟨?_, ?_, ?_⟩
  · rw [show ([.player who, .player who, .environment] : List (@Invocation P)) =
        [.player who, .player who] ++ [.environment] from rfl,
      MessageApplication.runPolicies_append, htwo, FinDist.bind_bind]
    apply FinDist.bind_congr
    intro chosen hchosen
    rw [FinDist.bind_bind]
    apply FinDist.bind_congr
    intro registered hregistered
    apply FinDist.bind_congr
    intro submitted hsubmittedStep
    simp only [MessageApplication.runPolicies, MessageApplication.invoke]
    rw [henvironment chosen hchosen registered hregistered submitted hsubmittedStep]
    simp only [FinDist.pure_bind]
    exact FinDist.bind_pure _
  · intro chosen hchosen registered hregistered submitted hsubmittedStep included hincluded
    have hregisteredConsistent := image.playerStep_registrationConsistent execution registered
      who (.privateCommand (.register field ⟨ty, chosen.1⟩)) hconsistent hregistered
    have hregisteredCache : image.registrationCache field
        (registered.principalHistory who) = some ⟨ty, chosen.1⟩ := by
      have hhistory := image.application.playerStep_history_self who execution
        (.privateCommand (.register field ⟨ty, chosen.1⟩)) registered hregistered
      unfold ApplicationImage.registrationCache at hcache ⊢
      rw [hhistory]
      exact ((ApplicationImage.registrationEncoding field).privateCommand
        image.application).cachedValue_append_encoded_of_none image.application
          _ _ ⟨ty, chosen.1⟩ hcache
    have hsubmittedConsistent := image.playerStep_registrationConsistent registered submitted
      who (.submit (.binding code.node (who, field))) hregisteredConsistent hsubmittedStep
    have hsubmittedCache : image.registrationCache field
        (submitted.principalHistory who) = some ⟨ty, chosen.1⟩ := by
      unfold ApplicationImage.registrationCache at hregisteredCache ⊢
      exact ((ApplicationImage.registrationEncoding field).privateCommand
        image.application).playerStep_cachedValue_of_some image.application who
          registered submitted (.submit (.binding code.node (who, field))) ⟨ty, chosen.1⟩
          hregisteredCache hsubmittedStep
    have hprepared : submitted.native.application.prepared.lookup (who, field) =
        some ⟨ty, chosen.1⟩ :=
      (hsubmittedConsistent who field).symm.trans hsubmittedCache
    have hregisteredNative : registered.native.pool = execution.native.pool := by
      have hnative : registered.native ∈
          ((image.application.playerStep who execution
            (.privateCommand (.register field ⟨ty, chosen.1⟩))).map
              MessageInterface.PolicyExecution.native).support := by
        rw [FinDist.support_map]
        exact ⟨registered, hregistered, rfl⟩
      rw [image.application.playerStep_native] at hnative
      simp only [PlayerCommand.toAction, MessageApplication.step,
        ApplicationImage.application, FinDist.mem_support_pure] at hnative
      rw [hnative]
    have hsubmittedNative : submitted.native.pool =
        (registered.native.pool.submit who (.binding code.node (who, field))).2 := by
      have hnative : submitted.native ∈
          ((image.application.playerStep who registered
            (.submit (.binding code.node (who, field)))).map
              MessageInterface.PolicyExecution.native).support := by
        rw [FinDist.support_map]
        exact ⟨submitted, hsubmittedStep, rfl⟩
      rw [image.application.playerStep_native] at hnative
      simp only [PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at hnative
      rw [hnative]
    have hlookup : submitted.native.pool.lookup id =
        some ⟨id, .binding code.node (who, field)⟩ := by
      rw [hsubmittedNative, hregisteredNative]
      exact execution.native.pool.lookup_submit_fresh who _ hlookupFresh
    have hregisterApplication : registered.native.application =
        execution.native.application.register who field ⟨ty, chosen.1⟩ := by
      have hnative : registered.native ∈
          ((image.application.playerStep who execution
            (.privateCommand (.register field ⟨ty, chosen.1⟩))).map
              MessageInterface.PolicyExecution.native).support := by
        rw [FinDist.support_map]
        exact ⟨registered, hregistered, rfl⟩
      rw [image.application.playerStep_native] at hnative
      simp only [PlayerCommand.toAction, MessageApplication.step,
        ApplicationImage.application, FinDist.mem_support_pure] at hnative
      simpa using congrArg MessageInterface.State.application hnative
    have hsubmitApplication : submitted.native.application =
        registered.native.application := by
      have hnative : submitted.native ∈
          ((image.application.playerStep who registered
            (.submit (.binding code.node (who, field)))).map
              MessageInterface.PolicyExecution.native).support := by
        rw [FinDist.support_map]
        exact ⟨submitted, hsubmittedStep, rfl⟩
      rw [image.application.playerStep_native] at hnative
      simp only [PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at hnative
      simpa using congrArg MessageInterface.State.application hnative
    have hrefinesSubmitted : submitted.native.application.Refines
        current.current.graph.1 := by
      rw [hsubmitApplication, hregisterApplication]
      exact hrefines.register who field ⟨ty, chosen.1⟩
    obtain ⟨next, hsource, hrefinesNext, hsnapshot⟩ :=
      include_binding_source_coupling guard tail fresh build current image
        submitted.native hrefinesSubmitted code.node
        (execution.native.pool.nextSerial who) hcode chosen.1 hprepared hlookup chosen.2
    have hincludedNative : included.native =
        image.application.includePending submitted.native id := by
      simp only [MessageApplication.environmentPolicyStep,
        EnvironmentPolicyCommand.toAction, MessageApplication.advance,
        MessageApplication.step, FinDist.pure_bind,
        FinDist.mem_support_pure] at hincluded
      exact congrArg MessageInterface.PolicyExecution.native hincluded
    refine ⟨next, hsource, ?_, ?_⟩
    · rw [hincludedNative]
      exact hrefinesNext
    · rw [hincludedNative]
      exact hsnapshot
  · intro hactive
    exact image.ordered_private_submit_environment_phase_eq players environment who execution
      (sourcePolicy ((current.current.source.toView who).eraseEnv))
      (fun chosen => .register field ⟨ty, chosen.1⟩)
      (fun _ => .binding code.node (who, field)) code.node htwo henvironment hlookupFresh
      (by intro _ _; rfl) hactive

end Vegas.SourceDecisionSite

/-- info: 'Vegas.SourceDecisionSite.binding_phase_source_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceDecisionSite.binding_phase_source_law
