/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImageProvenance
import Vegas.Compile.WindowedProjection

/-! # Binding provenance for activation-windowed executions

Activation-relative deadline handling preserves the preparation and frozen
snapshot invariants used by accepted binding provenance, including genuine
expiry messages handled at their retimed deadlines.
-/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The first private registration in each owner's history is exactly the
write-once preparation stored at that owner's slot. This invariant also
identifies empty slots before an unchanged owner draws a new source value. -/
def RegistrationConsistent (runtime : WindowedApplication P L)
    (execution : runtime.application.PolicyExecution) : Prop :=
  ∀ who slot, runtime.image.registrationCache slot
      ((execution.principalHistory who).map fun entry =>
        show runtime.image.application.PlayerEntry from runtime.erasePlayerEntry entry) =
    execution.native.application.base.prepared.lookup (who, slot)

private theorem handle_snapshots (runtime : WindowedApplication P L)
    (owner : P) (valid : Nat → TypedValue L → Prop)
    (state next : runtime.application.Application)
    (message : Message P (ApplicationImage.Payload P L))
    (hsnapshots : ApplicationImage.PreparedSnapshots owner valid state.base)
    (hmessage : ApplicationImage.PreparedMessage owner valid state.base.prepared message)
    (hnext : runtime.handle state message = some next) :
    ApplicationImage.PreparedSnapshots owner valid next.base := by
  obtain ⟨activation, base, _, _, hbase, rfl⟩ := runtime.handle_some state next message hnext
  have hunderlying : (runtime.atOrigin activation.since).handle state.base message = some base :=
    (runtime.atOrigin activation.since).application.withAdmission_handle_some
      (runtime.atOrigin activation.since).admitsMessage
      (runtime.atOrigin activation.since).admitsEnvironment state.base base message hbase
  exact ApplicationImage.PreparedSnapshots.handle (runtime.atOrigin activation.since)
    owner valid state.base base message hsnapshots hmessage hunderlying

private theorem handle_prepared (runtime : WindowedApplication P L)
    (state next : runtime.application.Application)
    (message : Message P (ApplicationImage.Payload P L))
    (hnext : runtime.handle state message = some next) :
    next.base.prepared = state.base.prepared := by
  obtain ⟨activation, base, _, _, hbase, rfl⟩ := runtime.handle_some state next message hnext
  have hunderlying : (runtime.atOrigin activation.since).handle state.base message = some base :=
    (runtime.atOrigin activation.since).application.withAdmission_handle_some
      (runtime.atOrigin activation.since).admitsMessage
      (runtime.atOrigin activation.since).admitsEnvironment state.base base message hbase
  exact ((runtime.atOrigin activation.since).handle_binding_effect
    state.base base message hunderlying).1

private theorem environmentStep_prepared
    (runtime : WindowedApplication P L)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.EnvironmentPolicyCommand)
    (hnext : next ∈ (runtime.application.environmentPolicyStep execution command).support) :
    next.native.application.base.prepared =
      execution.native.application.base.prepared := by
  have hnative : next.native ∈
      ((runtime.application.environmentPolicyStep execution command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [runtime.application.environmentStep_native] at hnative
  cases command with
  | deliver observer id | wait =>
      simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at hnative
      rw [hnative]
  | «include» id =>
      simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at hnative
      rw [hnative]
      cases hlookup : execution.native.pool.lookup id with
      | none =>
          rw [runtime.application.includePending_missing execution.native id hlookup]
      | some message =>
          cases hhandle : runtime.handle execution.native.application message with
          | none =>
              rw [runtime.application.includePending_reject execution.native id message
                hlookup hhandle]
          | some application =>
              rw [runtime.application.includePending_accept execution.native id message
                application hlookup hhandle]
              obtain ⟨activation, base, _, _, hbase, happlication⟩ :=
                runtime.handle_some execution.native.application application message hhandle
              subst application
              have hunderlying : (runtime.atOrigin activation.since).handle
                  execution.native.application.base message = some base :=
                (runtime.atOrigin activation.since).application.withAdmission_handle_some
                  (runtime.atOrigin activation.since).admitsMessage
                  (runtime.atOrigin activation.since).admitsEnvironment
                  execution.native.application.base base message hbase
              exact ((runtime.atOrigin activation.since).handle_binding_effect
                execution.native.application.base base message hunderlying).1
  | application applicationCommand =>
      cases applicationCommand with
      | advance clock =>
          have heq : next.native = { execution.native with application :=
              { execution.native.application with
                base := execution.native.application.base.advance clock } } := by
            simpa [EnvironmentPolicyCommand.toAction, MessageApplication.step,
              WindowedApplication.application, environmentStep] using hnative
          rw [heq]
          rfl
      | sample address =>
          change next.native ∈
            ((runtime.environmentStep execution.native.application (.sample address)).map
              fun application => { execution.native with application }).support at hnative
          rw [FinDist.support_map] at hnative
          obtain ⟨application, happlication, heq⟩ := hnative
          rw [← heq]
          simp only [environmentStep, FinDist.support_map, Set.mem_image] at happlication
          obtain ⟨base, hbase, rfl⟩ := happlication
          change base ∈ ((runtime.image.application.withAdmission
            runtime.image.admitsMessage runtime.image.admitsEnvironment).environmentStep
              execution.native.application.base (.sample address)).support at hbase
          rcases runtime.image.application.withAdmission_environment_support
              runtime.image.admitsMessage runtime.image.admitsEnvironment
              execution.native.application.base base (.sample address) hbase with rfl | hsample
          · rfl
          · rcases runtime.image.sample_support execution.native.application.base
                address base hsample with rfl | hsampled
            · rfl
            · obtain ⟨code, reads, value, _, _, _, _, _, rfl⟩ := hsampled
              rfl

private theorem playerStep_registrationConsistent
    (runtime : WindowedApplication P L)
    (execution next : runtime.application.PolicyExecution) (who : P)
    (command : runtime.application.PlayerCommand)
    (hconsistent : RegistrationConsistent runtime execution)
    (hnext : next ∈ (runtime.application.playerStep who execution command).support) :
    RegistrationConsistent runtime next := by
  cases command with
  | privateCommand privateCommand =>
      cases privateCommand with
      | register actual value =>
          simp only [MessageApplication.playerStep, PlayerCommand.toAction,
            MessageApplication.advance, MessageApplication.step, application,
            FinDist.pure_bind, FinDist.mem_support_pure] at hnext
          subst next
          intro owner slot
          by_cases howner : owner = who
          · subst owner
            simp only [if_pos, List.map_append, List.map_cons, List.map_nil,
              erasePlayerEntry, erasePlayerCommand]
            exact ApplicationImage.registration_after_register runtime.image who _ _ _ actual
              value (hconsistent who) slot
          · simp only [if_neg howner, ApplicationImage.State.register]
            rw [hconsistent owner slot]
            exact (ApplicationImage.lookup_sealValue_other
              execution.native.application.base.prepared who actual value (owner, slot) (by
                intro heq
                exact howner (Prod.mk.inj heq).1)).symm
  | submit payload | replay id | wait =>
      simp only [MessageApplication.playerStep, PlayerCommand.toAction,
        MessageApplication.advance, MessageApplication.step, FinDist.pure_bind,
        FinDist.mem_support_pure] at hnext
      subst next
      intro owner slot
      by_cases howner : owner = who
      · subst owner
        simp only [if_pos, List.map_append, List.map_cons, List.map_nil,
          erasePlayerEntry]
        rw [ApplicationImage.registrationCache_append_undecoded]
        · exact hconsistent who slot
        · rfl
      · simp only [if_neg howner]
        exact hconsistent owner slot

private theorem environmentStep_registrationConsistent
    (runtime : WindowedApplication P L)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.EnvironmentPolicyCommand)
    (hconsistent : RegistrationConsistent runtime execution)
    (hnext : next ∈ (runtime.application.environmentPolicyStep execution command).support) :
    RegistrationConsistent runtime next := by
  have hhistory := runtime.application.environmentStep_principalHistory
    execution command next hnext
  intro who slot
  rw [congrFun hhistory who, hconsistent who slot]
  exact congrArg (fun prepared => prepared.lookup (who, slot))
    (environmentStep_prepared runtime execution next command hnext).symm

private theorem playerStep_provenance
    (runtime : WindowedApplication P L) (owner : P)
    (valid : Nat → TypedValue L → Prop)
    (execution next : runtime.application.PolicyExecution) (who : P)
    (command : runtime.application.PlayerCommand)
    (hmessages : execution.native.pool.Satisfies
      (ApplicationImage.PreparedMessage owner valid
        execution.native.application.base.prepared))
    (hsnapshots : ApplicationImage.PreparedSnapshots owner valid
      execution.native.application.base)
    (hsubmit : ∀ payload, command = .submit payload →
      ApplicationImage.PreparedMessage owner valid
        execution.native.application.base.prepared
        ⟨(who, execution.native.pool.nextSerial who), payload⟩)
    (hnext : next ∈ (runtime.application.playerStep who execution command).support) :
    next.native.pool.Satisfies (ApplicationImage.PreparedMessage owner valid
        next.native.application.base.prepared) ∧
      ApplicationImage.PreparedSnapshots owner valid next.native.application.base := by
  cases command with
  | privateCommand command =>
      cases command with
      | register slot value =>
          simp only [MessageApplication.playerStep, PlayerCommand.toAction,
            MessageApplication.advance, MessageApplication.step, application,
            FinDist.pure_bind, FinDist.mem_support_pure] at hnext
          subst next
          have hregistered := ApplicationImage.BindingProvenance.register runtime.image owner valid
            ⟨execution.native.application.base, execution.native.pool, execution.native.receipts⟩
            who slot value ⟨hmessages, hsnapshots⟩
          exact ⟨hregistered.messages, hregistered.snapshots⟩
  | submit payload =>
      simp only [MessageApplication.playerStep, PlayerCommand.toAction,
        MessageApplication.advance, MessageApplication.step, FinDist.pure_bind,
        FinDist.mem_support_pure] at hnext
      subst next
      exact ⟨hmessages.submit who payload (hsubmit payload rfl), hsnapshots⟩
  | replay id =>
      simp only [MessageApplication.playerStep, PlayerCommand.toAction,
        MessageApplication.advance, MessageApplication.step, FinDist.pure_bind,
        FinDist.mem_support_pure] at hnext
      subst next
      exact ⟨hmessages.replay who id, hsnapshots⟩
  | wait =>
      simp only [MessageApplication.playerStep, PlayerCommand.toAction,
        MessageApplication.advance, FinDist.pure_bind, FinDist.mem_support_pure] at hnext
      subst next
      exact ⟨hmessages, hsnapshots⟩

private theorem environmentStep_provenance
    (runtime : WindowedApplication P L) (owner : P)
    (valid : Nat → TypedValue L → Prop)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.EnvironmentPolicyCommand)
    (hmessages : execution.native.pool.Satisfies
      (ApplicationImage.PreparedMessage owner valid
        execution.native.application.base.prepared))
    (hsnapshots : ApplicationImage.PreparedSnapshots owner valid
      execution.native.application.base)
    (hnext : next ∈ (runtime.application.environmentPolicyStep execution command).support) :
    next.native.pool.Satisfies (ApplicationImage.PreparedMessage owner valid
        next.native.application.base.prepared) ∧
      ApplicationImage.PreparedSnapshots owner valid next.native.application.base := by
  have hnative : next.native ∈
      ((runtime.application.environmentPolicyStep execution command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [runtime.application.environmentStep_native] at hnative
  cases command with
  | deliver observer id =>
      simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact ⟨hmessages.deliver observer id, hsnapshots⟩
  | «include» id =>
      simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at hnative
      rw [hnative]
      cases hlookup : execution.native.pool.lookup id with
      | none =>
          rw [runtime.application.includePending_missing execution.native id hlookup]
          exact ⟨hmessages, hsnapshots⟩
      | some message =>
          have hmessage := hmessages.1 message (List.mem_of_find?_eq_some hlookup)
          cases hhandle : runtime.handle execution.native.application message with
          | none =>
              rw [runtime.application.includePending_reject execution.native id message
                hlookup hhandle]
              exact ⟨hmessages.includePending id, hsnapshots⟩
          | some application =>
              rw [runtime.application.includePending_accept execution.native id message
                application hlookup hhandle]
              have hprepared := handle_prepared runtime execution.native.application
                application message hhandle
              constructor
              · simpa only [hprepared] using hmessages.includePending id
              · exact handle_snapshots runtime owner valid execution.native.application
                  application message hsnapshots hmessage hhandle
  | wait =>
      simp only [EnvironmentPolicyCommand.toAction, FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact ⟨hmessages, hsnapshots⟩
  | application applicationCommand =>
      cases applicationCommand with
      | advance clock =>
          have heq : next.native = { execution.native with application :=
              { execution.native.application with
                base := execution.native.application.base.advance clock } } := by
            simpa [EnvironmentPolicyCommand.toAction, MessageApplication.step,
              WindowedApplication.application, environmentStep] using hnative
          rw [heq]
          exact ⟨hmessages, hsnapshots⟩
      | sample address =>
          change next.native ∈
            ((runtime.environmentStep execution.native.application (.sample address)).map
              fun application => { execution.native with application }).support at hnative
          rw [FinDist.support_map] at hnative
          obtain ⟨application, happlication, heq⟩ := hnative
          rw [← heq]
          simp only [environmentStep, FinDist.support_map, Set.mem_image] at happlication
          obtain ⟨base, hbase, rfl⟩ := happlication
          change base ∈ ((runtime.image.application.withAdmission
            runtime.image.admitsMessage runtime.image.admitsEnvironment).environmentStep
              execution.native.application.base (.sample address)).support at hbase
          rcases runtime.image.application.withAdmission_environment_support
              runtime.image.admitsMessage runtime.image.admitsEnvironment
              execution.native.application.base base (.sample address) hbase with rfl | hsample
          · exact ⟨hmessages, hsnapshots⟩
          · rcases runtime.image.sample_support execution.native.application.base
                address base hsample with rfl | hsampled
            · exact ⟨hmessages, hsnapshots⟩
            · obtain ⟨code, reads, value, _, _, _, _, _, rfl⟩ := hsampled
              exact ⟨hmessages, hsnapshots⟩

/-- On an actual activation-windowed run, an owner's binding submissions that
name already registered values yield accepted bindings with those exact frozen
snapshots. Environment behavior and other player policies are unrestricted,
including clock advances and genuine expiry traffic. -/
theorem runPolicies_registeredBindings_of_registered_submissions
    (runtime : WindowedApplication P L) (memory : ApplicationImage.Memory P L)
    (hempty : ∀ field, memory.accepted field = none)
    (owner : P) (valid : Nat → TypedValue L → Prop)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (hbinding : ∀ history view address handle,
      .submit (.binding address handle) ∈ (players owner history view).support →
        handle.1 = owner ∧ ∃ value,
          runtime.image.registrationCache handle.2
            (history.map fun entry => show runtime.image.application.PlayerEntry from
              runtime.erasePlayerEntry entry) = some value ∧ valid handle.2 value)
    (schedule : List (@Invocation P)) (next : runtime.application.PolicyExecution)
    (hnext : next ∈ (runtime.application.runPolicies players environment schedule
      (PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (runtime.initial (ApplicationImage.State.initial memory))))).support) :
    runtime.image.RegisteredBindings owner valid
      ((next.principalHistory owner).map fun entry =>
        show runtime.image.application.PlayerEntry from runtime.erasePlayerEntry entry)
      next.native.application.base := by
  let invariant (execution : runtime.application.PolicyExecution) :=
    RegistrationConsistent runtime execution ∧
      execution.native.pool.Satisfies (ApplicationImage.PreparedMessage owner valid
        execution.native.application.base.prepared) ∧
      ApplicationImage.PreparedSnapshots owner valid execution.native.application.base
  have hinvariant : invariant next := by
    apply runtime.application.runPolicies_execution_invariant invariant players environment
      ?_ ?_ schedule _ next ?_ hnext
    · intro execution who command final hstate hcommand hfinal
      have hprovenance := playerStep_provenance runtime owner valid execution final who command
        hstate.2.1 hstate.2.2 ?_ hfinal
      · exact ⟨playerStep_registrationConsistent runtime execution final who command
            hstate.1 hfinal, hprovenance⟩
      · intro payload hsubmit howner address handle hpayload
        change who = owner at howner
        subst who
        subst command
        change payload = .binding address handle at hpayload
        subst payload
        obtain ⟨hhandle, value, hcache, hvalid⟩ := hbinding _ _ address handle hcommand
        refine ⟨value, ?_, hvalid⟩
        have heq : handle = (owner, handle.2) := Prod.ext hhandle rfl
        rw [heq, ← hstate.1 owner handle.2]
        exact hcache
    · intro execution command final hstate _ hfinal
      have hprovenance := environmentStep_provenance runtime owner valid execution final
        command hstate.2.1 hstate.2.2 hfinal
      exact ⟨environmentStep_registrationConsistent runtime execution final command
          hstate.1 hfinal, hprovenance⟩
    · constructor
      · intro who slot
        rfl
      · exact ⟨MessagePool.Satisfies.empty, fun field handle haccepted _ => by
          simp only [PolicyExecution.initial, MessageApplication.State.initial,
            initial, ApplicationImage.State.initial, hempty] at haccepted
          contradiction⟩
  intro field handle haccepted howner
  obtain ⟨value, hprepared, hfrozen, hvalid⟩ :=
    hinvariant.2.2 field handle haccepted howner
  refine ⟨value, ?_, hfrozen, hvalid⟩
  rw [hinvariant.1 owner handle.2]
  have heq : handle = (owner, handle.2) := Prod.ext howner rfl
  exact (congrArg (fun reference => next.native.application.base.prepared.lookup reference)
    heq).symm.trans hprepared

/-- Arbitrary player and environment policies preserve the correspondence
between private registration history and write-once preparation. -/
theorem runPolicies_registrationConsistent
    (runtime : WindowedApplication P L)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (execution next : runtime.application.PolicyExecution)
    (hconsistent : runtime.RegistrationConsistent execution)
    (hnext : next ∈
      (runtime.application.runPolicies players environment schedule execution).support) :
    runtime.RegistrationConsistent next := by
  apply runtime.application.runPolicies_execution_invariant
    runtime.RegistrationConsistent players environment ?_ ?_ schedule execution next
      hconsistent hnext
  · intro current actor command final hcurrent _ hstep
    exact playerStep_registrationConsistent runtime current final actor command hcurrent hstep
  · intro current command final hcurrent _ hstep
    exact environmentStep_registrationConsistent runtime current final command hcurrent hstep

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.runPolicies_registrationConsistent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_registrationConsistent
