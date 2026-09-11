/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockSourceCoupling

/-! # Source witnesses at the first resolving environment action

The source constructor supplies the successful-handler law. The service
supplies non-sampling and resolved-suffix laws on its actual environment
coordinates. Player commands and the schedule otherwise remain unrestricted.
-/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A non-sampling environment action can resolve an active instruction only
by accepting a pending message. Delivery, waiting, and clock advancement do
not resolve it; malformed or rejected submissions produce no source step. -/
theorem environmentPolicyStep_source_witness
    (runtime : WindowedApplication P L)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.EnvironmentPolicyCommand) (address : Nat)
    {G : Graph P L} (Witness : Type) (target : Witness → Config G)
    (Certificate : WindowedApplication.State P L → Witness → Prop)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some address)
    (hinactive : runtime.image.activeAddress? next.native.application.base.memory ≠
      some address)
    (hnosample : ∀ sampled, command ≠ .application (.sample sampled))
    (resolve : ∀ message resolved,
      runtime.handle execution.native.application message = some resolved →
      ∃ witness, resolved.base.Refines (target witness) ∧ resolved.FreshActivation ∧
        Certificate resolved witness)
    (hnext : next ∈ (runtime.application.environmentPolicyStep execution command).support) :
    ∃ witness, next.native.application.base.Refines (target witness) ∧
      next.native.application.FreshActivation ∧ Certificate next.native.application witness := by
  cases command with
  | wait | deliver who id =>
      simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
        EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind,
        FinDist.mem_support_pure] at hnext
      subst next
      exact False.elim (hinactive hactive)
  | application command =>
      cases command with
      | sample sampled => exact False.elim (hnosample sampled rfl)
      | advance clock =>
          simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
            EnvironmentPolicyCommand.toAction, MessageApplication.step, application_advance,
            FinDist.map_pure, FinDist.pure_bind, FinDist.mem_support_pure] at hnext
          subst next
          apply False.elim
          apply hinactive
          simpa [ApplicationImage.State.advance, ApplicationImage.activeAddress?] using hactive
  | «include» id =>
      simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
        EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind,
        FinDist.mem_support_pure] at hnext
      subst next
      cases hlookup : execution.native.pool.lookup id with
      | none =>
          rw [runtime.application.includePending_missing execution.native id hlookup] at hinactive
          exact False.elim (hinactive hactive)
      | some message =>
          cases hhandle : runtime.handle execution.native.application message with
          | none =>
              rw [runtime.application.includePending_reject execution.native id message
                hlookup hhandle] at hinactive
              exact False.elim (hinactive hactive)
          | some resolved =>
              obtain ⟨witness, hrefines, hfresh, hcertificate⟩ := resolve message resolved hhandle
              have haccepted := runtime.application.includePending_accept execution.native id
                message resolved hlookup hhandle
              exact ⟨witness, haccepted ▸ hrefines, haccepted ▸ hfresh,
                haccepted ▸ hcertificate⟩

/-- Any scheduled segment that resolves its initial head carries the source
witness of its first successful handler. The same induction applies to normal
service, delivery/reaction phases, and relay suffixes. Progress is a separate
obligation: the final inactive premise must be proved by the selected service. -/
theorem runPolicies_head_source_witness
    (runtime : WindowedApplication P L)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@Invocation P)) (AtEnvironment : Nat → Prop)
    (address : Nat) {G : Graph P L} (cfg : Config G)
    (execution final : runtime.application.PolicyExecution) (activation : Activation Nat)
    (Witness : Type) (target : Witness → Config G)
    (Certificate : WindowedApplication.State P L → Witness → Prop)
    (hindex : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length + schedule.countP Invocation.isEnvironment →
      AtEnvironment index)
    (hnosample : ∀ (current : runtime.application.PolicyExecution) command,
      AtEnvironment current.environmentHistory.length →
      command ∈ (environment current.environmentHistory
        (State.environmentView runtime.application current.native)).support →
      ∀ sampled, command ≠ .application (.sample sampled))
    (resolve : ∀ current message resolved,
      current.active = some activation → current.base.Refines cfg →
      runtime.handle current message = some resolved →
      ∃ witness, resolved.base.Refines (target witness) ∧ resolved.FreshActivation ∧
        Certificate resolved witness)
    (preserve : ∀ witness before after suffix,
      (∀ index, before.environmentHistory.length ≤ index →
        index < before.environmentHistory.length + suffix.countP Invocation.isEnvironment →
        AtEnvironment index) →
      runtime.image.activeAddress? before.native.application.base.memory ≠ some address →
      before.native.application.base.Refines (target witness) →
      before.native.application.FreshActivation → Certificate before.native.application witness →
      after ∈ (runtime.application.runPolicies players environment suffix before).support →
      after.native.application.base.Refines (target witness) ∧
        after.native.application.FreshActivation ∧ Certificate after.native.application witness)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some address)
    (hactivation : execution.native.application.active = some activation)
    (hrefines : execution.native.application.base.Refines cfg)
    (hinactive : runtime.image.activeAddress? final.native.application.base.memory ≠ some address)
    (hfinal : final ∈
      (runtime.application.runPolicies players environment schedule execution).support) :
    ∃ witness, final.native.application.base.Refines (target witness) ∧
      final.native.application.FreshActivation ∧ Certificate final.native.application witness := by
  induction schedule generalizing execution with
  | nil =>
      simp only [MessageApplication.runPolicies, FinDist.mem_support_pure] at hfinal
      subst final
      exact False.elim (hinactive hactive)
  | cons invocation rest ih =>
      simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion] at hfinal
      obtain ⟨middle, hmiddle, hrest⟩ := hfinal
      have hlength := runtime.application.runPolicies_environmentHistory_length players environment
        [invocation] execution middle (by
          simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hmiddle)
      have hrestIndex : ∀ index, middle.environmentHistory.length ≤ index →
          index < middle.environmentHistory.length + rest.countP Invocation.isEnvironment →
          AtEnvironment index := by
        intro index hlo hhi
        apply hindex index
        · omega
        · simp only [List.countP_cons, List.countP_nil] at hlength ⊢
          omega
      cases invocation with
      | player who =>
          simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, _, hstep⟩ := hmiddle
          have hpublic := runtime.playerStep_publicState who execution middle command hstep
          have hmemory := congrArg Prod.fst hpublic
          change middle.native.application.base.memory =
            execution.native.application.base.memory at hmemory
          have hactiveMiddle : runtime.image.activeAddress?
              middle.native.application.base.memory = some address := by
            rw [hmemory]
            exact hactive
          exact ih middle hrestIndex hactiveMiddle ((congrArg Prod.snd hpublic).trans hactivation)
            (runtime.playerStep_refines who execution middle command cfg hrefines hstep).1 hrest
      | environment =>
          simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, hcommand, hstep⟩ := hmiddle
          have hnotSample := hnosample execution command
            (hindex _ (Nat.le_refl _) (by simp [Invocation.isEnvironment])) hcommand
          by_cases hmiddleActive : runtime.image.activeAddress?
              middle.native.application.base.memory = some address
          · obtain ⟨hmiddleRefines, hmiddleActivation, _⟩ :=
              runtime.environmentPolicyStep_refines_of_active execution middle command address cfg
                hrefines hactive hmiddleActive hnotSample hstep
            exact ih middle hrestIndex hmiddleActive (hmiddleActivation.trans hactivation)
              hmiddleRefines hrest
          · obtain ⟨witness, hresolved, hfresh, hcertificate⟩ :=
              runtime.environmentPolicyStep_source_witness execution middle command address
                Witness target Certificate hactive hmiddleActive hnotSample
                (fun message resolved hhandle =>
                  resolve execution.native.application message resolved hactivation
                    hrefines hhandle)
                hstep
            exact ⟨witness, preserve witness middle final rest hrestIndex hmiddleActive
              hresolved hfresh hcertificate hrest⟩

end Vegas.WindowedApplication
