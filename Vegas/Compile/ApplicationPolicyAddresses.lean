/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPolicyCache
import Vegas.Compile.WindowedMessageOrigins

/-! # Address provenance of generated source policies -/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- With a certified completed prefix in the ambient image, every submission
supported by the generated policy for the remaining plan targets exactly the
currently active emitted instruction. -/
theorem liftProfileIn_submit_address
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ}
    (plan : ApplicationPlan accounted fresh state) (deadlineOf : Nat → Nat)
    (image : ApplicationImage P L) (profile : SourceBehavioralProfile prog)
    (before : List (ApplicationInstruction P L))
    (hinstructions : image.instructions = before ++ plan.instructions deadlineOf)
    (memory : ApplicationImage.Memory P L)
    (hbefore : ∀ instruction ∈ before, memory.done instruction.address = true)
    (player : P) (history : List image.application.PlayerEntry)
    (view : image.application.View) (hview : view.application = memory)
    (payload : ApplicationImage.Payload P L)
    (hcommand : .submit payload ∈
      (plan.liftProfileIn image deadlineOf profile player history view).support) :
    payload.address? = image.activeAddress? memory := by
  induction plan generalizing before player history view with
  | ret => simp [liftProfileIn] at hcommand
  | @sample Γ pending name ty dist tail accounted fresh state next ih =>
      simp only [liftProfileIn] at hcommand
      split at hcommand
      · rename_i hdone
        apply ih profile.afterSample
          (before ++ [.sample (ApplicationPlan.headSampleCode fresh state)])
        · simpa only [instructions, List.append_assoc, List.singleton_append] using hinstructions
        · intro instruction hinstruction
          simp only [List.mem_append, List.mem_singleton] at hinstruction
          rcases hinstruction with hold | rfl
          · exact hbefore instruction hold
          · rw [hview] at hdone
            simpa only [ApplicationInstruction.address, headSampleCode_node] using hdone
        · exact hview
        · exact hcommand
      · simp at hcommand
  | @binding Γ pending name owner ty guard tail newName accounted fresh state unrestricted next
      ih =>
      simp only [liftProfileIn] at hcommand
      split at hcommand
      · rename_i hdone
        apply ih profile.afterCommit (before ++ [(.bind
          ((SourceDecisionSite.here guard tail).bindingCode fresh state
            state.nextField))])
        · simpa only [instructions, List.append_assoc, List.singleton_append] using hinstructions
        · intro instruction hinstruction
          simp only [List.mem_append, List.mem_singleton] at hinstruction
          rcases hinstruction with hold | rfl
          · exact hbefore instruction hold
          · rw [hview] at hdone
            simpa [ApplicationInstruction.address, SourceDecisionSite.bindingCode,
              SourceDecisionSite.compiledNode, decisionSiteState] using hdone
        · exact hview
        · exact hcommand
      · rename_i hunresolved
        split at hcommand
        · rename_i howner
          subst player
          let site : SourceDecisionSite owner (.commit name owner guard tail) _ name _ guard :=
            .here guard tail
          have hsupported := site.bindingPolicy_supported_command fresh state image
            (profile owner site) history view (.submit payload)
            (by simpa [site] using hcommand)
          rcases hsupported with hwait | hregister | hsubmit
          · contradiction
          · rcases hregister with ⟨_, hfalse⟩
            contradiction
          · have hpayload : payload = .binding
                (site.bindingCode fresh state (site.compiledField fresh state)).node
                (owner, site.compiledField fresh state) := by
              injection hsubmit
            subst payload
            change _ = (ApplicationImage.mk image.instructions).activeAddress? memory
            rw [hinstructions, ApplicationImage.activeAddress?_after_completed before
              _ memory hbefore]
            change some (ApplicationInstruction.bind
              ((SourceDecisionSite.here guard tail).bindingCode fresh state
                state.nextField)).address = _
            apply (ApplicationImage.activeAddress?_head _ _ memory _).symm
            rw [← hview]
            simpa [ApplicationInstruction.address, site, SourceDecisionSite.bindingCode,
              SourceDecisionSite.compiledNode, decisionSiteState] using hunresolved
        · simp at hcommand
  | @publicChoice Γ pending name publicName owner ty guard tail newName unresolved accounted fresh
      state publicGuard next ih =>
      simp only [liftProfileIn] at hcommand
      split at hcommand
      · rename_i hdone
        apply ih profile.afterCommit.afterReveal
          (before ++ [(.publicChoice
            ((PublicChoiceSite.atHead name publicName owner guard tail).code fresh state))])
        · simpa only [instructions, List.append_assoc, List.singleton_append] using hinstructions
        · intro instruction hinstruction
          simp only [List.mem_append, List.mem_singleton] at hinstruction
          rcases hinstruction with hold | rfl
          · exact hbefore instruction hold
          · rw [hview] at hdone
            have haddress : (ApplicationInstruction.publicChoice
                (PublicChoiceSite.code
                  (PublicChoiceSite.atHead name publicName owner guard tail) fresh state)).address
                = state.nodes.length + 1 := rfl
            change memory.done (state.nodes.length + 1) = true
            exact hdone
        · exact hview
        · exact hcommand
      · rename_i hunresolved
        split at hcommand
        · rename_i howner
          subst player
          let site := PublicChoiceSite.atHead name publicName owner guard tail
          let controller := site.imageController fresh state image
            (image.ownerReadout? owner (site.compiledGuard fresh state).choiceReads)
            (profile owner site.decision) (fun _ _ => false)
          have hsupported := controller.supported_wait_or_encoded image.application history view
            (.submit payload) (by simpa [site, controller] using hcommand)
          rcases hsupported with hwait | ⟨value, hvalue⟩
          · contradiction
          · have hrecognized : ¬(ApplicationInstruction.publicChoice
                (site.code fresh state)).RejectsCommand
                image owner (.submit payload) := by
              rw [hvalue]
              intro hreject
              have hnone := hreject rfl
              change controller.codec.decode (controller.codec.encode value) = none at hnone
              rw [controller.codec.decode_encode] at hnone
              contradiction
            change _ = (ApplicationImage.mk image.instructions).activeAddress? memory
            rw [ApplicationInstruction.submission_address_of_not_rejects image
              (ApplicationInstruction.publicChoice (site.code fresh state))
              owner payload hrecognized, hinstructions,
              ApplicationImage.activeAddress?_after_completed before
                _ memory hbefore]
            apply (ApplicationImage.activeAddress?_head _ _ memory _).symm
            rw [← hview]
            have haddress : (ApplicationInstruction.publicChoice
                (site.code fresh state)).address = state.nodes.length + 1 := rfl
            rw [haddress]
            exact Bool.eq_false_of_not_eq_true hunresolved
        · simp at hcommand
  | @conditional Γ pending name publicName owner ty guard tail spec unresolved newName accounted
      fresh state publicGuard next ih =>
      simp only [liftProfileIn] at hcommand
      split at hcommand
      · rename_i hdone
        apply ih profile.afterCommit.afterReveal
          (before ++ [(.conditional
            ((ConditionalPublicationSite.atHead name publicName owner guard tail spec).code fresh
              state
              ((ConditionalPublicationSite.atHead name publicName owner guard tail spec).sourceField
                fresh state)
              (deadlineOf
                (PublicChoiceSite.publicationNode
                  (ConditionalPublicationSite.atHead name publicName owner guard tail spec).choice
                  fresh state))))])
        · simpa only [instructions, List.append_assoc, List.singleton_append] using hinstructions
        · intro instruction hinstruction
          simp only [List.mem_append, List.mem_singleton] at hinstruction
          rcases hinstruction with hold | rfl
          · exact hbefore instruction hold
          · rw [hview] at hdone
            have haddress : (ApplicationInstruction.conditional
                (ConditionalPublicationSite.code
                  (ConditionalPublicationSite.atHead name publicName owner guard tail spec)
                  fresh state
                  (ConditionalPublicationSite.sourceField
                    (ConditionalPublicationSite.atHead name publicName owner guard tail spec)
                    fresh state)
                  (deadlineOf (state.nodes.length + 1)))).address =
                state.nodes.length + 1 := rfl
            change memory.done (state.nodes.length + 1) = true
            exact hdone
        · exact hview
        · exact hcommand
      · rename_i hunresolved
        split at hcommand
        · rename_i howner
          subst player
          let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
          let sourceSlot := site.sourceField fresh state
          let deadline := deadlineOf (site.choice.publicationNode fresh state)
          let readout := image.ownerReadout? owner
            (site.choice.compiledGuard fresh state).choiceReads
          have hhead := conditionalPolicy_headCommand site fresh state sourceSlot deadline image
            readout (profile owner site.choice.decision) history view (.submit payload)
            (by simpa [site, sourceSlot, deadline, readout] using hcommand)
          rcases hhead with hwait | hrecognized
          · contradiction
          · change _ = (ApplicationImage.mk image.instructions).activeAddress? memory
            rw [ApplicationInstruction.submission_address_of_not_rejects image
                (ApplicationInstruction.conditional
                  (site.code fresh state sourceSlot deadline))
                owner payload hrecognized,
              hinstructions, ApplicationImage.activeAddress?_after_completed before
                _ memory hbefore]
            apply (ApplicationImage.activeAddress?_head _ _ memory _).symm
            rw [← hview]
            have haddress : (ApplicationInstruction.conditional
                (site.code fresh state sourceSlot deadline)).address =
                state.nodes.length + 1 := rfl
            rw [haddress]
            exact Bool.eq_false_of_not_eq_true hunresolved
        · simp at hcommand
  | @conditionalCopy Γ pending name publicName owner ty guard tail spec newName unresolved
      accounted fresh state publicGuard next ih =>
      simp only [liftProfileIn] at hcommand
      split at hcommand
      · rename_i hdone
        apply ih profile.afterCommit.afterReveal
          (before ++ [(.conditional
            ((ConditionalPublicationSite.atHead name publicName owner guard tail spec).code fresh
              state
              ((ConditionalPublicationSite.atHead name publicName owner guard tail spec).sourceField
                fresh state)
              (deadlineOf
                (PublicChoiceSite.publicationNode
                  (ConditionalPublicationSite.atHead name publicName owner guard tail spec).choice
                  fresh state))))])
        · simpa only [instructions, List.append_assoc, List.singleton_append] using hinstructions
        · intro instruction hinstruction
          simp only [List.mem_append, List.mem_singleton] at hinstruction
          rcases hinstruction with hold | rfl
          · exact hbefore instruction hold
          · rw [hview] at hdone
            have haddress : (ApplicationInstruction.conditional
                (ConditionalPublicationSite.code
                  (ConditionalPublicationSite.atHead name publicName owner guard tail spec)
                  fresh state
                  (ConditionalPublicationSite.sourceField
                    (ConditionalPublicationSite.atHead name publicName owner guard tail spec)
                    fresh state)
                  (deadlineOf (state.nodes.length + 1)))).address =
                state.nodes.length + 1 := rfl
            change memory.done (state.nodes.length + 1) = true
            exact hdone
        · exact hview
        · exact hcommand
      · rename_i hunresolved
        split at hcommand
        · rename_i howner
          subst player
          let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
          let sourceSlot := site.sourceField fresh state
          let deadline := deadlineOf (site.choice.publicationNode fresh state)
          let readout := image.ownerReadout? owner
            (site.choice.compiledGuard fresh state).choiceReads
          have hhead := conditionalPolicy_headCommand site fresh state sourceSlot deadline image
            readout (profile owner site.choice.decision) history view (.submit payload)
            (by simpa [site, sourceSlot, deadline, readout] using hcommand)
          rcases hhead with hwait | hrecognized
          · contradiction
          · change _ = (ApplicationImage.mk image.instructions).activeAddress? memory
            rw [ApplicationInstruction.submission_address_of_not_rejects image
                (ApplicationInstruction.conditional
                  (site.code fresh state sourceSlot deadline))
                owner payload hrecognized,
              hinstructions, ApplicationImage.activeAddress?_after_completed before
                _ memory hbefore]
            apply (ApplicationImage.activeAddress?_head _ _ memory _).symm
            rw [← hview]
            have haddress : (ApplicationInstruction.conditional
                (site.code fresh state sourceSlot deadline)).address =
                state.nodes.length + 1 := rfl
            rw [haddress]
            exact Bool.eq_false_of_not_eq_true hunresolved
        · simp at hcommand

end Vegas.ApplicationPlan
