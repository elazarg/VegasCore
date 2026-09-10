/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedController
import Interaction.SealedApplicationHiding
import Interaction.MessageApplicationPolicyTrace

/-! # Receipt-bearing hiding through a public release boundary

Protected-owner invocations are permitted. Before release, the specified
policy waits; afterward, execution continues and may disclose the value.
The compared law reads the first release-enabled snapshot of each complete
shared invocation trace, or its final snapshot if release never becomes enabled.
Public acceptance/rejection receipts and unrestricted replay remain observable.
-/

noncomputable section

namespace Interaction.SealedProgram

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

def WaitsBeforeRelease (program : SealedProgram Principal)
    (policy : (program.messageApplication (Value := Value)).PlayerPolicy)
    (release : List (Event Principal Value) → Bool) : Prop :=
  ∀ history view, release view.application = false →
    policy history view = FinDist.pure .wait

theorem openingPolicy_waitsBefore (program : SealedProgram Principal)
    (owner : Principal) (node : Nat) (value : Value) :
    WaitsBeforeRelease program (openingPolicy program owner node value)
      (fun events => (openingHandle? program events owner node).isSome) := by
  intro history view hrelease
  have hnone : openingHandle? program view.application owner node = none := by
    cases hhandle : openingHandle? program view.application owner node with
    | none => rfl
    | some handle => simp [hhandle] at hrelease
  simp [openingPolicy, openingCommand, openingRequest?, hnone]

private theorem ApplicationPolicyRelated.owner_wait
    {program : SealedProgram Principal} {hiddenOwner : Principal}
    {left right : (program.messageApplication (Value := Value)).PolicyExecution}
    (related : ApplicationPolicyRelated program hiddenOwner left right) :
    ∃ nextLeft nextRight,
      (program.messageApplication).playerStep hiddenOwner left .wait = FinDist.pure nextLeft ∧
      (program.messageApplication).playerStep hiddenOwner right .wait = FinDist.pure nextRight ∧
      ApplicationPolicyRelated program hiddenOwner nextLeft nextRight := by
  refine ⟨_, _, MessageApplication.playerStep_wait _ _ _,
    MessageApplication.playerStep_wait _ _ _, related.native, ?_, related.environmentHistory⟩
  intro who hne
  simp only [if_neg hne]
  exact related.principalHistory who hne

/-- Any relation-invariant readout has the same law at the first public
release boundary. Both complete traces execute, including their suffixes.
The protected policies may differ, but must wait before release; all other
player policies and the environment are unchanged. -/
theorem tracePolicies_release_readout_congr
    (program : SealedProgram Principal) (hiddenOwner : Principal)
    (first second : Principal → (program.messageApplication (Value := Value)).PlayerPolicy)
    (environment : (program.messageApplication (Value := Value)).EnvironmentPolicy)
    (release : List (Event Principal Value) → Bool)
    (hplayers : ∀ who, who ≠ hiddenOwner → first who = second who)
    (hfirst : WaitsBeforeRelease program (first hiddenOwner) release)
    (hsecond : WaitsBeforeRelease program (second hiddenOwner) release)
    (schedule : List (@MessageApplication.Invocation Principal))
    {Result : Type*}
    (readout : (program.messageApplication (Value := Value)).PolicyExecution → Result)
    (hreadout : ∀ {left right}, ApplicationPolicyRelated program hiddenOwner left right →
      readout left = readout right)
    {left right : (program.messageApplication (Value := Value)).PolicyExecution}
    (related : ApplicationPolicyRelated program hiddenOwner left right) :
    (((program.messageApplication).tracePolicies first environment schedule left).map
        (MessageApplication.PolicyTrace.firstRelease
          (fun (execution : (program.messageApplication (Value := Value)).PolicyExecution) =>
            release execution.native.application.events))).map readout =
      (((program.messageApplication).tracePolicies second environment schedule right).map
        (MessageApplication.PolicyTrace.firstRelease
          (fun (execution : (program.messageApplication (Value := Value)).PolicyExecution) =>
            release execution.native.application.events))).map readout := by
  induction schedule generalizing left right with
  | nil =>
      simp only [MessageApplication.tracePolicies, FinDist.map_pure,
        MessageApplication.PolicyTrace.firstRelease, hreadout related]
  | cons invocation rest ih =>
      rw [MessageApplication.tracePolicies_firstRelease_cons,
        MessageApplication.tracePolicies_firstRelease_cons]
      have hpublic : release left.native.application.events =
          release right.native.application.events := congrArg release related.native.native.events
      cases hrelease : release left.native.application.events with
      | true =>
          have hright := hpublic.symm.trans hrelease
          simp only [hright, ↓reduceIte, FinDist.map_pure, hreadout related]
      | false =>
          have hright := hpublic.symm.trans hrelease
          simp only [hright, Bool.false_eq_true, ↓reduceIte, FinDist.map_bind]
          cases invocation with
          | player who =>
              by_cases hwho : who = hiddenOwner
              · subst who
                rw [MessageApplication.invoke, MessageApplication.invoke,
                  hfirst _ _ hrelease, hsecond _ _ hright]
                obtain ⟨nextLeft, nextRight, hl, hr, hrelated⟩ := related.owner_wait
                simp only [FinDist.pure_bind, hl, hr]
                exact ih hrelated
              · simp only [MessageApplication.invoke, FinDist.bind_bind, hplayers who hwho,
                  related.principalHistory who hwho, related.native.observe_eq who]
                apply FinDist.bind_congr
                intro command _
                obtain ⟨nextLeft, nextRight, hl, hr, hrelated⟩ :=
                  related.playerStep who hwho command
                simp only [hl, hr, FinDist.pure_bind]
                exact ih hrelated
          | environment =>
              simp only [MessageApplication.invoke, FinDist.bind_bind,
                related.environmentHistory, related.native.environmentView_eq]
              apply FinDist.bind_congr
              intro command _
              obtain ⟨nextLeft, nextRight, hl, hr, hrelated⟩ := related.environmentStep command
              simp only [hl, hr, FinDist.pure_bind]
              exact ih hrelated

theorem tracePolicies_hiding_beforeRelease
    (program : SealedProgram Principal) (hiddenOwner : Principal)
    (first second : Principal → (program.messageApplication (Value := Value)).PlayerPolicy)
    (environment : (program.messageApplication (Value := Value)).EnvironmentPolicy)
    (release : List (Event Principal Value) → Bool)
    (hplayers : ∀ who, who ≠ hiddenOwner → first who = second who)
    (hfirst : WaitsBeforeRelease program (first hiddenOwner) release)
    (hsecond : WaitsBeforeRelease program (second hiddenOwner) release)
    (schedule : List (@MessageApplication.Invocation Principal))
    {left right : (program.messageApplication (Value := Value)).PolicyExecution}
    (related : ApplicationPolicyRelated program hiddenOwner left right) :
    (((program.messageApplication).tracePolicies first environment schedule left).map
        (MessageApplication.PolicyTrace.firstRelease
          (fun (execution : (program.messageApplication (Value := Value)).PolicyExecution) =>
            release execution.native.application.events))).map
        (program.applicationObservations hiddenOwner) =
      (((program.messageApplication).tracePolicies second environment schedule right).map
        (MessageApplication.PolicyTrace.firstRelease
          (fun (execution : (program.messageApplication (Value := Value)).PolicyExecution) =>
            release execution.native.application.events))).map
        (program.applicationObservations hiddenOwner) :=
  tracePolicies_release_readout_congr program hiddenOwner first second environment
    release hplayers hfirst hsecond schedule (program.applicationObservations hiddenOwner)
    (fun related => related.observations_eq) related

/-- info: 'Interaction.SealedProgram.tracePolicies_hiding_beforeRelease' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tracePolicies_hiding_beforeRelease

end Interaction.SealedProgram
