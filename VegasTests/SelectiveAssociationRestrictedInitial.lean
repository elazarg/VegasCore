/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestrictedRealization

/-! # Initialized execution of the restricted prescribed profile

The execution laws below concern the complete raw response game. They evaluate
the prescribed profile from its actual initial state; they do not assert
sequential rationality at other information sets.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def granted (execution : app.Execution) (event : nativeGraph.EventId) : app.Execution :=
  { execution with
    application := { execution.application with serviceGrant := some event }
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .application (.grant event)⟩] }

theorem grant_step (execution : app.Execution) (event : nativeGraph.EventId) :
    nativeRuntime.interactionStep leaks policy network (.grant event) execution =
      FinDist.pure (granted execution event) := by
  simp [interactionStep, interactionInstruction, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, app, serviceApp, reactiveApplication,
    environmentStep,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume, FinDist.map_pure, granted]

theorem player_step (execution : app.Execution) (who : Player) (action : app.Action)
    (selected : response who ((activate execution who).observe app who) = action) :
    nativeRuntime.interactionStep leaks policy network (.player who) execution =
      FinDist.pure ((activate execution who).respond app who action) := by
  simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
    ReactiveApplication.dispatch, activation_law, FinDist.pure_bind,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume, ReactiveApplication.invoke,
    policy, selected, FinDist.map_pure]

def quietPrelude : app.Execution :=
  (activate ((activate initial alice).respond app alice ⟨none⟩) bob).respond app bob ⟨none⟩

theorem prelude_law :
    nativeRuntime.runInteractionPlan leaks policy network [.player alice, .player bob] initial =
      FinDist.pure quietPrelude := by
  rw [runInteractionPlan, player_step initial alice ⟨none⟩ rfl, FinDist.pure_bind,
    runInteractionPlan, player_step _ bob ⟨none⟩ rfl, FinDist.pure_bind]
  rfl

def aliceReady : app.Execution := activate (granted quietPrelude aliceBinding) alice

def aliceSent : app.Execution :=
  aliceReady.respond app alice (bindingResponse alice aliceBinding 0 false)

def aliceIncluded : app.Execution :=
  { aliceSent.includePending app (alice, 0) with
    environmentRecall := aliceSent.environmentRecall ++
      [⟨aliceSent.observeEnvironment app, .include (alice, 0)⟩] }

private theorem alice_choice : response alice (aliceReady.observe app alice) =
    bindingResponse alice aliceBinding 0 false := by
  change correctiveBinding alice aliceBinding false (aliceReady.observe app alice) = _
  have fresh : (aliceReady.observe app alice).application.candidates (.prepared 0) = .fresh := rfl
  simp only [correctiveBinding, freshSlot, fresh, ↓reduceIte]

private theorem alice_selected : nativeRuntime.reactiveLatest leaks aliceBinding alice
    (aliceSent.observeEnvironment app) = .include (alice, 0) := by
  rfl

private theorem alice_inclusion :
    nativeRuntime.interactionStep leaks policy network (.includeLatest aliceBinding alice)
      aliceSent = FinDist.pure aliceIncluded := by
  simp only [interactionStep, interactionInstruction, alice_selected, FinDist.pure_bind,
    ReactiveApplication.dispatch, ReactiveApplication.Command.actor?, ReactiveApplication.resume,
    ReactiveApplication.Execution.environmentStep, FinDist.map_pure, FinDist.pure_bind]
  rfl

theorem initial_five_rounds :
    nativeRuntime.runInteractionPlan leaks policy network (nativePlan.take 5) initial =
      FinDist.pure aliceIncluded := by
  change nativeRuntime.runInteractionPlan leaks policy network
    ([.player alice, .player bob] ++ [.grant aliceBinding, .player alice,
      .includeLatest aliceBinding alice]) initial = _
  rw [runInteractionPlan_append, prelude_law, FinDist.pure_bind,
    runInteractionPlan, grant_step, FinDist.pure_bind,
    runInteractionPlan, player_step _ alice _ alice_choice, FinDist.pure_bind]
  change nativeRuntime.runInteractionPlan leaks policy network
    [.includeLatest aliceBinding alice] aliceSent = _
  rw [runInteractionPlan, alice_inclusion, FinDist.pure_bind]
  rfl

theorem initial_alice_binding :
    aliceBindingRef.get? aliceIncluded.application.config.store = some (.success false) := by
  have realized := binding_realizes policy aliceReady alice 0 false
    (by
      exact (State.initial_bindingInvariant nativeInputs).copy rfl rfl rfl)
    (by
      change MessageNetwork.empty.SerialsBeforeNext
      exact MessageNetwork.SerialsBeforeNext.empty)
    (by rfl) (by decide) (by change 0 < 1; decide)
  obtain ⟨next, stored, law⟩ := realized
  change (nativeRuntime.interactionStep leaks policy network
    (.includeLatest aliceBinding alice) aliceSent).map _ = _ at law
  rw [alice_inclusion, FinDist.map_pure] at law
  have same : aliceIncluded.application = next :=
    FinDist.mem_support_pure.mp (law ▸ FinDist.mem_support_pure.mpr rfl)
  rw [same]
  exact stored

theorem initial_no_public_certificate (who : Player) :
    (nativeRuntime.packetEvidence leaks).observe (aliceIncluded.observe app who) = [] := by
  rfl

end VegasTests.SelectiveAssociation.Restricted
