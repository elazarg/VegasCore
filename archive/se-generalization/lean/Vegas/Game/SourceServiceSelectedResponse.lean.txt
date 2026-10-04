/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingSelectedInput

/-! # The actual lottery at the selected owned input

The same early-stop evaluator, with the owner silent, retains the original
before-response execution at a selected hit. Removing its last silent own
recall entry recovers that execution. Replacing exactly that response by the
canonical opportunity gives the selected family's whole stopped execution
law. Completion before a selected input stays on the actual reference path.

This identity concerns the literal timing family, including its closed-gate
silence. It makes no rationality or source-admission claim at late inputs.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private def selectedBeforeResponse (owner : Player)
    (execution : (application setup leaks).Execution) :
    (application setup leaks).Execution :=
  { execution with
    «recall» := Function.update execution.recall owner (execution.recall owner).dropLast }

/-- Removing the last own recall entry from an actual silent response recovers
its unchanged before-response execution. -/
theorem sourceService_silent_response_dropLast (owner : Player)
    (execution : (application setup leaks).Execution) :
    let after := execution.respond (application setup leaks) owner ⟨none⟩
    { after with
      «recall» := Function.update after.recall owner (after.recall owner).dropLast } =
      execution := by
  change selectedBeforeResponse owner
    (execution.respond (application setup leaks) owner ⟨none⟩) = execution
  cases execution
  dsimp only [selectedBeforeResponse, ReactiveApplication.Execution.respond]
  congr 1
  funext actor
  by_cases own : actor = owner
  · subst actor
    simp only [Function.update_self, ↓reduceIte, List.dropLast_concat]
  · simp only [Function.update_of_ne own, ite_eq_right own]

/-- The selected-family stop is the actual owner-silent stop followed, only
at its selected input, by that input's actual canonical response lottery.
The before-response execution is read from the last silent recall entry;
the chosen response is neither conditioned on support nor drawn twice. -/
theorem sourceService_selected_response_law
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (bound : (graph setup).EventId → Nat) (profile : BehavioralProfile setup.program)
    (owner : Player) (event : (graph setup).EventId) (turns : Nat) (slot : Fin (turns + 1))
    (count : Nat) (execution : (application setup leaks).Execution)
    (absent : sourceServiceSelectedInput? setup leaks owner event slot.val
      (execution.recall owner) = none) :
    let app := application setup leaks
    let familyPlayers := Function.update players owner
      (sourceServiceTurnFamily setup leaks bound profile owner event turns slot)
    let silentPlayers := Function.update players owner app.silentPolicy
    let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed ∨
      sourceServiceSelectedInput? setup leaks owner event slot.val (final.recall owner) ≠ none
    app.runUntil scheduler familyPlayers stop count execution =
      (app.runUntil scheduler silentPlayers stop count execution).bind fun final =>
        if sourceServiceSelectedInput? setup leaks owner event slot.val (final.recall owner) =
            none then PMF.pure final
        else
          let before := { final with
            «recall» := Function.update final.recall owner (final.recall owner).dropLast }
          (sourceServiceCanonicalOpportunity setup leaks bound profile owner event
            (before.recall owner) (before.observe app owner)).map (before.respond app owner) := by
  classical
  dsimp only
  let app := application setup leaks
  let familyPlayers := Function.update players owner
    (sourceServiceTurnFamily setup leaks bound profile owner event turns slot)
  let silentPlayers := Function.update players owner app.silentPolicy
  let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed ∨
    sourceServiceSelectedInput? setup leaks owner event slot.val (final.recall owner) ≠ none
  let selected := fun final : app.Execution =>
    if sourceServiceSelectedInput? setup leaks owner event slot.val (final.recall owner) = none
      then PMF.pure final
    else
      let before := selectedBeforeResponse owner final
      (sourceServiceCanonicalOpportunity setup leaks bound profile owner event
        (before.recall owner) (before.observe app owner)).map (before.respond app owner)
  change app.runUntil scheduler familyPlayers stop count execution =
    (app.runUntil scheduler silentPlayers stop count execution).bind selected
  induction count generalizing execution with
  | zero =>
      simp only [ReactiveApplication.runUntil, PMF.pure_bind, selected, absent, ↓reduceIte]
  | succ count ih =>
      by_cases halt : stop execution
      · rw [app.runUntil_of_stop scheduler familyPlayers stop _ execution halt,
          app.runUntil_of_stop scheduler silentPlayers stop _ execution halt, PMF.pure_bind]
        simp only [selected, absent, ↓reduceIte]
      · simp only [ReactiveApplication.runUntil, halt, ↓reduceIte, ReactiveApplication.round,
          ReactiveApplication.dispatch, PMF.bind_bind]
        apply bind_congr_on_support _
        intro command _chosen
        apply bind_congr_on_support _
        intro middle moved
        have middleAbsent : sourceServiceSelectedInput? setup leaks owner event slot.val
            (middle.recall owner) = none := by
          rw [app.environmentStep_recall execution middle command moved]
          exact absent
        cases command with
        | activate actor =>
            simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
              ReactiveApplication.invoke, PMF.bind_map, Function.comp_def]
            by_cases own : actor = owner
            · subst actor
              by_cases current : sourceServiceTurn setup leaks owner event (middle.recall owner)
                  (middle.observe app owner) = some slot.val
              · have responseStopped (response : app.Action) :
                    app.runUntil scheduler familyPlayers stop count
                      (middle.respond app owner response) =
                      PMF.pure (middle.respond app owner response) := by
                  apply app.runUntil_of_stop
                  right
                  rw [sourceServiceSelectedInput?_respond owner event slot.val middle
                    middleAbsent response, ite_eq_left current]
                  exact Option.some_ne_none _
                have silentReadout := sourceServiceSelectedInput?_respond owner event slot.val
                  middle middleAbsent ⟨none⟩
                rw [ite_eq_left current] at silentReadout
                have silentStopped : app.runUntil scheduler silentPlayers stop count
                    (middle.respond app owner ⟨none⟩) =
                    PMF.pure (middle.respond app owner ⟨none⟩) := by
                  apply app.runUntil_of_stop
                  right
                  rw [silentReadout]
                  exact Option.some_ne_none _
                have familyLaw : familyPlayers owner (middle.recall owner)
                    (middle.observe app owner) =
                    sourceServiceCanonicalOpportunity setup leaks bound profile owner event
                      (middle.recall owner) (middle.observe app owner) := by
                  dsimp only [familyPlayers]
                  rw [Function.update_self]
                  unfold sourceServiceTurnFamily
                  exact app.turnScheduledPolicy_selected _ slot _ _ _ _ current
                have silentLaw : silentPlayers owner (middle.recall owner)
                    (middle.observe app owner) = PMF.pure ⟨none⟩ := by
                  simp only [silentPlayers, Function.update_self,
                    ReactiveApplication.silentPolicy_apply]
                rw [familyLaw, silentLaw, PMF.pure_bind, silentStopped, PMF.pure_bind]
                simp_rw [responseStopped]
                change (sourceServiceCanonicalOpportunity setup leaks bound profile owner event
                    (middle.recall owner) (middle.observe app owner)).map
                    (middle.respond app owner) = selected (middle.respond app owner ⟨none⟩)
                have present : sourceServiceSelectedInput? setup leaks owner event slot.val
                    ((middle.respond app owner ⟨none⟩).recall owner) ≠ none := by
                  rw [silentReadout]
                  exact Option.some_ne_none _
                dsimp only [selected]
                rw [ite_eq_right present]
                exact congrArg (fun before : app.Execution =>
                  (sourceServiceCanonicalOpportunity setup leaks bound profile owner event
                    (before.recall owner) (before.observe app owner)).map
                      (before.respond app owner))
                  (sourceService_silent_response_dropLast owner middle).symm
              · have familyLaw : familyPlayers owner (middle.recall owner)
                      (middle.observe app owner) = PMF.pure ⟨none⟩ := by
                  dsimp only [familyPlayers]
                  rw [Function.update_self]
                  have silent : sourceServiceTurnFamily setup leaks bound profile owner event
                      turns slot (middle.recall owner) (middle.observe app owner) =
                      app.silentPolicy (middle.recall owner) (middle.observe app owner) := by
                    apply app.turnScheduledPolicy_unselected
                    intro other equal
                    cases Option.some.inj equal
                    exact current
                  exact silent
                have silentLaw : silentPlayers owner (middle.recall owner)
                    (middle.observe app owner) = PMF.pure ⟨none⟩ := by
                  simp only [silentPlayers, Function.update_self,
                    ReactiveApplication.silentPolicy_apply]
                rw [familyLaw, silentLaw, PMF.pure_bind, PMF.pure_bind]
                apply ih
                rw [sourceServiceSelectedInput?_respond owner event slot.val middle middleAbsent
                  ⟨none⟩, ite_eq_right current]
            · have familyForeign : familyPlayers actor = players actor :=
                Function.update_of_ne own _ _
              have silentForeign : silentPlayers actor = players actor :=
                Function.update_of_ne own _ _
              rw [familyForeign, silentForeign]
              apply bind_congr_on_support _
              intro response _supported
              apply ih
              rw [app.respond_recall_other middle actor owner (Ne.symm own) response]
              exact middleAbsent
        | «include» _ | application _ | wait =>
            simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
              PMF.pure_bind]
            exact ih middle middleAbsent

end Vegas
