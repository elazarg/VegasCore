/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveEvidence
import Interaction.ReactiveResponseMenu
import GameTheoryExtensions.Protocol.Knowledge

/-! # Receipt evidence constrains every compatible native history -/

noncomputable section

namespace Interaction.ReactiveApplication.ReceiptEvidence

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (evidence : app.ReceiptEvidence)

theorem knows_observed (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (who : Principal) (past : List app.PlayerEntry) (view : app.PlayerView)
    (fact : evidence.Fact) (observed : fact ∈ evidence.observe view) :
    (app.information initial horizon scheduler).Knows who (some (past, view))
      (fun history => stateInvariant (fun state => evidence.valid state fact) history.state) := by
  rintro ⟨⟨state, trace⟩, equal⟩
  change (app.signals initial horizon scheduler).infoOf who trace = some (past, view) at equal
  rw [app.info] at equal
  cases state with
  | none => cases equal
  | some control =>
      change (if control.actor = some who then
        some (control.execution.recall who, control.execution.observe app who)
        else none) = some (past, view) at equal
      split at equal
      · have sameView := congrArg Prod.snd (Option.some.inj equal)
        change control.execution.observe app who = view at sameView
        apply evidence.observed_valid control.execution who
          (evidence.history_sound initial horizon scheduler trace) fact
        exact sameView.symm ▸ observed
      · cases equal

/-- Restricting responses does not weaken receipt knowledge. This applies
to arbitrary observation-local menus, including malformed traffic and replay. -/
theorem knows_observed_menu (menu : app.ResponseMenu) (initial : FinDist app.State)
    (horizon : Nat) (scheduler : app.Scheduler)
    (who : Principal) (past : List app.PlayerEntry) (view : app.PlayerView)
    (fact : evidence.Fact) (observed : fact ∈ evidence.observe view) :
    (menu.information initial horizon scheduler).Knows who (some (past, view))
      (fun history => stateInvariant (fun state => evidence.valid state fact) history.state) := by
  rintro ⟨⟨state, trace⟩, equal⟩
  change (menu.signals initial horizon scheduler).infoOf who trace = some (past, view) at equal
  rw [ResponseMenu.info] at equal
  cases state with
  | none => cases equal
  | some control =>
      change (if control.actor = some who then
        some (control.execution.recall who, control.execution.observe app who)
        else none) = some (past, view) at equal
      split at equal
      · have sameView := congrArg Prod.snd (Option.some.inj equal)
        change control.execution.observe app who = view at sameView
        apply evidence.observed_valid control.execution who
          (evidence.history_sound initial horizon scheduler
            (menu.toRawTrace initial horizon scheduler trace)) fact
        exact sameView.symm ▸ observed
      · cases equal

end Interaction.ReactiveApplication.ReceiptEvidence
