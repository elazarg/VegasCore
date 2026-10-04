/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseMenu

/-! # Finite menus can retain every known-envelope replay

The player's own outputs, passive leaks and ledger determine replay eligibility.
Adding all those replays to any finite menu stays finite, without bounding the
numeric identifiers or removing the original responses. Failed replay attempts
outside this set are not identified with silence: they may be supplied by the
base menu, and their private recall is still the raw response record.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

variable {Principal : Type} {app : ReactiveApplication Principal} (menu : app.ResponseMenu)

def knownPackets (past : List app.PlayerEntry) (view : app.PlayerView) :
    List (Message Principal app.Payload) :=
  app.outputs past ++ view.messages.leaked ++ view.messages.ledger

def replayActions (past : List app.PlayerEntry) (view : app.PlayerView) :
    Finset app.Action := by
  classical
  exact ((knownPackets past view).map fun message =>
    (⟨some (.replay message.id)⟩ : app.Action)).toFinset

/-- Close a menu under every replay currently supported by the player's knowledge. -/
def withKnownReplays : app.ResponseMenu where
  actions who past view := by
    classical
    exact menu.actions who past view ∪ replayActions past view
  nonempty who past view := by
    classical
    exact (menu.nonempty who past view).mono Finset.subset_union_left

theorem base_available (who : Principal) (past : List app.PlayerEntry) (view : app.PlayerView)
    (action : app.Action) (member : action ∈ menu.actions who past view) :
    action ∈ menu.withKnownReplays.actions who past view := by
  classical
  exact Finset.mem_union_left _ member

theorem known_replay_available (who : Principal) (past : List app.PlayerEntry)
    (view : app.PlayerView)
    (message : Message Principal app.Payload) (known : message ∈ knownPackets past view) :
    (⟨some (.replay message.id)⟩ : app.Action) ∈
      menu.withKnownReplays.actions who past view := by
  classical
  apply Finset.mem_union_right
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨message, known, rfl⟩)

variable [DecidableEq Principal]

/-- On every execution satisfying native input recall, every replayable envelope
is available in the finite menu, with no restriction on its identifier. -/
theorem native_replay_available (execution : app.Execution) (who : Principal)
    (valid : execution.InputRecall app)
    (message : Message Principal app.Payload) (known : message ∈ execution.network.known who) :
    (⟨some (.replay message.id)⟩ : app.Action) ∈
      menu.withKnownReplays.actions who (execution.recall who) (execution.observe app who) := by
  apply menu.known_replay_available who _ _ message
  rw [app.known_from_recall execution who valid] at known
  exact known

end Interaction.ReactiveApplication.ResponseMenu
