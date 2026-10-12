/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRecovery
import Interaction.ReactiveRoundReachability

/-! # Continuing an execution reached by other players

An execution reached by some players can be continued by others. The anchored
profile (`Interaction.ReactiveApplication.anchoredPolicy`) replays, at every
input lying on a player's recall at the anchor execution, the response that
player recorded there, and follows the continuing profile at every other
input. Every execution the original players reach along the way to the anchor
is reached by the anchored profile
(`Interaction.ReactiveApplication.mem_roundsFrom_anchoredPolicy`), and from the
anchor on the anchored profile runs exactly as the continuing profile
(`Interaction.ReactiveApplication.runRounds_anchoredPolicy`). So a property of
the runs of a fixed profile from the executions it reaches yields the same
property of the continuing profile from every execution reached by any
players.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}

open Classical in
/-- **The anchored profile.** At an input whose recall is a strict prefix of
the player's recall at `anchor`, recorded next at that input's view, respond
with the recorded response; elsewhere follow `players`. -/
def anchoredPolicy (anchor : app.Execution) (players : Principal → app.Policy) :
    Principal → app.Policy := fun who past view =>
  match (anchor.recall who)[past.length]? with
  | some entry =>
      if past ++ [entry] <+: anchor.recall who ∧ entry.beforeView = view then
        PMF.pure entry.action
      else players who past view
  | none => players who past view

omit [DecidableEq Principal] in
/-- From a recall extending the anchor's, the anchored profile follows the
continuing profile. -/
theorem anchoredPolicy_of_extends (anchor : app.Execution) (players : Principal → app.Policy)
    (who : Principal) (past : List app.PlayerEntry) (view : app.PlayerView)
    (extends_ : anchor.recall who <+: past) :
    anchoredPolicy anchor players who past view = players who past view := by
  have none : (anchor.recall who)[past.length]? = none :=
    List.getElem?_eq_none (extends_.length_le)
  unfold anchoredPolicy
  rw [none]

omit [DecidableEq Principal] in
/-- At an input on the anchor's recall, the anchored profile replays the
recorded response. -/
theorem anchoredPolicy_of_recorded (anchor : app.Execution) (players : Principal → app.Policy)
    (who : Principal) (past : List app.PlayerEntry) (entry : app.PlayerEntry)
    (recorded : past ++ [entry] <+: anchor.recall who) :
    anchoredPolicy anchor players who past entry.beforeView = PMF.pure entry.action := by
  classical
  have found : (anchor.recall who)[past.length]? = some entry := by
    obtain ⟨rest, same⟩ := recorded
    rw [← same]
    simp
  unfold anchoredPolicy
  rw [found]
  simp [recorded]

private theorem respond_recall_self (execution : app.Execution) (who : Principal)
    (action : app.Action) :
    ∃ emitted, (execution.respond app who action).recall who =
      execution.recall who ++ [⟨execution.observe app who, action, emitted⟩] := by
  rcases action with ⟨transmission⟩
  cases transmission <;> simp only [Execution.respond, ↓reduceIte] <;> exact ⟨_, rfl⟩

/-- **The anchored profile reaches what the original players reached.** Every
execution reached by `original` whose recall is, for every player, a prefix of
that player's recall at the anchor, is reached by the anchored profile. -/
theorem mem_roundsFrom_anchoredPolicy (initial : PMF app.State) (scheduler : app.Scheduler)
    (anchor : app.Execution) (original players : Principal → app.Policy) :
    ∀ (count : Nat) (execution : app.Execution),
      execution ∈ (app.roundsFrom initial scheduler original count).support →
      (∀ who, execution.recall who <+: anchor.recall who) →
      execution ∈ (app.roundsFrom initial scheduler (anchoredPolicy anchor players)
        count).support := by
  intro count
  induction count with
  | zero =>
      intro execution supported _
      exact supported
  | succ count ih =>
      intro execution supported below
      rw [roundsFrom_succ] at supported ⊢
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      obtain ⟨command, selected, dispatched⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
      obtain ⟨middle, stepped, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
      have recallEq := app.environmentStep_recall prior middle command stepped
      have priorBelow : ∀ who, prior.recall who <+: anchor.recall who := by
        intro who
        refine List.IsPrefix.trans ?_ (below who)
        change execution ∈ (app.resume original (command.actor? app) middle).support at resumed
        cases actor : command.actor? app with
        | none =>
            rw [actor] at resumed
            cases (PMF.mem_support_pure_iff _ _).mp resumed
            rw [recallEq]
        | some responder =>
            rw [actor] at resumed
            change execution ∈ ((original responder (middle.recall responder)
              (middle.observe app responder)).map (middle.respond app responder)).support
              at resumed
            obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ resumed
            by_cases same : who = responder
            · subst same
              obtain ⟨emitted, recalled⟩ := respond_recall_self middle who response
              rw [recalled, ← recallEq]
              exact List.prefix_append _ _
            · rw [app.respond_recall_other middle responder who same response, recallEq]
      refine (PMF.mem_support_bind_iff _ _ _).mpr ⟨prior, ih prior priorMem priorBelow, ?_⟩
      refine (PMF.mem_support_bind_iff _ _ _).mpr ⟨command, selected, ?_⟩
      refine (PMF.mem_support_bind_iff _ _ _).mpr ⟨middle, stepped, ?_⟩
      change execution ∈ (app.resume original (command.actor? app) middle).support at resumed
      cases actor : command.actor? app with
      | none =>
          rw [actor] at resumed
          exact resumed
      | some responder =>
          rw [actor] at resumed
          change execution ∈ ((original responder (middle.recall responder)
            (middle.observe app responder)).map (middle.respond app responder)).support
            at resumed
          obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ resumed
          obtain ⟨emitted, recalled⟩ := respond_recall_self middle responder response
          have recorded := below responder
          rw [recalled] at recorded
          change _ ∈ ((anchoredPolicy anchor players responder (middle.recall responder)
            (middle.observe app responder)).map (middle.respond app responder)).support
          rw [anchoredPolicy_of_recorded anchor players responder (middle.recall responder)
            ⟨middle.observe app responder, response, emitted⟩ recorded, PMF.pure_map]
          exact (PMF.mem_support_pure_iff _ _).mpr rfl

/-- **From the anchor on, the anchored profile is the continuing profile.** -/
theorem runRounds_anchoredPolicy (scheduler : app.Scheduler) (anchor : app.Execution)
    (players : Principal → app.Policy) (count : Nat) :
    app.runRounds scheduler (anchoredPolicy anchor players) count anchor =
      app.runRounds scheduler players count anchor := by
  refine PolicyInvariant.runRounds_congr (predicate := fun execution =>
    ∀ who, anchor.recall who <+: execution.recall who) ⟨?_, ?_⟩ players ?_ scheduler count
    anchor fun _ => List.prefix_refl _
  · intro execution responder action valid _ who
    by_cases same : who = responder
    · subst same
      obtain ⟨emitted, recalled⟩ := respond_recall_self execution who action
      rw [recalled]
      exact (valid who).trans (List.prefix_append _ _)
    · rw [app.respond_recall_other execution responder who same action]
      exact valid who
  · intro execution next command valid moved who
    rw [app.environmentStep_recall execution next command moved]
    exact valid who
  · intro execution valid who
    exact anchoredPolicy_of_extends anchor players who _ _ (valid who)

end Interaction.ReactiveApplication
