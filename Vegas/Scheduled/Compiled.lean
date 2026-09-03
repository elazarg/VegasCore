/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Protocol
import Vegas.Scheduled.Basic

/-!
# The serialized counterfactual for a compiled program

`Vegas.Scheduled.Basic` reasons about scheduling over an abstract system, and
`EventGraph.toExecutionProtocol` compiles a program to a protocol that resolves a
whole frontier atomically.  Results about the first said nothing about the
second, which is what this module fixes.

## What is built here, and what it is not

This is **not** the compiled protocol.  That one applies a frontier packet as a
single joint action, with no scheduler coordinate at all
(`toExecutionProtocol_step_eq_pure_applyFrontier`), so no strategy in it can
condition on an order.

What is built here is the *counterfactual*: the same graph, run by a runtime
that applies one player's submission at a time in an order it chooses and
publishes.  It is the implementation a compiler would produce if it serialized
the frontier instead of exposing it whole, and it is the object the negative
scheduling results are about.  Having both as instances of one interface is what
lets the comparison be stated rather than described.

## Why menus need the private channel

A player's legal frontier action is fixed by its *own* observation
(`FrontierAction.available_iff_of_observe_eq`), which includes values sealed to
it; `publicObserve` sees only unowned fields.  So `Obs` here is the pair of the
public observation and the player's own — the public part carries activity,
which depends on global readiness, and the private part carries availability.
This is exactly the requirement that made `ScheduledSystem` grow `Obs` in the
first place.

## Status

The instantiation is complete and its obligations are discharged.  What is *not*
proved here is that the two runtimes agree on anything: whether this system
satisfies `EffectsCommute`, and hence whether serializing is harmless for a
schedule-blind payoff, needs the reordering theorem, which needs enabledness
stability across peer writes.  The pieces for it exist
(`CommitStep.written_eq`, `FrontierAction.legal_write_unique`,
`CommitAvailable.persist_after_other_ready_write`,
`CommitAvailable.reflect_before_other_ready_write`, `Ready.completeNode_of_ne`)
and the argument is not assembled.
-/

noncomputable section

namespace Vegas

open GameTheory.Protocol
open GameTheory.Math.Probability
open EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

namespace Compiled

/-- The packet in which `who` submits `action` and nobody else moves.

A serialized runtime applies one of these at a time; the compiled protocol
applies a whole frontier at once.  That is the entire difference between them. -/
def soloPacket {G : Graph Player L} (who : Player) (action : FrontierAction G who) :
    ∀ other, Option (FrontierAction G other) :=
  fun other => if hwho : who = other then some (hwho ▸ action) else none

omit [Fintype Player] in
@[simp] theorem soloPacket_self {G : Graph Player L} (who : Player)
    (action : FrontierAction G who) :
    soloPacket who action who = some action := by
  simp [soloPacket]

omit [Fintype Player] in
@[simp] theorem soloPacket_of_ne {G : Graph Player L} {who other : Player}
    (action : FrontierAction G who) (hne : who ≠ other) :
    soloPacket who action other = none := by
  simp [soloPacket, hne]

/-- Being obliged to move, in the compiled protocol's sense. -/
def ActiveAt (G : Graph Player L) (cfg : Config G) (who : Player) : Prop :=
  ¬ Terminal G cfg ∧ readyInternalNodes G cfg = ∅ ∧ who ∈ activePlayers G cfg

/-- Activity is fixed by what a player sees.

The public part decides whether execution has stopped and whether internal work
is pending; the player's own part decides whether it has a ready commit. -/
theorem activeAt_iff_of_obs_eq {G : Graph Player L} {left right : Config G}
    {who : Player}
    (hpublic : publicObserve G left = publicObserve G right)
    (hown : observe G left who = observe G right who) :
    ActiveAt G left who ↔ ActiveAt G right who := by
  have hdone : left.done = right.done := by
    have := congrArg PublicObservation.done hpublic
    simpa [publicObserve] using this
  have hterminal : Terminal G left ↔ Terminal G right := by
    unfold Terminal
    rw [hdone]
  have hinternal : readyInternalNodes G left = readyInternalNodes G right :=
    readyInternalNodes_eq_of_publicObserve_eq hpublic
  have hready : readyCommitNodes G left who = readyCommitNodes G right who :=
    readyCommitNodes_eq_of_observe_eq hown
  unfold ActiveAt activePlayers
  rw [hinternal]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hready]
  exact and_congr_left' (not_congr hterminal)

/-- What a participant's own view permits it to submit. -/
def MenuAllows (G : Graph Player L) (cfg : Config G) (who : Player) :
    Option (FrontierAction G who) → Prop
  | none => ¬ ActiveAt G cfg who
  | some action => ActiveAt G cfg who ∧ FrontierAction.Available G cfg who action

/-- **What a player may submit is fixed by what it sees.**

Activity comes from the public part, availability from the player's own.  This
is the obligation `ScheduledSystem` imposes, and it is satisfiable here only
because the observation is the pair: no function of the public view alone
decides a Vegas player's menu. -/
theorem menuAllows_iff_of_obs_eq {G : Graph Player L} (hwf : G.WF)
    {left right : Config G} {who : Player}
    (hpublic : publicObserve G left = publicObserve G right)
    (hown : observe G left who = observe G right who)
    (choice : Option (FrontierAction G who)) :
    MenuAllows G left who choice ↔ MenuAllows G right who choice := by
  cases choice with
  | none => exact not_congr (activeAt_iff_of_obs_eq hpublic hown)
  | some action =>
      exact and_congr (activeAt_iff_of_obs_eq hpublic hown)
        (FrontierAction.available_iff_of_observe_eq hwf hown)

/-- **The serialized runtime for a compiled program.**

The same graph as `EventGraph.toExecutionProtocol`, run one submission at a time
in an order the scheduler picks and the state records.  This is the
counterfactual the negative scheduling results are about; the compiled protocol
is the atomic one and has no scheduler coordinate at all.

The accepted orders are the *enumerations* of the players, not every list.  A
runtime that could accept `[]`, or a list omitting a submitter, would not be a
serialization of the round -- it would be a runtime that drops submissions, and
comparing it to the atomic protocol would prove nothing about ordering.
Requiring every player costs nothing, since `applyOrder` skips a coordinate that
did not submit. -/
def serializedSystem (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G) :
    ScheduledSystem Player where
  Base := ReachableConfig G
  Action who := FrontierAction G who
  init := ⟨Config.initial G, Reachable.initial⟩
  active state who := ActiveAt G state.1 who
  available state who := { action | FrontierAction.Available G state.1 who action }
  terminal state := Terminal G state.1
  applyOne state who action :=
    FinDist.pure (applyFrontier G state (soloPacket who action))
  View := PublicObservation G
  view state := publicObserve G state.1
  Obs who := PublicObservation G × Observation G who
  obs state who := (publicObserve G state.1, observe G state.1 who)
  menuAt who seen :=
    { choice | ∃ cfg : Config G,
        publicObserve G cfg = seen.1 ∧ observe G cfg who = seen.2 ∧
          MenuAllows G cfg who choice }
  menuAt_some state who action := by
    constructor
    · rintro ⟨cfg, hpublic, hown, hallows⟩
      exact (menuAllows_iff_of_obs_eq hwf hpublic hown (some action)).mp hallows
    · rintro ⟨hactive, havailable⟩
      exact ⟨state.1, rfl, rfl, hactive, havailable⟩
  menuAt_none state who := by
    constructor
    · rintro ⟨cfg, hpublic, hown, hallows⟩
      exact (menuAllows_iff_of_obs_eq hwf hpublic hown none).mp hallows
    · intro hinactive
      exact ⟨state.1, rfl, rfl, hinactive⟩
  schedules _ := { order | order.Nodup ∧ ∀ who : Player, who ∈ order }
  schedules_nonempty _ :=
    ⟨Finset.univ.toList, Finset.univ.nodup_toList,
      fun who => Finset.mem_toList.mpr (Finset.mem_univ who)⟩
  progress state hterminal := (toExecutionProtocol G hwf hguards).progress state hterminal

/-- **The serialized runtime is genuinely permissive.**

Two distinct enumerations of the players are both accepted, so its scheduler has
a real choice to make -- which is the whole difference from the compiled
protocol, where there is no scheduler coordinate to choose with.

Stated from a supplied pair rather than derived from `1 < card Player`, so a
caller exhibits the two orders its own program actually admits. -/
theorem serializedSystem_not_enforcesOrder
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    {left right : List Player}
    (hleftNodup : left.Nodup) (hleftAll : ∀ who : Player, who ∈ left)
    (hrightNodup : right.Nodup) (hrightAll : ∀ who : Player, who ∈ right)
    (hne : left ≠ right) :
    ¬ (serializedSystem G hwf hguards).EnforcesOrder := by
  intro henforce
  exact hne (henforce (publicObserve G (Config.initial G))
    ⟨hleftNodup, hleftAll⟩ ⟨hrightNodup, hrightAll⟩)

end Compiled

end Vegas
