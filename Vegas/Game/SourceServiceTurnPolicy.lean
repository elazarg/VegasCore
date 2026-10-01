/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFiniteness
import Interaction.ReactiveMixtureRounds
import GameTheoryExtensions.Math.Probability.TotalVariation

/-! # Turn-counted prescribed policy for every scheduler

An owner's opportunities at its event are its turns: responses whose view had
the event as the player's own turn. A turn timing chooses, for each owned
event, the turn index at which the owner makes its source decision; every
other response replays. The index is read from actual own recall, so the
policy needs no roster or scheduler cursor.

Deciding at the first turn is the limiting policy. Fully mixed approximants
defer the decision with a small total weight, uniformly over later turns. A
later turn need not occur under an arbitrary scheduler, so the deferral weight
is the error by which an approximant may miss the source decision
(`Vegas.TurnTiming.deferral`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The opportunity index of `who`'s current input at `event`: the number of its
recorded turns at `event`, when `event` is its turn now. -/
def sourceServiceTurn (who : Player) (event : (graph setup).EventId)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) : Option Nat :=
  if view.application.publicView.ownTurn? who = some event then
    some (past.countP fun entry =>
      decide (entry.beforeView.application.publicView.ownTurn? who = some event))
  else none

/-- For each owned event, a law over the owner's turn index at which it makes
its source decision. -/
abbrev TurnTiming (turns : Nat) : Type :=
  ∀ event who, (graph setup).actor? event = some who → PMF (Fin (turns + 1))

/-- Make the source decision at the selected turn and replay otherwise. -/
def sourceServiceTurnFamily (profile : BehavioralProfile setup.program) (who : Player)
    (event : (graph setup).EventId) (turns : Nat) (slot : Fin (turns + 1)) :
    (application setup leaks).Policy :=
  (application setup leaks).turnScheduledPolicy (sourceServiceTurn setup leaks who event)
    (some slot) (sourceServiceOpportunity setup leaks profile who event)
    (application setup leaks).replayPolicy

/-- The turn-counted prescribed policy: at its own turn an owner follows the
behavioral realization of the event's timing lottery; otherwise it replays. -/
def sourceServiceTurnPolicy (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (who : Player) :
    (application setup leaks).Policy := fun past view =>
  match view.application.publicView.ownTurn? who with
  | none => (application setup leaks).replayPolicy past view
  | some event =>
      if owned : (graph setup).actor? event = some who then
        ((application setup leaks).policyMixture (timing event who owned)
          (sourceServiceTurnFamily setup leaks profile who event turns)).policy past view
      else (application setup leaks).replayPolicy past view

/-- Decide at the first turn: the limiting timing. -/
def firstTurnTiming (turns : Nat) : TurnTiming setup turns := fun _ _ _ => PMF.pure 0

/-- Defer the decision with total weight `weight`, uniformly over the turns. -/
def deferralTiming (turns : Nat) (weight : ℝ) (nonnegative : 0 ≤ weight) (bounded : weight ≤ 1) :
    TurnTiming setup turns := fun _ _ _ =>
  mix weight nonnegative bounded (PMF.uniformOfFintype _) (PMF.pure 0)

variable {setup}

/-- The probability that an owned event's owner does not decide at its first
turn; zero for an event without an owner. -/
def TurnTiming.deferral {turns : Nat} (timing : TurnTiming setup turns)
    (event : (graph setup).EventId) : ℝ :=
  match owned : (graph setup).actor? event with
  | none => 0
  | some who => 1 - (timing event who owned 0).toReal

variable (setup)

/-- An input that is not the player's turn at `event` is not an opportunity. -/
theorem sourceServiceTurn_of_not_turn (who : Player) (event : (graph setup).EventId)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (other : view.application.publicView.ownTurn? who ≠ some event) :
    sourceServiceTurn setup leaks who event past view = none := by
  simp only [sourceServiceTurn, other, ↓reduceIte]

/-- At its own turn a player follows the event's timing mixture. -/
theorem sourceServiceTurnPolicy_turn (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some who)
    (serving : view.application.publicView.ownTurn? who = some event) :
    sourceServiceTurnPolicy setup leaks turns timing profile who past view =
      ((application setup leaks).policyMixture (timing event who owned)
        (sourceServiceTurnFamily setup leaks profile who event turns)).policy past view := by
  simp only [sourceServiceTurnPolicy, serving, owned, ↓reduceDIte]

/-- A player owning no ready event replays. -/
theorem sourceServiceTurnPolicy_idle (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (idle : view.application.publicView.Idle who) :
    sourceServiceTurnPolicy setup leaks turns timing profile who past view =
      (application setup leaks).replayPolicy past view := by
  simp only [sourceServiceTurnPolicy, PublicView.ownTurn?_eq_none _ who idle]

theorem sourceServiceTurnFamily_finiteSupport (finite : setup.program.FiniteBindingTypes)
    (profile : BehavioralProfile setup.program) (who : Player) (event : (graph setup).EventId)
    (turns : Nat) (slot : Fin (turns + 1)) :
    ReactiveApplication.Policy.FiniteSupport _
      (sourceServiceTurnFamily setup leaks profile who event turns slot) :=
  (application setup leaks).turnScheduledPolicy_finiteSupport _ _
    (sourceServiceOpportunity_finiteSupport setup leaks finite profile who event)
    (application setup leaks).replayPolicy_finiteSupport

theorem sourceServiceTurnPolicy_finiteSupport (turns : Nat) (timing : TurnTiming setup turns)
    (finite : setup.program.FiniteBindingTypes) (profile : BehavioralProfile setup.program)
    (who : Player) :
    ReactiveApplication.Policy.FiniteSupport _
      (sourceServiceTurnPolicy setup leaks turns timing profile who) := by
  intro past view
  unfold sourceServiceTurnPolicy
  split
  · exact (application setup leaks).replayPolicy_finiteSupport past view
  · split
    · exact (application setup leaks).policyMixture_finiteSupport _
        (sourceServiceTurnFamily_finiteSupport setup leaks finite profile who _ turns) past view
    · exact (application setup leaks).replayPolicy_finiteSupport past view

theorem firstTurnTiming_deferral (turns : Nat) (event : (graph setup).EventId) :
    (firstTurnTiming setup turns).deferral event = 0 := by
  unfold TurnTiming.deferral
  split
  · rfl
  · simp [firstTurnTiming]

theorem deferralTiming_deferral_le (turns : Nat) (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bounded : weight ≤ 1) (event : (graph setup).EventId) :
    (deferralTiming setup turns weight nonnegative bounded).deferral event ≤ weight := by
  unfold TurnTiming.deferral
  split
  · exact nonnegative
  · rw [deferralTiming, mix_apply_toReal]
    have uniform : 0 ≤ ((PMF.uniformOfFintype (Fin (turns + 1))) 0).toReal :=
      ENNReal.toReal_nonneg
    simp only [PMF.pure_apply, ↓reduceIte, ENNReal.toReal_one]
    nlinarith

theorem deferralTiming_fullSupport (turns : Nat) (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bounded : weight ≤ 1) (positive : 0 < weight) (event : (graph setup).EventId)
    (who : Player) (owned : (graph setup).actor? event = some who) :
    FullSupport (deferralTiming setup turns weight nonnegative bounded event who owned) := by
  intro slot
  exact mem_support_mix_left weight nonnegative bounded positive
    (PMF.mem_support_uniformOfFintype slot)

end Vegas
