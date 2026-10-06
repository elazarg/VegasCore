/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFiniteness
import Vegas.Game.SourceServiceCanonicalPolicy
import Interaction.ReactiveMixtureRounds
import GameTheoryExtensions.Math.Probability.TotalVariation

/-! # Turn-counted prescribed policy for every scheduler

An owner's opportunities at its event are its turns: responses whose view had
the event as the player's own turn. A turn timing chooses, for each owned
event, the turn index at which the owner makes its source decision; every
other response is silent. The index is read from actual own recall, so the
policy needs no roster or scheduler cursor.

The source decision is the canonical one
(`Vegas.sourceServiceCanonicalOpportunity`): a binding is submitted at the slot
the audit expects, and no fresh call is made once a packet included within the
inclusion bound `bound event` would miss the event's deadline.

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

/-- For each owned event, a law over the owner's turn index at which it makes
its source decision. -/
abbrev TurnTiming (setup : Setup (Player := Player) (L := L)) (turns : Nat)
    (mode : EventGraph.ExecutionMode := .sequential) : Type :=
  ∀ event who, (serviceGraph setup mode).actor? event = some who → PMF (Fin (turns + 1))

/-- Decide at the first turn: the limiting timing. -/
def firstTurnTiming (setup : Setup (Player := Player) (L := L)) (turns : Nat)
    (mode : EventGraph.ExecutionMode := .sequential) : TurnTiming setup turns mode :=
  fun _ _ _ => PMF.pure 0

/-- Defer the decision with total weight `weight`, uniformly over the turns. -/
def deferralTiming (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    (turns : Nat) (weight : ℝ) (nonnegative : 0 ≤ weight) (bounded : weight ≤ 1) :
    TurnTiming setup turns mode := fun _ _ _ =>
  mix weight nonnegative bounded (PMF.uniformOfFintype _) (PMF.pure 0)

/-- The probability that an owned event's owner does not decide at its first
turn; zero for an event without an owner. -/
def TurnTiming.deferral {setup : Setup (Player := Player) (L := L)}
    {mode : EventGraph.ExecutionMode} {turns : Nat} (timing : TurnTiming setup turns mode)
    (event : (serviceGraph setup mode).EventId) : ℝ :=
  match owned : (serviceGraph setup mode).actor? event with
  | none => 0
  | some who => 1 - (timing event who owned 0).toReal

section Configured

variable (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (deadline : (serviceGraph setup mode).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- The opportunity index of `who`'s current input at `event`: the number of its
recorded turns at `event`, when `event` is its turn now. -/
def serviceTurn (who : Player) (event : (serviceGraph setup mode).EventId)
    (past : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (view : (serviceApplication setup mode deadline leaks).PlayerView) : Option Nat :=
  if view.application.publicView.ownTurn? who = some event then
    some (past.countP fun entry =>
      decide (entry.beforeView.application.publicView.ownTurn? who = some event))
  else none

/-- Make the source decision at the selected turn and remain silent otherwise. -/
def serviceTurnFamily (bound : (serviceGraph setup mode).EventId → Nat)
    (profile : BehavioralProfile setup.program) (who : Player)
    (event : (serviceGraph setup mode).EventId) (turns : Nat) (slot : Fin (turns + 1)) :
    (serviceApplication setup mode deadline leaks).Policy :=
  (serviceApplication setup mode deadline leaks).turnScheduledPolicy
    (serviceTurn setup mode deadline leaks who event)
    (some slot) (serviceCanonicalOpportunity setup mode deadline leaks bound profile who event)
    (serviceApplication setup mode deadline leaks).silentPolicy

/-- The turn-counted prescribed policy: at its own turn an owner follows the
behavioral realization of the event's timing lottery; otherwise it is silent. -/
def serviceTurnPolicy (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (who : Player) : (serviceApplication setup mode deadline leaks).Policy := fun past view =>
  match view.application.publicView.ownTurn? who with
  | none => (serviceApplication setup mode deadline leaks).silentPolicy past view
  | some event =>
      if owned : (serviceGraph setup mode).actor? event = some who then
        ((serviceApplication setup mode deadline leaks).policyMixture (timing event who owned)
          (serviceTurnFamily setup mode deadline leaks bound profile who event turns)).policy
            past view
      else (serviceApplication setup mode deadline leaks).silentPolicy past view

end Configured

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The turn index on the default runtime. -/
abbrev sourceServiceTurn : Player → (graph setup).EventId →
    List (application setup leaks).PlayerEntry → (application setup leaks).PlayerView →
      Option Nat :=
  serviceTurn setup .sequential (rankDeadline setup .sequential) leaks

/-- The decision at a selected turn on the default runtime. -/
abbrev sourceServiceTurnFamily : ((graph setup).EventId → Nat) →
    BehavioralProfile setup.program → Player → (graph setup).EventId →
      (turns : Nat) → Fin (turns + 1) → (application setup leaks).Policy :=
  serviceTurnFamily setup .sequential (rankDeadline setup .sequential) leaks

/-- The turn-counted prescribed policy on the default runtime. -/
abbrev sourceServiceTurnPolicy : ((graph setup).EventId → Nat) → (turns : Nat) →
    TurnTiming setup turns → BehavioralProfile setup.program → Player →
      (application setup leaks).Policy :=
  serviceTurnPolicy setup .sequential (rankDeadline setup .sequential) leaks

/-- An input that is not the player's turn at `event` is not an opportunity. -/
theorem sourceServiceTurn_of_not_turn (who : Player) (event : (graph setup).EventId)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (other : view.application.publicView.ownTurn? who ≠ some event) :
    sourceServiceTurn setup leaks who event past view = none := by
  simp only [sourceServiceTurn, serviceTurn, other, ↓reduceIte]

/-- At its own turn a player follows the event's timing mixture. -/
theorem sourceServiceTurnPolicy_turn (bound : (graph setup).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some who)
    (serving : view.application.publicView.ownTurn? who = some event) :
    sourceServiceTurnPolicy setup leaks bound turns timing profile who past view =
      ((application setup leaks).policyMixture (timing event who owned)
        (sourceServiceTurnFamily setup leaks bound profile who event turns)).policy past view := by
  simp only [sourceServiceTurnPolicy, serviceTurnPolicy, serving, owned, ↓reduceDIte]

/-- A player owning no ready event is silent. -/
theorem sourceServiceTurnPolicy_idle (bound : (graph setup).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (idle : view.application.publicView.Idle who) :
    sourceServiceTurnPolicy setup leaks bound turns timing profile who past view =
      (application setup leaks).silentPolicy past view := by
  simp only [sourceServiceTurnPolicy, serviceTurnPolicy, PublicView.ownTurn?_eq_none _ who idle]

theorem sourceServiceTurnFamily_finiteSupport (bound : (graph setup).EventId → Nat)
    (finite : setup.program.FiniteBindingTypes)
    (profile : BehavioralProfile setup.program) (who : Player) (event : (graph setup).EventId)
    (turns : Nat) (slot : Fin (turns + 1)) :
    ReactiveApplication.Policy.FiniteSupport _
      (sourceServiceTurnFamily setup leaks bound profile who event turns slot) :=
  (application setup leaks).turnScheduledPolicy_finiteSupport _ _
    (sourceServiceCanonicalOpportunity_finiteSupport setup leaks bound finite profile who event)
    (application setup leaks).silentPolicy_finiteSupport

theorem sourceServiceTurnPolicy_finiteSupport (bound : (graph setup).EventId → Nat)
    (turns : Nat) (timing : TurnTiming setup turns)
    (finite : setup.program.FiniteBindingTypes) (profile : BehavioralProfile setup.program)
    (who : Player) :
    ReactiveApplication.Policy.FiniteSupport _
      (sourceServiceTurnPolicy setup leaks bound turns timing profile who) := by
  intro past view
  unfold sourceServiceTurnPolicy serviceTurnPolicy
  split
  · exact (application setup leaks).silentPolicy_finiteSupport past view
  · split
    · exact (application setup leaks).policyMixture_finiteSupport _
        (sourceServiceTurnFamily_finiteSupport setup leaks bound finite profile who _ turns)
        past view
    · exact (application setup leaks).silentPolicy_finiteSupport past view

theorem firstTurnTiming_deferral {mode : EventGraph.ExecutionMode} (turns : Nat)
    (event : (serviceGraph setup mode).EventId) :
    (firstTurnTiming setup turns mode).deferral event = 0 := by
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
