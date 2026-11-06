/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceCanonicalPolicy
import Vegas.Game.RevealServicePayoffs
import Interaction.ReactivePolicyMixture
import Interaction.ReactiveRecovery
import Interaction.ReactiveRoundReachability
import Interaction.ScheduledOpening

/-! # Turn-counted prescribed policy for every scheduler

An owner's opportunities at its event are its turns: responses whose view had
the event as the player's own turn. A turn timing chooses, for each owned
event, the turn index at which the owner makes its source decision; every
other response is silent. The index is read from actual own recall, so the
policy needs no roster or scheduler cursor.

The source decision is the canonical one
(`Vegas.serviceCanonicalOpportunity`): a binding is submitted at the slot
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

/-- The probability that an owned event's owner does not decide at its first
turn; zero for an event without an owner. -/
def TurnTiming.deferral {setup : Setup (Player := Player) (L := L)}
    {mode : EventGraph.ExecutionMode} {turns : Nat} (timing : TurnTiming setup turns mode)
    (event : (serviceGraph setup mode).EventId) : ℝ :=
  match owned : (serviceGraph setup mode).actor? event with
  | none => 0
  | some who => 1 - (timing event who owned 0).toReal

/-- The missing mass after retaining each event's first-turn branch. -/
def TurnTiming.deferralError {setup : Setup (Player := Player) (L := L)}
    {mode : EventGraph.ExecutionMode} {turns : Nat} (timing : TurnTiming setup turns mode) : ℝ :=
  1 - ∏ event, (1 - timing.deferral event)

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

/-- Make a reference's decision at the selected turn and remain silent otherwise. -/
def serviceReferenceTurnFamily (bound : (serviceGraph setup mode).EventId → Nat)
    (reference : (serviceGraph setup mode).BehavioralProfile) (who : Player)
    (event : (serviceGraph setup mode).EventId) (turns : Nat) (slot : Fin (turns + 1)) :
    (serviceApplication setup mode deadline leaks).Policy :=
  (serviceApplication setup mode deadline leaks).turnScheduledPolicy
    (serviceTurn setup mode deadline leaks who event)
    (some slot) (serviceReferenceOpportunity setup mode deadline leaks bound reference who event)
    (serviceApplication setup mode deadline leaks).silentPolicy

/-- Make the source decision at the selected turn and remain silent otherwise. -/
def serviceTurnFamily (bound : (serviceGraph setup mode).EventId → Nat)
    (profile : BehavioralProfile setup.program) (who : Player)
    (event : (serviceGraph setup mode).EventId) (turns : Nat) (slot : Fin (turns + 1)) :
    (serviceApplication setup mode deadline leaks).Policy :=
  serviceReferenceTurnFamily setup mode deadline leaks bound
    (compileEventProfile setup.program profile) who event turns slot

/-- A reference's turn-counted policy: at its own turn an owner follows the
behavioral realization of the event's timing lottery; otherwise it is silent. -/
def serviceReferenceTurnPolicy (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns mode)
    (reference : (serviceGraph setup mode).BehavioralProfile)
    (who : Player) : (serviceApplication setup mode deadline leaks).Policy := fun past view =>
  match view.application.publicView.ownTurn? who with
  | none => (serviceApplication setup mode deadline leaks).silentPolicy past view
  | some event =>
      if owned : (serviceGraph setup mode).actor? event = some who then
        ((serviceApplication setup mode deadline leaks).policyMixture (timing event who owned)
          (serviceReferenceTurnFamily setup mode deadline leaks bound reference who event
            turns)).policy past view
      else (serviceApplication setup mode deadline leaks).silentPolicy past view

/-- The turn-counted prescribed policy of the compiled source profile. -/
def serviceTurnPolicy (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (who : Player) : (serviceApplication setup mode deadline leaks).Policy :=
  serviceReferenceTurnPolicy setup mode deadline leaks bound turns timing
    (compileEventProfile setup.program profile) who

/-- **A reference's client policy.** The turn-counted policy, completed by
silence at every history where the player's own recorded responses do not all
follow it. -/
def serviceReferenceClientPolicy (bound : (serviceGraph setup mode).EventId → Nat)
    (turns : Nat) (timing : TurnTiming setup turns mode)
    (reference : (serviceGraph setup mode).BehavioralProfile)
    (who : Player) : (serviceApplication setup mode deadline leaks).Policy :=
  (serviceReferenceTurnPolicy setup mode deadline leaks bound turns timing reference who).recover
    (serviceApplication setup mode deadline leaks).silentPolicy

/-- **The client policy** of the compiled source profile. -/
def serviceClientPolicy (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (who : Player) : (serviceApplication setup mode deadline leaks).Policy :=
  serviceReferenceClientPolicy setup mode deadline leaks bound turns timing
    (compileEventProfile setup.program profile) who

end Configured

section ClientRuns

variable {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- Completing clients after their own off-policy responses preserves their run law. -/
theorem sourceServiceClientPolicy_roundsFrom
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (count : Nat) :
    (serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
      scheduler (serviceClientPolicy setup mode deadline leaks bound turns timing profile) count =
      (serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler (serviceTurnPolicy setup mode deadline leaks bound turns timing profile)
        count := by
  unfold ReactiveApplication.roundsFrom
  congr 1
  funext state
  have completed := ReactiveApplication.Policy.recoverWhere_runRounds
    (serviceTurnPolicy setup mode deadline leaks bound turns timing profile) (fun _ => True)
    (fun _ => (serviceApplication setup mode deadline leaks).silentPolicy) scheduler count
    (ReactiveApplication.Execution.initial (serviceApplication setup mode deadline leaks) state)
      (fun _ _ => .nil)
  simp only [ite_true] at completed
  exact completed

/-- Against a unilateral deviation, completing the other clients preserves the run law. -/
theorem sourceServiceClientPolicy_deviation_roundsFrom
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (who : Player) (alternative : (serviceApplication setup mode deadline leaks).Policy)
    (count : Nat) :
    (serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
      scheduler (Function.update
        (serviceClientPolicy setup mode deadline leaks bound turns timing profile)
        who alternative) count =
      (serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler (Function.update
          (serviceTurnPolicy setup mode deadline leaks bound turns timing profile)
          who alternative) count := by
  let players := Function.update
    (serviceTurnPolicy setup mode deadline leaks bound turns timing profile) who alternative
  have shape : Function.update
      (serviceClientPolicy setup mode deadline leaks bound turns timing profile) who alternative =
      fun player => if player ≠ who then (players player).recover
        (serviceApplication setup mode deadline leaks).silentPolicy else players player := by
    funext player
    by_cases same : player = who
    · subst player
      simp only [players, Function.update_self, ne_eq, not_true_eq_false, ↓reduceIte]
    · simp only [players, Function.update_of_ne same, ne_eq, same, not_false_eq_true, ↓reduceIte]
      rfl
  unfold ReactiveApplication.roundsFrom
  rw [shape]
  congr 1
  funext state
  exact ReactiveApplication.Policy.recoverWhere_runRounds players (fun player => player ≠ who)
    (fun _ => (serviceApplication setup mode deadline leaks).silentPolicy) scheduler count
    (ReactiveApplication.Execution.initial (serviceApplication setup mode deadline leaks) state)
      (fun _ _ => .nil)

end ClientRuns

/-- The first-turn clients of a source profile have, through the supplied reader,
the complete terminal configuration law of the profile's source run. -/
def FirstTurnReadoutLaw (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode) (deadline : (serviceGraph setup mode).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (reader : (serviceApplication setup mode deadline leaks).ProtocolState →
      Option (Config Player L setup.program.terminalCtx))
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) : Prop :=
  ((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
    scheduler (serviceTurnPolicy setup mode deadline leaks bound turns
      (firstTurnTiming setup turns mode) profile) horizon).map
      (fun execution => reader ((serviceApplication setup mode deadline leaks).finished
        execution)) =
    (setup.run profile).map some

/-- The first-turn clients of a source profile have the complete terminal
configuration law of the profile's source run. -/
def FirstTurnSourceLaw (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode) (deadline : (serviceGraph setup mode).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) : Prop :=
  ((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
    scheduler (serviceTurnPolicy setup mode deadline leaks bound turns
      (firstTurnTiming setup turns mode) profile) horizon).map
      (fun execution => serviceSourceReadout setup mode deadline leaks
        ((serviceApplication setup mode deadline leaks).finished execution)) =
    (setup.run profile).map some

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

section Generic

variable (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- An input that is not the player's turn at `event` is not an opportunity. -/
theorem sourceServiceTurn_of_not_turn (who : Player) (event : (serviceGraph setup mode).EventId)
    (past : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (view : (serviceApplication setup mode deadline leaks).PlayerView)
    (other : view.application.publicView.ownTurn? who ≠ some event) :
    serviceTurn setup mode deadline leaks who event past view = none := by
  simp only [serviceTurn, other, ↓reduceIte]

/-- At its own turn a player follows the event's timing mixture. -/
theorem sourceServiceTurnPolicy_turn (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns mode)
    (profile : BehavioralProfile setup.program) (who : Player)
    (past : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (view : (serviceApplication setup mode deadline leaks).PlayerView)
    (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some who)
    (serving : view.application.publicView.ownTurn? who = some event) :
    serviceTurnPolicy setup mode deadline leaks bound turns timing profile who past view =
      ((serviceApplication setup mode deadline leaks).policyMixture (timing event who owned)
        (serviceTurnFamily setup mode deadline leaks bound profile who event turns)).policy past
        view := by
  simp only [serviceTurnPolicy, serviceReferenceTurnPolicy, serving, owned, ↓reduceDIte]
  rfl

section FirstTurn

variable {setup leaks}

/-- At the first turn no earlier recorded response saw the event as the
player's turn. -/
theorem sourceServiceTurn_first {owner : Player} {event : (serviceGraph setup mode).EventId}
    {past : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    {view : (serviceApplication setup mode deadline leaks).PlayerView}
    (first : serviceTurn setup mode deadline leaks owner event past view = some 0) :
    view.application.publicView.ownTurn? owner = some event ∧
      ∀ entry ∈ past, entry.beforeView.application.publicView.ownTurn? owner ≠ some event := by
  unfold serviceTurn at first
  split at first
  · rename_i turn
    have counted := Option.some.inj first
    rw [List.countP_eq_zero] at counted
    exact ⟨turn, fun entry member equal => counted entry member (decide_eq_true equal)⟩
  · cases first

/-- A pure first-turn timing retains its selection after every own transcript. -/
theorem sourceServiceTurnPolicy_firstTurn {bound : (serviceGraph setup mode).EventId → Nat}
    {turns : Nat} {profile : BehavioralProfile setup.program} {who : Player}
    {past : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    {view : (serviceApplication setup mode deadline leaks).PlayerView}
    {event : (serviceGraph setup mode).EventId}
    (owned : (serviceGraph setup mode).actor? event = some who)
    (first : serviceTurn setup mode deadline leaks who event past view = some 0) :
    serviceTurnPolicy setup mode deadline leaks bound turns (firstTurnTiming setup turns mode)
        profile who past view =
      serviceCanonicalOpportunity setup mode deadline leaks bound profile who event past view := by
  let app := serviceApplication setup mode deadline leaks
  let family := serviceTurnFamily setup mode deadline leaks bound profile who event turns
  have pin : (app.policyMixture (PMF.pure (0 : Fin (turns + 1))) family).posterior past =
      PMF.pure 0 := by
    simpa only [List.nil_append] using app.policyMixture_posterior_pure_append
      (PMF.pure (0 : Fin (turns + 1))) family [] past 0 rfl
  rw [sourceServiceTurnPolicy_turn setup leaks bound turns _ profile who past view event owned
    (sourceServiceTurn_first first).1]
  change (app.policyMixture (PMF.pure (0 : Fin (turns + 1))) family).policy past view = _
  rw [app.policyMixture_policy, pin, PMF.pure_bind]
  exact app.turnScheduledPolicy_selected _ (0 : Fin (turns + 1)) _ _ past view first


/-- A pure first-turn client is silent at every later turn at the event. -/
theorem sourceServiceTurnPolicy_laterTurn {bound : (serviceGraph setup mode).EventId → Nat}
    {turns : Nat} {profile : BehavioralProfile setup.program} {who : Player}
    {past : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    {view : (serviceApplication setup mode deadline leaks).PlayerView}
    {event : (serviceGraph setup mode).EventId}
    (owned : (serviceGraph setup mode).actor? event = some who)
    (serving : view.application.publicView.ownTurn? who = some event)
    (later : serviceTurn setup mode deadline leaks who event past view ≠ some 0) :
    serviceTurnPolicy setup mode deadline leaks bound turns (firstTurnTiming setup turns mode)
        profile who past view = PMF.pure ⟨none⟩ := by
  let app := serviceApplication setup mode deadline leaks
  let family := serviceTurnFamily setup mode deadline leaks bound profile who event turns
  have pin : (app.policyMixture (PMF.pure (0 : Fin (turns + 1))) family).posterior past =
      PMF.pure 0 := by
    simpa only [List.nil_append] using app.policyMixture_posterior_pure_append
      (PMF.pure (0 : Fin (turns + 1))) family [] past 0 rfl
  rw [sourceServiceTurnPolicy_turn setup leaks bound turns _ profile who past view event owned
    serving]
  change (app.policyMixture (PMF.pure (0 : Fin (turns + 1))) family).policy past view = _
  rw [app.policyMixture_policy, pin, PMF.pure_bind]
  exact app.turnScheduledPolicy_unselected _ (some (0 : Fin (turns + 1))) _ _ past view
    (fun slot selected => by cases selected; exact later)

end FirstTurn

theorem firstTurnTiming_deferral {mode : EventGraph.ExecutionMode} (turns : Nat)
    (event : (serviceGraph setup mode).EventId) :
    (firstTurnTiming setup turns mode).deferral event = 0 := by
  unfold TurnTiming.deferral
  split
  · rfl
  · simp [firstTurnTiming]

@[simp]
theorem firstTurnTiming_deferralError {mode : EventGraph.ExecutionMode} (turns : Nat) :
    (firstTurnTiming setup turns mode).deferralError = 0 := by
  simp [TurnTiming.deferralError, firstTurnTiming_deferral]

end Generic

end Vegas
