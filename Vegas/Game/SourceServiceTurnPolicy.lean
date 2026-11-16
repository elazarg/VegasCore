module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceCanonicalPolicy
public import Vegas.Game.RevealServicePayoffs
public import Interaction.ReactivePolicyMixture
public import Interaction.ReactiveRecovery
public import Interaction.ReactiveRoundReachability
public import Interaction.ScheduledOpening

@[expose] public section

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
    (deps : setup.dataflowGraph.Dependencies := setup.informationDependencies) : Type :=
  ∀ event who, (serviceGraph setup deps).actor? event = some who → PMF (Fin (turns + 1))

/-- Decide at the first turn: the limiting timing. -/
def firstTurnTiming (setup : Setup (Player := Player) (L := L)) (turns : Nat)
    (deps : setup.dataflowGraph.Dependencies := setup.informationDependencies) :
    TurnTiming setup turns deps :=
  fun _ _ _ => PMF.pure 0

/-- The probability that an owned event's owner does not decide at its first
turn; zero for an event without an owner. -/
def TurnTiming.deferral {setup : Setup (Player := Player) (L := L)}
    {deps : setup.dataflowGraph.Dependencies} {turns : Nat} (timing : TurnTiming setup turns deps)
    (event : (serviceGraph setup deps).EventId) : ℝ :=
  match owned : (serviceGraph setup deps).actor? event with
  | none => 0
  | some who => 1 - (timing event who owned 0).toReal

/-- The missing mass after retaining each event's first-turn branch. -/
def TurnTiming.deferralError {setup : Setup (Player := Player) (L := L)}
    {deps : setup.dataflowGraph.Dependencies} {turns : Nat}
    (timing : TurnTiming setup turns deps) : ℝ :=
  1 - ∏ event, (1 - timing.deferral event)

section Configured

variable (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
  (duration : (serviceGraph setup deps).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))

/-- The opportunity index of `who`'s current input at `event`: the number of its
recorded turns at `event`, when `event` is its turn now. -/
def serviceTurn (who : Player) (event : (serviceGraph setup deps).EventId)
    (past : List (serviceApplication setup deps duration leaks).PlayerEntry)
    (view : (serviceApplication setup deps duration leaks).PlayerView) : Option Nat :=
  if view.application.publicView.ownTurn? who = some event then
    some (past.countP fun entry =>
      decide (entry.beforeView.application.publicView.ownTurn? who = some event))
  else none

/-- Make a reference's decision at the selected turn and remain silent otherwise. -/
def serviceReferenceTurnFamily (bound : (serviceGraph setup deps).EventId → Nat)
    (reference : (serviceGraph setup deps).BehavioralProfile) (who : Player)
    (event : (serviceGraph setup deps).EventId) (turns : Nat) (slot : Fin (turns + 1)) :
    (serviceApplication setup deps duration leaks).Policy :=
  (serviceApplication setup deps duration leaks).turnScheduledPolicy
    (serviceTurn setup deps duration leaks who event)
    (some slot) (serviceReferenceOpportunity setup deps duration leaks bound reference who event)
    (serviceApplication setup deps duration leaks).silentPolicy

/-- Make the source decision at the selected turn and remain silent otherwise. -/
def serviceTurnFamily (bound : (serviceGraph setup deps).EventId → Nat)
    (profile : BehavioralProfile setup.program) (who : Player)
    (event : (serviceGraph setup deps).EventId) (turns : Nat) (slot : Fin (turns + 1)) :
    (serviceApplication setup deps duration leaks).Policy :=
  serviceReferenceTurnFamily setup deps duration leaks bound
    (compileEventProfile setup.program profile) who event turns slot

/-- A reference's turn-counted policy: at its own turn an owner follows the
behavioral realization of the event's timing lottery; otherwise it is silent. -/
def serviceReferenceTurnPolicy (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns deps)
    (reference : (serviceGraph setup deps).BehavioralProfile)
    (who : Player) : (serviceApplication setup deps duration leaks).Policy := fun past view =>
  match view.application.publicView.ownTurn? who with
  | none => (serviceApplication setup deps duration leaks).silentPolicy past view
  | some event =>
      if owned : (serviceGraph setup deps).actor? event = some who then
        ((serviceApplication setup deps duration leaks).policyMixture (timing event who owned)
          (serviceReferenceTurnFamily setup deps duration leaks bound reference who event
            turns)).policy past view
      else (serviceApplication setup deps duration leaks).silentPolicy past view

/-- The turn-counted prescribed policy of the compiled source profile. -/
def serviceTurnPolicy (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns deps) (profile : BehavioralProfile setup.program)
    (who : Player) : (serviceApplication setup deps duration leaks).Policy :=
  serviceReferenceTurnPolicy setup deps duration leaks bound turns timing
    (compileEventProfile setup.program profile) who

/-- **A reference's client policy.** The turn-counted policy, completed by
silence at every history where the player's own recorded responses do not all
follow it. -/
def serviceReferenceClientPolicy (bound : (serviceGraph setup deps).EventId → Nat)
    (turns : Nat) (timing : TurnTiming setup turns deps)
    (reference : (serviceGraph setup deps).BehavioralProfile)
    (who : Player) : (serviceApplication setup deps duration leaks).Policy :=
  (serviceReferenceTurnPolicy setup deps duration leaks bound turns timing reference who).recover
    (serviceApplication setup deps duration leaks).silentPolicy

/-- **The client policy** of the compiled source profile. -/
def serviceClientPolicy (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns deps) (profile : BehavioralProfile setup.program)
    (who : Player) : (serviceApplication setup deps duration leaks).Policy :=
  serviceReferenceClientPolicy setup deps duration leaks bound turns timing
    (compileEventProfile setup.program profile) who

end Configured

section ClientRuns

variable {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

/-- Completing clients after their own off-policy responses preserves their run law. -/
theorem sourceServiceClientPolicy_roundsFrom
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns deps) (profile : BehavioralProfile setup.program)
    (count : Nat) :
    (serviceApplication setup deps duration leaks).roundsFrom (serviceInitialLaw setup deps)
      scheduler (serviceClientPolicy setup deps duration leaks bound turns timing profile) count =
      (serviceApplication setup deps duration leaks).roundsFrom (serviceInitialLaw setup deps)
        scheduler (serviceTurnPolicy setup deps duration leaks bound turns timing profile)
        count := by
  unfold ReactiveApplication.roundsFrom
  congr 1
  funext state
  have completed := ReactiveApplication.Policy.recoverWhere_runRounds
    (serviceTurnPolicy setup deps duration leaks bound turns timing profile) (fun _ => True)
    (fun _ => (serviceApplication setup deps duration leaks).silentPolicy) scheduler count
    (ReactiveApplication.Execution.initial (serviceApplication setup deps duration leaks) state)
      (fun _ _ => .nil)
  simp only [ite_true] at completed
  exact completed

/-- Against a unilateral deviation, completing the other clients preserves the run law. -/
theorem sourceServiceClientPolicy_deviation_roundsFrom
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns deps) (profile : BehavioralProfile setup.program)
    (who : Player) (alternative : (serviceApplication setup deps duration leaks).Policy)
    (count : Nat) :
    (serviceApplication setup deps duration leaks).roundsFrom (serviceInitialLaw setup deps)
      scheduler (Function.update
        (serviceClientPolicy setup deps duration leaks bound turns timing profile)
        who alternative) count =
      (serviceApplication setup deps duration leaks).roundsFrom (serviceInitialLaw setup deps)
        scheduler (Function.update
          (serviceTurnPolicy setup deps duration leaks bound turns timing profile)
          who alternative) count := by
  let players := Function.update
    (serviceTurnPolicy setup deps duration leaks bound turns timing profile) who alternative
  have shape : Function.update
      (serviceClientPolicy setup deps duration leaks bound turns timing profile) who alternative =
      fun player => if player ≠ who then (players player).recover
        (serviceApplication setup deps duration leaks).silentPolicy else players player := by
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
    (fun _ => (serviceApplication setup deps duration leaks).silentPolicy) scheduler count
    (ReactiveApplication.Execution.initial (serviceApplication setup deps duration leaks) state)
      (fun _ _ => .nil)

end ClientRuns

/-- The first-turn clients of a source profile have, through the supplied reader,
the complete terminal configuration law of the profile's source run. -/
def FirstTurnReadoutLaw (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies) (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (reader : (serviceApplication setup deps duration leaks).ProtocolState →
      Option (Config Player L setup.program.terminalCtx))
    (horizon : Nat) (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) : Prop :=
  ((serviceApplication setup deps duration leaks).roundsFrom (serviceInitialLaw setup deps)
    scheduler (serviceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps) profile) horizon).map
      (fun execution => reader ((serviceApplication setup deps duration leaks).finished
        execution)) =
    (setup.run profile).map some

/-- The first-turn clients of a source profile have the complete terminal
configuration law of the profile's source run. -/
def FirstTurnSourceLaw (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies) (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (horizon : Nat) (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) : Prop :=
  ((serviceApplication setup deps duration leaks).roundsFrom (serviceInitialLaw setup deps)
    scheduler (serviceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps) profile) horizon).map
      (fun execution => serviceSourceReadout setup deps duration leaks
        ((serviceApplication setup deps duration leaks).finished execution)) =
    (setup.run profile).map some

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))

section Generic

variable (setup : Setup (Player := Player) (L := L)) {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))

/-- An input that is not the player's turn at `event` is not an opportunity. -/
theorem sourceServiceTurn_of_not_turn (who : Player) (event : (serviceGraph setup deps).EventId)
    (past : List (serviceApplication setup deps duration leaks).PlayerEntry)
    (view : (serviceApplication setup deps duration leaks).PlayerView)
    (other : view.application.publicView.ownTurn? who ≠ some event) :
    serviceTurn setup deps duration leaks who event past view = none := by
  simp only [serviceTurn, other, ↓reduceIte]

/-- At its own turn a player follows the event's timing mixture. -/
theorem sourceServiceTurnPolicy_turn_reference (bound : (serviceGraph setup deps).EventId → Nat)
    (turns : Nat)
    (timing : TurnTiming setup turns deps)
    (reference : (serviceGraph setup deps).BehavioralProfile) (who : Player)
    (past : List (serviceApplication setup deps duration leaks).PlayerEntry)
    (view : (serviceApplication setup deps duration leaks).PlayerView)
    (event : (serviceGraph setup deps).EventId)
    (owned : (serviceGraph setup deps).actor? event = some who)
    (serving : view.application.publicView.ownTurn? who = some event) :
    serviceReferenceTurnPolicy setup deps duration leaks bound turns timing reference who past
      view =
      ((serviceApplication setup deps duration leaks).policyMixture (timing event who owned)
        (serviceReferenceTurnFamily setup deps duration leaks bound reference who event
          turns)).policy past
        view := by
  simp only [serviceReferenceTurnPolicy, serving, owned, ↓reduceDIte]

/-- At its own turn a player follows the event's timing mixture. -/
theorem sourceServiceTurnPolicy_turn (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns deps)
    (profile : BehavioralProfile setup.program) (who : Player)
    (past : List (serviceApplication setup deps duration leaks).PlayerEntry)
    (view : (serviceApplication setup deps duration leaks).PlayerView)
    (event : (serviceGraph setup deps).EventId)
    (owned : (serviceGraph setup deps).actor? event = some who)
    (serving : view.application.publicView.ownTurn? who = some event) :
    serviceTurnPolicy setup deps duration leaks bound turns timing profile who past view =
      ((serviceApplication setup deps duration leaks).policyMixture (timing event who owned)
        (serviceTurnFamily setup deps duration leaks bound profile who event turns)).policy past
        view :=
  sourceServiceTurnPolicy_turn_reference setup leaks bound turns timing
    (compileEventProfile setup.program profile) who past view event owned serving

section FirstTurn

variable {setup leaks}

/-- At the first turn no earlier recorded response saw the event as the
player's turn. -/
theorem sourceServiceTurn_first {owner : Player} {event : (serviceGraph setup deps).EventId}
    {past : List (serviceApplication setup deps duration leaks).PlayerEntry}
    {view : (serviceApplication setup deps duration leaks).PlayerView}
    (first : serviceTurn setup deps duration leaks owner event past view = some 0) :
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
theorem sourceServiceTurnPolicy_firstTurn_reference {bound :
    (serviceGraph setup deps).EventId → Nat}
    {turns : Nat} {reference : (serviceGraph setup deps).BehavioralProfile} {who : Player}
    {past : List (serviceApplication setup deps duration leaks).PlayerEntry}
    {view : (serviceApplication setup deps duration leaks).PlayerView}
    {event : (serviceGraph setup deps).EventId}
    (owned : (serviceGraph setup deps).actor? event = some who)
    (first : serviceTurn setup deps duration leaks who event past view = some 0) :
    serviceReferenceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps)
        reference who past view =
      serviceReferenceOpportunity setup deps duration leaks bound reference who event past view
        := by
  let app := serviceApplication setup deps duration leaks
  let family := serviceReferenceTurnFamily setup deps duration leaks bound reference who event turns
  have pin : (app.policyMixture (PMF.pure (0 : Fin (turns + 1))) family).posterior past =
      PMF.pure 0 := by
    simpa only [List.nil_append] using app.policyMixture_posterior_pure_append
      (PMF.pure (0 : Fin (turns + 1))) family [] past 0 rfl
  rw [sourceServiceTurnPolicy_turn_reference setup leaks bound turns _ reference who past view
    event owned
    (sourceServiceTurn_first first).1]
  change (app.policyMixture (PMF.pure (0 : Fin (turns + 1))) family).policy past view = _
  rw [app.policyMixture_policy, pin, PMF.pure_bind]
  exact app.turnScheduledPolicy_selected _ (0 : Fin (turns + 1)) _ _ past view first

/-- A pure first-turn timing retains its selection after every own transcript. -/
theorem sourceServiceTurnPolicy_firstTurn {bound : (serviceGraph setup deps).EventId → Nat}
    {turns : Nat} {profile : BehavioralProfile setup.program} {who : Player}
    {past : List (serviceApplication setup deps duration leaks).PlayerEntry}
    {view : (serviceApplication setup deps duration leaks).PlayerView}
    {event : (serviceGraph setup deps).EventId}
    (owned : (serviceGraph setup deps).actor? event = some who)
    (first : serviceTurn setup deps duration leaks who event past view = some 0) :
    serviceTurnPolicy setup deps duration leaks bound turns (firstTurnTiming setup turns deps)
        profile who past view =
      serviceCanonicalOpportunity setup deps duration leaks bound profile who event past view := by
  apply sourceServiceTurnPolicy_firstTurn_reference (deps := deps)
    (reference := compileEventProfile setup.program profile) <;> assumption


/-- A pure first-turn client is silent at every later turn at the event. -/
theorem sourceServiceTurnPolicy_laterTurn_reference {bound :
    (serviceGraph setup deps).EventId → Nat}
    {turns : Nat} {reference : (serviceGraph setup deps).BehavioralProfile} {who : Player}
    {past : List (serviceApplication setup deps duration leaks).PlayerEntry}
    {view : (serviceApplication setup deps duration leaks).PlayerView}
    {event : (serviceGraph setup deps).EventId}
    (owned : (serviceGraph setup deps).actor? event = some who)
    (serving : view.application.publicView.ownTurn? who = some event)
    (later : serviceTurn setup deps duration leaks who event past view ≠ some 0) :
    serviceReferenceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps)
        reference who past view = PMF.pure ⟨none⟩ := by
  let app := serviceApplication setup deps duration leaks
  let family := serviceReferenceTurnFamily setup deps duration leaks bound reference who event turns
  have pin : (app.policyMixture (PMF.pure (0 : Fin (turns + 1))) family).posterior past =
      PMF.pure 0 := by
    simpa only [List.nil_append] using app.policyMixture_posterior_pure_append
      (PMF.pure (0 : Fin (turns + 1))) family [] past 0 rfl
  rw [sourceServiceTurnPolicy_turn_reference setup leaks bound turns _ reference who past view
    event owned
    serving]
  change (app.policyMixture (PMF.pure (0 : Fin (turns + 1))) family).policy past view = _
  rw [app.policyMixture_policy, pin, PMF.pure_bind]
  exact app.turnScheduledPolicy_unselected _ (some (0 : Fin (turns + 1))) _ _ past view
    (fun slot selected => by cases selected; exact later)

/-- A pure first-turn client is silent at every later turn at the event. -/
theorem sourceServiceTurnPolicy_laterTurn {bound : (serviceGraph setup deps).EventId → Nat}
    {turns : Nat} {profile : BehavioralProfile setup.program} {who : Player}
    {past : List (serviceApplication setup deps duration leaks).PlayerEntry}
    {view : (serviceApplication setup deps duration leaks).PlayerView}
    {event : (serviceGraph setup deps).EventId}
    (owned : (serviceGraph setup deps).actor? event = some who)
    (serving : view.application.publicView.ownTurn? who = some event)
    (later : serviceTurn setup deps duration leaks who event past view ≠ some 0) :
    serviceTurnPolicy setup deps duration leaks bound turns (firstTurnTiming setup turns deps)
        profile who past view = PMF.pure ⟨none⟩ := by
  apply sourceServiceTurnPolicy_laterTurn_reference (deps := deps)
    (reference := compileEventProfile setup.program profile) <;> assumption

end FirstTurn

theorem firstTurnTiming_deferral {deps : setup.dataflowGraph.Dependencies} (turns : Nat)
    (event : (serviceGraph setup deps).EventId) :
    (firstTurnTiming setup turns deps).deferral event = 0 := by
  unfold TurnTiming.deferral
  split
  · rfl
  · simp [firstTurnTiming]

@[simp]
theorem firstTurnTiming_deferralError {deps : setup.dataflowGraph.Dependencies} (turns : Nat) :
    (firstTurnTiming setup turns deps).deferralError = 0 := by
  simp [TurnTiming.deferralError, firstTurnTiming_deferral]

variable {setup leaks} in
/-- A client depends only on its owner's graph policy. -/
theorem serviceReferenceTurnPolicy_eq_of_owner
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns deps)
    (left right : (serviceGraph setup deps).BehavioralProfile) (owner : Player)
    (same : left owner = right owner) :
    serviceReferenceTurnPolicy setup deps duration leaks bound turns timing left owner =
      serviceReferenceTurnPolicy setup deps duration leaks bound turns timing right owner := by
  have policies : serviceReferencePolicy setup deps duration leaks left owner =
      serviceReferencePolicy setup deps duration leaks right owner := by
    funext past view
    simp only [serviceReferencePolicy, same]
  have opportunities (event : (serviceGraph setup deps).EventId) :
      serviceReferenceOpportunity setup deps duration leaks bound left owner event =
        serviceReferenceOpportunity setup deps duration leaks bound right owner event := by
    funext past view
    simp only [serviceReferenceOpportunity, policies]
  have families (event : (serviceGraph setup deps).EventId) :
      serviceReferenceTurnFamily setup deps duration leaks bound left owner event turns =
        serviceReferenceTurnFamily setup deps duration leaks bound right owner event turns := by
    funext slot
    simp only [serviceReferenceTurnFamily, opportunities]
  funext past view
  simp only [serviceReferenceTurnPolicy, families]

end Generic

end Vegas

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

/-- First-turn clients agree whenever their ready graph kernels agree. -/
theorem serviceReferenceTurnPolicy_eq_of_ready_kernels
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (left right : (serviceGraph setup deps).BehavioralProfile) (who : Player)
    (past : List (serviceApplication setup deps duration leaks).PlayerEntry)
    (view : (serviceApplication setup deps duration leaks).PlayerView)
    (same : ∀ event, view.application.publicView.EventReady event →
      ∀ actor observation active,
        left who event actor observation active = right who event actor observation active) :
    serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) left who past view =
      serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) right who past view := by
  classical
  have policies : serviceReferencePolicy setup deps duration leaks left who past view =
      serviceReferencePolicy setup deps duration leaks right who past view := by
    unfold serviceReferencePolicy
    split
    · cases serving : view.application.publicView.ownTurn? who with
      | none => simp only
      | some event =>
          simp only
          split
          · rename_i actor
            split
            · rfl
            · rename_i active
              rw [same event (view.application.publicView.ownTurn?_spec who event serving).1
                actor _ active]
          · rfl
    · rfl
  cases serving : view.application.publicView.ownTurn? who with
  | none => simp only [serviceReferenceTurnPolicy, serving]
  | some event =>
      have actor := (view.application.publicView.ownTurn?_spec who event serving).2
      by_cases first : serviceTurn setup deps duration leaks who event past view = some 0
      · rw [sourceServiceTurnPolicy_firstTurn_reference actor first,
          sourceServiceTurnPolicy_firstTurn_reference actor first]
        unfold serviceReferenceOpportunity
        rw [policies]
      · rw [sourceServiceTurnPolicy_laterTurn_reference actor serving first,
          sourceServiceTurnPolicy_laterTurn_reference actor serving first]

end Vegas
