/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceAsyncStep

/-! # Turn timings cost at most their deferral weight, in every dependency mode

A turn-counted client draws, for each of its owned events, the turn index at
which it makes its source decision. From initialization, where no player has
recorded anything, the client is the mixture over that index of the clients
whose timing fixes it (`Vegas.serviceTurnPolicy_eq_timingMixture`): the
index only changes responses at the owner's turns at the event. Fixing one
event's index at the first turn therefore moves the law of every run by at most
the event's deferral weight, and fixing all of them moves it by at most the
total deferral weight. This holds for every scheduler, every initial law, every
dependency mode and deadline, and whatever policies some players follow
instead of their clients (`Vegas.overriddenTurnProfile_roundsFrom_bind_within`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- The turn-counted clients of a profile, with one player replaced. -/
abbrev deviatedTurnProfile (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (who : Player) (alternative : (serviceApplication setup mode deadline leaks).Policy) :
    Player → (serviceApplication setup mode deadline leaks).Policy :=
  Function.update (serviceTurnPolicy setup mode deadline leaks bound turns timing profile) who
    alternative

/-- Another player than the deviator keeps its client. -/
theorem deviatedTurnProfile_of_ne (bound : (serviceGraph setup mode).EventId → Nat)
    (turns : Nat) (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    {who owner : Player} (alternative : (serviceApplication setup mode deadline leaks).Policy)
    (foreign : owner ≠ who) :
    deviatedTurnProfile bound turns timing profile who alternative owner =
      serviceTurnPolicy setup mode deadline leaks bound turns timing profile owner :=
  Function.update_of_ne foreign _ _

/-- The timing whose turn index at one event is fixed. -/
def TurnTiming.fix {turns : Nat} (timing : TurnTiming setup turns mode)
    (event : (serviceGraph setup mode).EventId) (slot : Fin (turns + 1)) :
    TurnTiming setup turns mode := fun other who owned =>
  if other = event then PMF.pure slot else timing other who owned

/-- The timing whose turn indices at a list of events are fixed at the first
turn. -/
def TurnTiming.fixFirst {turns : Nat} (timing : TurnTiming setup turns mode) :
    List (serviceGraph setup mode).EventId → TurnTiming setup turns mode
  | [] => timing
  | event :: rest => TurnTiming.fixFirst (timing.fix event 0) rest

/-- Fixing every event at the first turn gives the first-turn timing. -/
theorem TurnTiming.fixFirst_all {turns : Nat} (timing : TurnTiming setup turns mode) :
    timing.fixFirst (List.finRange _) = firstTurnTiming setup turns mode := by
  have general : ∀ (events : List (serviceGraph setup mode).EventId)
      (current : TurnTiming setup turns mode) event who owned,
      (event ∈ events → (current.fixFirst events) event who owned = PMF.pure 0) ∧
        (event ∉ events → (current.fixFirst events) event who owned = current event who owned) := by
    intro events
    induction events with
    | nil => intro current event who owned; simp [TurnTiming.fixFirst]
    | cons head rest ih =>
        intro current event who owned
        simp only [TurnTiming.fixFirst, List.mem_cons, not_or]
        refine ⟨fun member => ?_, fun ⟨different, absent⟩ => ?_⟩
        · by_cases later : event ∈ rest
          · exact (ih _ event who owned).1 later
          · rw [(ih _ event who owned).2 later]
            rcases member with same | inRest
            · simp [TurnTiming.fix, same]
            · exact (later inRest).elim
        · rw [(ih _ event who owned).2 absent]
          simp [TurnTiming.fix, different]
  funext event who owned
  exact (general _ timing event who owned).1 (List.mem_finRange event)

/-- A fixed turn index changes no deferral weight but the event's own. -/
theorem TurnTiming.fix_deferral_of_ne {turns : Nat} (timing : TurnTiming setup turns mode)
    (event other : (serviceGraph setup mode).EventId) (slot : Fin (turns + 1))
    (different : other ≠ event) :
    (timing.fix event slot).deferral other = timing.deferral other := by
  unfold TurnTiming.deferral
  split
  · rfl
  · simp [TurnTiming.fix, different]

/-- Fixing a turn index changes no client at an input that is not a turn at
that event. -/
theorem serviceTurnPolicy_fix_of_not_turn (bound : (serviceGraph setup mode).EventId → Nat)
    {turns : Nat} (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (event : (serviceGraph setup mode).EventId) (slot : Fin (turns + 1)) (who : Player)
    (past : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (view : (serviceApplication setup mode deadline leaks).PlayerView)
    (other : view.application.publicView.ownTurn? who ≠ some event) :
    serviceTurnPolicy setup mode deadline leaks bound turns (timing.fix event slot) profile who
        past view =
      serviceTurnPolicy setup mode deadline leaks bound turns timing profile who past view := by
  unfold serviceTurnPolicy
  split
  · rfl
  · rename_i current turnEq
    have different : current ≠ event := fun same => other (by rw [turnEq, same])
    simp only [TurnTiming.fix, different, ↓reduceIte]

/-- Fixing the turn index of an event changes only its owner's client. -/
theorem serviceTurnPolicy_fix_of_not_owner (bound : (serviceGraph setup mode).EventId → Nat)
    {turns : Nat} (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (event : (serviceGraph setup mode).EventId) (slot : Fin (turns + 1)) (who : Player)
    (foreign : (serviceGraph setup mode).actor? event ≠ some who) :
    serviceTurnPolicy setup mode deadline leaks bound turns (timing.fix event slot) profile who =
      serviceTurnPolicy setup mode deadline leaks bound turns timing profile who := by
  funext past view
  unfold serviceTurnPolicy
  split
  · rfl
  · rename_i current _
    by_cases owned : (serviceGraph setup mode).actor? current = some who
    · have different : current ≠ event := fun same => foreign (same ▸ owned)
      simp only [owned, ↓reduceDIte, TurnTiming.fix, different, ↓reduceIte]
    · simp only [owned, ↓reduceDIte]

/-- **The client is its timing mixture at one event.** An owner's turn-counted
client is the mixture, over the event's turn index, of its clients with that
index fixed: the members respond alike except at the owner's turns at the
event, where they respond as the event's turn family. -/
theorem serviceTurnPolicy_eq_timingMixture (bound : (serviceGraph setup mode).EventId → Nat)
    {turns : Nat} (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (event : (serviceGraph setup mode).EventId) (owner : Player)
    (owned : (serviceGraph setup mode).actor? event = some owner) :
    ((serviceApplication setup mode deadline leaks).policyMixture (timing event owner owned)
      fun slot => serviceTurnPolicy setup mode deadline leaks bound turns (timing.fix event slot)
        profile owner).policy =
      serviceTurnPolicy setup mode deadline leaks bound turns timing profile owner := by
  let app := serviceApplication setup mode deadline leaks
  funext past view
  apply app.policyMixture_policy_of_region (timing event owner owned) _
    (serviceTurnFamily setup mode deadline leaks bound profile owner event turns) _
    (fun _ view => view.application.publicView.ownTurn? owner = some event)
  · intro slot past view serving
    rw [sourceServiceTurnPolicy_turn setup leaks bound turns _ profile owner past view event owned
      serving, app.policyMixture_policy]
    have fixed : (app.policyMixture ((timing.fix event slot) event owner owned)
        (serviceTurnFamily setup mode deadline leaks bound profile owner event turns)).posterior
          past = PMF.pure slot := by
      have start := app.policyMixture_posterior_pure_append
        ((timing.fix event slot) event owner owned)
        (serviceTurnFamily setup mode deadline leaks bound profile owner event turns) [] past slot
        (by simp [TurnTiming.fix]; rfl)
      simpa only [List.nil_append] using start
    rw [fixed, PMF.pure_bind]
  · intro slot past view other
    exact serviceTurnPolicy_fix_of_not_turn bound timing profile event slot owner past view other
  · intro past view other
    refine ⟨app.silentPolicy past view, fun slot => ?_⟩
    exact app.turnScheduledPolicy_of_none _ _ _ _ _ _
      (sourceServiceTurn_of_not_turn setup leaks owner event past view other)
  · intro past view serving
    exact sourceServiceTurnPolicy_turn setup leaks bound turns timing profile owner past view event
      owned serving

/-- The clients of a timing, with some players following other policies. -/
def overriddenTurnProfile (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (override : Player → Option (serviceApplication setup mode deadline leaks).Policy) :
    Player → (serviceApplication setup mode deadline leaks).Policy := fun who =>
  (override who).getD (serviceTurnPolicy setup mode deadline leaks bound turns timing profile who)

/-- **One event's timing costs at most its deferral weight.** From the
initial law, every run of the overridden clients, followed by any common
kernel, is within the event's deferral weight of the run with the event's turn
index fixed at the first turn. -/
theorem overriddenTurnProfile_fix_roundsFrom_bind_within {β : Type}
    (initial : PMF (EventGraphRuntime.State (serviceGraph setup mode)))
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler) (horizon : Nat)
    (bound : (serviceGraph setup mode).EventId → Nat) {turns : Nat}
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (override : Player → Option (serviceApplication setup mode deadline leaks).Policy)
    (event : (serviceGraph setup mode).EventId)
    (readout : (serviceApplication setup mode deadline leaks).Execution → PMF β) :
    PMF.WithinTV (timing.deferral event)
      (((serviceApplication setup mode deadline leaks).roundsFrom initial scheduler
        (overriddenTurnProfile bound turns timing profile override) horizon).bind readout)
      (((serviceApplication setup mode deadline leaks).roundsFrom initial scheduler
        (overriddenTurnProfile bound turns (timing.fix event 0) profile override) horizon).bind
          readout) := by
  let app := serviceApplication setup mode deadline leaks
  have nonneg := deferral_nonneg timing event
  cases owned : (serviceGraph setup mode).actor? event with
  | none =>
      have same : overriddenTurnProfile (deadline := deadline) (leaks := leaks) bound turns
          (timing.fix event 0) profile override =
          overriddenTurnProfile bound turns timing profile override := by
        funext who
        unfold overriddenTurnProfile
        rw [serviceTurnPolicy_fix_of_not_owner bound timing profile event 0 who
          (by rw [owned]; exact fun absurd => by cases absurd)]
      rw [same]
      exact (PMF.WithinTV.refl _).mono nonneg
  | some owner =>
      cases overridden : override owner with
      | some policy =>
          have same : overriddenTurnProfile (deadline := deadline) (leaks := leaks) bound turns
              (timing.fix event 0) profile override =
              overriddenTurnProfile bound turns timing profile override := by
            funext who
            unfold overriddenTurnProfile
            by_cases isOwner : who = owner
            · subst isOwner
              simp only [overridden, Option.getD_some]
            · rw [serviceTurnPolicy_fix_of_not_owner bound timing profile event 0 who
                (by rw [owned]; exact fun equal => isOwner (Option.some.inj equal).symm)]
          rw [same]
          exact (PMF.WithinTV.refl _).mono nonneg
      | none =>
          let base := overriddenTurnProfile (deadline := deadline) (leaks := leaks) bound turns
            timing profile override
          let member := fun slot : Fin (turns + 1) =>
            serviceTurnPolicy setup mode deadline leaks bound turns (timing.fix event slot) profile
              owner
          have fixed (slot : Fin (turns + 1)) :
              overriddenTurnProfile (deadline := deadline) (leaks := leaks) bound turns
                (timing.fix event slot) profile override =
                Function.update base owner (member slot) := by
            funext who
            by_cases isOwner : who = owner
            · subst isOwner
              simp only [Function.update_self, member, overriddenTurnProfile, overridden,
                Option.getD_none]
            · rw [Function.update_of_ne isOwner]
              simp only [base, overriddenTurnProfile]
              rw [serviceTurnPolicy_fix_of_not_owner bound timing profile event slot who
                (by rw [owned]; exact fun equal => isOwner (Option.some.inj equal).symm)]
          have mixed : base = Function.update base owner
              (app.policyMixture (timing event owner owned) member).policy := by
            funext who
            by_cases isOwner : who = owner
            · subst isOwner
              rw [Function.update_self, serviceTurnPolicy_eq_timingMixture bound timing profile
                event who owned]
              simp only [base, overriddenTurnProfile, overridden, Option.getD_none]
            · rw [Function.update_of_ne isOwner]
          rw [fixed 0]
          change PMF.WithinTV _ ((app.roundsFrom initial scheduler base horizon).bind readout) _
          unfold ReactiveApplication.roundsFrom
          rw [PMF.bind_bind, PMF.bind_bind]
          apply PMF.WithinTV.bind_right
          intro state _
          conv_lhs => rw [mixed]
          rw [← app.runRounds_policyMixture scheduler (timing event owner owned) member
            owner base horizon (ReactiveApplication.Execution.initial app state)]
          have prior : (app.policyMixture (timing event owner owned) member).posterior
              ((ReactiveApplication.Execution.initial app state).recall owner) =
                timing event owner owned :=
            app.policyMixture_posterior_of_agree _ _ app.silentPolicy _
              fun before entry member => by
                have empty := List.prefix_nil.mp member
                simp at empty
          rw [prior, PMF.bind_bind]
          apply PMF.WithinTV.of_bind_point (timing event owner owned) 0
          unfold TurnTiming.deferral
          split
          · rename_i absent
            rw [owned] at absent
            cases absent
          · rename_i who ownedWho
            have same : who = owner := Option.some.inj (ownedWho.symm.trans owned)
            subst same
            exact le_refl _

/-- **Every timing costs at most its total deferral weight.** From the
initial law, every run of the overridden clients of a timing, followed by any
common kernel, is within the total deferral weight of the run of the
overridden first-turn clients. -/
theorem overriddenTurnProfile_roundsFrom_bind_within {β : Type}
    (initial : PMF (EventGraphRuntime.State (serviceGraph setup mode)))
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler) (horizon : Nat)
    (bound : (serviceGraph setup mode).EventId → Nat) {turns : Nat}
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (override : Player → Option (serviceApplication setup mode deadline leaks).Policy)
    (readout : (serviceApplication setup mode deadline leaks).Execution → PMF β) :
    PMF.WithinTV (∑ event, timing.deferral event)
      (((serviceApplication setup mode deadline leaks).roundsFrom initial scheduler
        (overriddenTurnProfile bound turns timing profile override) horizon).bind readout)
      (((serviceApplication setup mode deadline leaks).roundsFrom initial scheduler
        (overriddenTurnProfile bound turns (firstTurnTiming setup turns mode) profile override)
          horizon).bind readout) := by
  have general : ∀ (events : List (serviceGraph setup mode).EventId), events.Nodup →
      ∀ current : TurnTiming setup turns mode,
      PMF.WithinTV ((events.map current.deferral).sum)
        (((serviceApplication setup mode deadline leaks).roundsFrom initial scheduler
          (overriddenTurnProfile bound turns current profile override) horizon).bind readout)
        (((serviceApplication setup mode deadline leaks).roundsFrom initial scheduler
          (overriddenTurnProfile bound turns (current.fixFirst events) profile override)
            horizon).bind readout) := by
    intro events
    induction events with
    | nil => intro _ current; simpa [TurnTiming.fixFirst] using PMF.WithinTV.refl _
    | cons event rest ih =>
        intro distinct current
        obtain ⟨absent, restDistinct⟩ := List.nodup_cons.mp distinct
        have step := overriddenTurnProfile_fix_roundsFrom_bind_within initial scheduler horizon
          bound current profile override event readout
        have later := ih restDistinct (current.fix event 0)
        have sameWeights : (rest.map (current.fix event 0).deferral).sum =
            (rest.map current.deferral).sum := by
          congr 1
          apply List.map_congr_left
          intro other member
          exact current.fix_deferral_of_ne event other 0 fun same => absent (same ▸ member)
        rw [sameWeights] at later
        simpa only [List.map_cons, List.sum_cons, TurnTiming.fixFirst] using step.trans later
  have all := general (List.finRange _) (List.nodup_finRange _) timing
  rw [timing.fixFirst_all, ← Fin.sum_univ_def] at all
  exact all

/-- **Honest timing coupling.** For every initial law and scheduler, the
turn-counted clients of a timing, run from initialization and followed by any
common kernel, are within the total deferral weight of the first-turn
clients. -/
theorem serviceTurnPolicy_roundsFrom_bind_within {β : Type}
    (initial : PMF (EventGraphRuntime.State (serviceGraph setup mode)))
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler) (horizon : Nat)
    (bound : (serviceGraph setup mode).EventId → Nat) {turns : Nat}
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (readout : (serviceApplication setup mode deadline leaks).Execution → PMF β) :
    PMF.WithinTV (∑ event, timing.deferral event)
      (((serviceApplication setup mode deadline leaks).roundsFrom initial scheduler
        (serviceTurnPolicy setup mode deadline leaks bound turns timing profile) horizon).bind
          readout)
      (((serviceApplication setup mode deadline leaks).roundsFrom initial scheduler
        (serviceTurnPolicy setup mode deadline leaks bound turns (firstTurnTiming setup turns mode)
          profile) horizon).bind readout) :=
  overriddenTurnProfile_roundsFrom_bind_within initial scheduler horizon bound timing profile
    (fun _ => none) readout

/-- **Deviated timing coupling.** For every initial law, scheduler and policy
of one deviating player, the deviated turn-counted clients of a timing, run
from initialization and followed by any common kernel, are within the total
deferral weight of the deviated first-turn clients. -/
theorem deviatedTurnProfile_roundsFrom_bind_within {β : Type}
    (initial : PMF (EventGraphRuntime.State (serviceGraph setup mode)))
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler) (horizon : Nat)
    (bound : (serviceGraph setup mode).EventId → Nat) {turns : Nat}
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (who : Player) (alternative : (serviceApplication setup mode deadline leaks).Policy)
    (readout : (serviceApplication setup mode deadline leaks).Execution → PMF β) :
    PMF.WithinTV (∑ event, timing.deferral event)
      (((serviceApplication setup mode deadline leaks).roundsFrom initial scheduler
        (deviatedTurnProfile bound turns timing profile who alternative) horizon).bind readout)
      (((serviceApplication setup mode deadline leaks).roundsFrom initial scheduler
        (deviatedTurnProfile bound turns (firstTurnTiming setup turns mode) profile who
          alternative) horizon).bind readout) := by
  have shape (current : TurnTiming setup turns mode) :
      deviatedTurnProfile bound turns current profile who alternative =
        overriddenTurnProfile (deadline := deadline) (leaks := leaks) bound turns current profile
          fun player => if player = who then some alternative else none := by
    funext player
    by_cases same : player = who
    · subst same
      simp [deviatedTurnProfile, overriddenTurnProfile]
    · simp [deviatedTurnProfile, overriddenTurnProfile, same]
  rw [shape, shape]
  exact overriddenTurnProfile_roundsFrom_bind_within initial scheduler horizon bound timing profile
    _ readout

end Vegas
