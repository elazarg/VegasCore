/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSureFailure
import Vegas.Game.OnePacketPrescribedSupport

/-! # The pending event completes next

The event graph of a setup is sequentialized, so a cut has at most one ready
event (`Vegas.ready_unique`). Every configuration step either stutters or
completes a ready event, so a run from a configuration whose only ready event
is `event` either never leaves it or first completes `event`, by one step of
`event` itself; no other event completes or fails before it
(`Vegas.ConfigReaches.first_step_of_ready_unique`).

At every history of an information state of `who` with a pending event, that
event is ready on the current configuration and is its only ready event
(`Vegas.pendingEvent_ready_unique`). So, under a scheduler that completes play,
every terminal continuation of such a history, whatever anyone plays, reaches
its final configuration through a first step that completes the pending event
(`Vegas.pendingEvent_completes_next`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- **The only ready event completes first.** A run from a configuration
whose only ready event is `event` either stays at that configuration or first
takes a step of `event`, from whose result it continues. -/
theorem ConfigReaches.first_step_of_ready_unique {before after : (graph setup).Config}
    (reach : ConfigReaches setup before after) {event : (graph setup).EventId}
    (only : ∀ other, before.cut.Ready other → other = event) :
    after = before ∨ ∃ (ready : before.cut.Ready event) (action : (graph setup).Action event),
      ∃ middle ∈ (before.step event ready action).support, ConfigReaches setup middle after := by
  induction reach using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl rfl
  | head step rest next =>
      rename_i start middle
      rcases step with same | ⟨other, ready, action, member⟩
      · subst same
        exact next only
      · obtain rfl := only other ready
        exact Or.inr ⟨ready, action, middle, member, rest⟩

/-- One protocol transition from an initialized state reaches an initialized
state by one configuration step. -/
private theorem transition_reaches (initial : PMF (application setup leaks).State)
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    (before : (application setup leaks).Control) (after : (application setup leaks).ProtocolState)
    (joint : Player → Option (application setup leaks).Action)
    (reached : after ∈ ((application setup leaks).transition initial horizon scheduler
      (some before) joint).support) :
    ∃ next, after = some next ∧ ConfigStep setup before.execution.application.config
      next.execution.application.config := by
  have stays : ∃ next, after = some next := by
    rcases before with ⟨remaining, current, execution⟩
    cases current with
    | some who => exact ⟨_, (PMF.mem_support_pure_iff _ _).mp reached⟩
    | none =>
        cases remaining with
        | zero => exact ⟨_, (PMF.mem_support_pure_iff _ _).mp reached⟩
        | succ remaining =>
            obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
            obtain ⟨next, _, same⟩ := PMF.support_map .. ▸ moved
            exact ⟨_, same.symm⟩
  obtain ⟨next, rfl⟩ := stays
  exact ⟨next, rfl, transition_configStep initial horizon scheduler before next joint reached⟩

section OnePacket

variable [Fintype Player] (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

/-- **The pending event is the only ready event.** At a history of the
one-packet game whose information for `who` has `event` pending, the state is a
control at which `event` is ready, and every ready event is `event`. -/
theorem pendingEvent_ready_unique {who : Player}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who (some (past, view)) = some event)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    (infoEq : ((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
      horizon scheduler).infoOf who history.trace = some (past, view)) :
    ∃ control, history.state = some control ∧
      control.execution.application.config.cut.Ready event ∧
      ∀ other, control.execution.application.config.cut.Ready other → other = event := by
  let app := application setup leaks
  let menu := bounds.onePacketMenu (runtime setup) leaks
  obtain ⟨turn, _, _, _⟩ := pendingEvent_spec pending
  have observed : app.observe who history.state = some (past, view) :=
    (menu.info (initialLaw setup) horizon scheduler who history.trace).symm.trans infoEq
  generalize history.state = state at observed ⊢
  rcases state with _ | ⟨remaining, actor, execution⟩
  · simp [ReactiveApplication.observe] at observed
  by_cases active : actor = some who
  swap
  · simp [ReactiveApplication.observe, active] at observed
  subst active
  simp only [ReactiveApplication.observe, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
    at observed
  obtain ⟨pastEq, viewEq⟩ := observed
  subst pastEq
  subst viewEq
  have turnExec : execution.application.publicView.ownTurn? who = some event := turn
  have ready : execution.application.config.cut.Ready event :=
    (execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event turnExec).1
  exact ⟨_, rfl, ready, fun other otherReady => ready_unique _ otherReady ready⟩

/-- **The pending event completes next.** Under a scheduler that completes play,
let the information of `who` at a history of the one-packet game have `event`
pending. Every terminal continuation of the history, under any players, ends
at a control whose configuration is reached from the history's configuration
by a first step of `event`: no other event completes or fails before it. -/
theorem pendingEvent_completes_next
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ who, ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    {who : Player} {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who (some (past, view)) = some event)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    (infoEq : ((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
      horizon scheduler).infoOf who history.trace = some (past, view)) :
    ∃ control, history.state = some control ∧
      ∀ final ∈ (((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
          horizon scheduler).runBehavioralTerminalFrom certificate players history).support,
        ∃ finalControl, final.state = some finalControl ∧
          ∃ (ready : control.execution.application.config.cut.Ready event)
            (action : (graph setup).Action event),
            ∃ middle ∈ (control.execution.application.config.step event ready action).support,
              ConfigReaches setup middle finalControl.execution.application.config := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  obtain ⟨control, current, ready, only⟩ :=
    pendingEvent_ready_unique bounds horizon scheduler pending history infoEq
  refine ⟨control, current, fun final supported => ?_⟩
  have reaches := (menu.information (initialLaw setup) horizon
    scheduler).runBehavioralTerminalFrom_support_closed certificate players
    (fun state => ∃ next, state = some next ∧ ConfigReaches setup
      control.execution.application.config next.execution.application.config)
    (fun state joint _ target holds reached => by
      obtain ⟨before, rfl, reach⟩ := holds
      obtain ⟨next, rfl, step⟩ := transition_reaches (initialLaw setup) horizon scheduler before
        target joint reached
      exact ⟨next, rfl, reach.tail step⟩)
    history ⟨control, current, Relation.ReflTransGen.refl⟩ final supported
  obtain ⟨finalControl, state, reach⟩ := reaches
  refine ⟨finalControl, state, ?_⟩
  rcases ConfigReaches.first_step_of_ready_unique reach only with same | first
  · have stopped := (menu.information (initialLaw setup) horizon
      scheduler).runBehavioralTerminalFrom_support_terminal certificate players history final
      supported
    rw [state] at stopped
    have trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
        (some finalControl) :=
      state ▸ menu.toRawTrace (initialLaw setup) horizon scheduler final.trace
    have terminal := completes finalControl trace stopped
    have done : event ∈ finalControl.execution.application.config.cut.completed := by
      rw [terminal]
      exact Finset.mem_univ _
    rw [same] at done
    exact (ready.1 done).elim
  · exact first

end OnePacket

end Vegas
