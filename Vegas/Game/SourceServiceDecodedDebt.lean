/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceReachedDecoding

/-! # Step-closed properties read through the native decoding

Every native configuration reached under any players and any scheduler decodes
to a point of the source program at its completed prefix
(`Vegas.SourceResidual`). The decoding advances by one source step whenever the
native configuration completes an event (`Vegas.SourceResidual.step`), whatever
action completes it: a sample, any binding including a failed one, or any
disclosure decision. A property of source points closed under every source
step therefore persists along every native protocol transition, under arbitrary
responses and scheduler choices (`Vegas.decodedHolds_transition`).

A source debt is such a property
(`Vegas.SourceProgram.ProtocolState.indebted_step`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {profile : BehavioralProfile setup.program}

/-- A property of source points closed under every source step, whatever the
joint action. -/
def StepClosed (setup : Setup (Player := Player) (L := L))
    (property : ProtocolState setup.program → Prop) : Prop :=
  ∀ state joint target, property state →
    target ∈ (ProtocolState.step setup.program state joint).support → property target

/-- A property holds at the decoding of a configuration at a prefix. -/
def DecodedHolds (property : ProtocolState setup.program → Prop) (rank : Nat)
    (config : (graph setup).Config) : Prop :=
  ∀ state, sourceServicePrefix? setup rank config = some state → property state

/-- A configuration step keeps a step-closed property of the decoding, at
whichever prefix the step reaches. -/
theorem SourceResidual.decodedHolds_configStep
    {property : ProtocolState setup.program → Prop} (closed : StepClosed setup property)
    {rank : Nat} {before after : (graph setup).Config}
    (residual : SourceResidual setup profile rank before)
    (holds : DecodedHolds property rank before)
    (step : ConfigStep setup before after) {next : Nat} (ordered : after.cut.IsPrefix next) :
    DecodedHolds property next after := by
  rcases step with same | ⟨event, ready, action, member⟩
  · subst same
    rw [isPrefix_unique ordered residual.checkpoint.ordered]
    exact holds
  · have advanced : after.cut.IsPrefix (rank + 1) := by
      rw [before.step_cut event ready action after member]
      exact residual.checkpoint.ordered.complete_at event ready
        ((ready_iff_rank setup before rank residual.checkpoint.ordered event).mp ready)
    rw [isPrefix_unique ordered advanced]
    obtain ⟨successor, reached⟩ := residual.step event ready action after member
    intro state decoded
    rw [successor.decode, Option.some.injEq] at decoded
    subst decoded
    exact closed _ _ _ (holds _ residual.decode) reached

variable (setup runtime) in
/-- An initialized native protocol state whose configuration has a source
residual at a prefix where a step-closed property holds of its decoding. -/
def DecodedState (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (profile : BehavioralProfile setup.program)
    (property : ProtocolState setup.program → Prop) :
    (application setup runtime leaks).ProtocolState → Prop
  | none => False
  | some control => ∃ rank,
      Nonempty (SourceResidual setup profile rank control.execution.application.config) ∧
        DecodedHolds property rank control.execution.application.config

/-- One protocol transition changes the configuration by one configuration
step, under arbitrary responses and scheduler choices. -/
theorem transition_configStep
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    (initial : PMF (application setup runtime leaks).State) (horizon : Nat)
    (scheduler : (application setup runtime leaks).Scheduler)
    (before after : (application setup runtime leaks).Control)
    (joint : Player → Option (application setup runtime leaks).Action)
    (reached : some after ∈ ((application setup runtime leaks).transition initial horizon scheduler
      (some before) joint).support) :
    ConfigStep setup before.execution.application.config after.execution.application.config := by
  rcases before with ⟨remaining, current, execution⟩
  cases current with
  | some who =>
      cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
      exact Or.inl (runtime.reactive_respond_application leaks execution who _).1
  | none =>
      cases remaining with
      | zero =>
          cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
          exact Or.inl rfl
      | succ remaining =>
          obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          obtain ⟨next, supported, same⟩ := PMF.support_map .. ▸ moved
          cases Option.some.inj same
          exact environmentStep_configStep setup leaks execution next command supported

/-- **Decoded properties persist.** A step-closed property of the decoding of an
initialized native state holds after every protocol transition, under arbitrary
responses and scheduler choices. -/
theorem decodedHolds_transition
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {property : ProtocolState setup.program → Prop} (closed : StepClosed setup property)
    (initial : PMF (application setup runtime leaks).State) (horizon : Nat)
    (scheduler : (application setup runtime leaks).Scheduler)
    (before after : (application setup runtime leaks).ProtocolState)
    (joint : Player → Option (application setup runtime leaks).Action)
    (holds : DecodedState setup runtime leaks profile property before)
    (reached : after ∈ ((application setup runtime leaks).transition initial horizon scheduler
      before
      joint).support) :
    DecodedState setup runtime leaks profile property after := by
  cases before with
  | none => exact holds.elim
  | some control =>
      obtain ⟨rank, ⟨residual⟩, decoded⟩ := holds
      have stays : ∃ next, after = some next := by
        rcases control with ⟨remaining, current, execution⟩
        cases current with
        | some who => exact ⟨_, (PMF.mem_support_pure_iff _ _).mp reached⟩
        | none =>
            cases remaining with
            | zero => exact ⟨_, (PMF.mem_support_pure_iff _ _).mp reached⟩
            | succ remaining =>
                obtain ⟨command, _, moved⟩ :=
                  Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                obtain ⟨next, _, same⟩ := PMF.support_map .. ▸ moved
                exact ⟨_, same.symm⟩
      obtain ⟨next, rfl⟩ := stays
      have step := transition_configStep initial horizon scheduler control next joint reached
      rcases step.prefix rank residual.checkpoint.ordered with same | advanced
      · refine ⟨rank, residual.configStep step rank ?_, ?_⟩
        · rw [same]
          exact residual.checkpoint.ordered
        · exact residual.decodedHolds_configStep closed decoded step (by
            rw [same]
            exact residual.checkpoint.ordered)
      · exact ⟨rank + 1, residual.configStep step (rank + 1) advanced,
          residual.decodedHolds_configStep closed decoded step advanced⟩

/-- A step-closed source property initialized on every supported setup draw
holds at the decoding of every initialized menu history, for any scheduler. -/
theorem decodedState_history_of_stepClosed
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {property : ProtocolState setup.program → Prop} (closed : StepClosed setup property)
    (initialized : ∀ initial ∈ setup.initialLaw.support,
      property (ProtocolState.entry setup.program (Config.initial initial)))
    (menu : (application setup runtime leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (application setup runtime leaks).Scheduler) :
    ∀ {state} (_trace : (menu.protocol (initialLaw setup) horizon scheduler).Trace state)
      (control : (application setup runtime leaks).Control), state = some control →
      DecodedState setup runtime leaks profile property (some control) := by
  intro state trace
  induction trace with
  | start => intro _ current; cases current
  | @extend before after prior joint _ realized ih =>
      intro control current
      subst current
      cases before with
      | none =>
          change some control ∈ ((initialLaw setup).map fun state =>
            some ⟨horizon, none, ReactiveApplication.Execution.initial
              (application setup runtime leaks) state⟩).support at realized
          obtain ⟨state, supported, same⟩ := PMF.support_map .. ▸ realized
          cases Option.some.inj same
          obtain ⟨initial, member, rfl⟩ := PMF.support_map .. ▸ supported
          let residual := SourceResidual.initial setup profile initial
          refine ⟨0, ⟨residual⟩, fun point decoded => ?_⟩
          change sourceServicePrefix? setup 0 (EventGraphRuntime.State.initial
            (graph := graph setup) (setup.eventInputs initial)).config = some point at decoded
          rw [residual.decode, Option.some.injEq] at decoded
          subst decoded
          exact initialized initial member
      | some previous =>
          exact decodedHolds_transition closed (initialLaw setup) horizon scheduler
            (some previous) (some control) joint (ih previous rfl) realized

/-- A terminal cut is a prefix only of the full event count. -/
theorem isPrefix_eventCount_of_terminal {cut : (graph setup).order.Cut} {rank : Nat}
    (ordered : cut.IsPrefix rank) (terminal : cut.Terminal) :
    rank = (graph setup).order.eventCount := by
  apply le_antisymm ordered.1
  by_contra short
  push Not at short
  have completed : (⟨rank, short⟩ : Fin (graph setup).order.eventCount) ∈ cut.completed := by
    rw [terminal]
    exact Finset.mem_univ _
  exact Nat.lt_irrefl _ ((ordered.2 _).mp completed)

end Vegas
