/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceReachedDecoding
import Vegas.Pending.ReactiveGraphSteps
import Vegas.Source.FailedBindingDeviation

/-! # Step-closed properties at actual native endpoints

Every supported native transition follows a finite path of the sole graph
executor, including automatic completions after public default. Source residuals
transport every step-closed source property along that path to the decoding of
its actual endpoint. Initialization and all subsequent transitions retain the
full source configuration and public default history without a second reader.
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

/-- A player owing a failure keeps owing it under every source step. -/
theorem owesFailure_stepClosed (who : Player) :
    StepClosed setup (ProtocolState.OwesFailure who setup.program) :=
  fun state joint target owed reached =>
    ProtocolState.owesFailure_step who setup.program state joint target owed reached

/-- A property holds at the decoding of a configuration at a prefix. -/
def DecodedHolds (property : ProtocolState setup.program → Prop) (rank : Nat)
    (config : (graph setup).Config) : Prop :=
  ∀ state, sourceServicePrefix? setup rank config = some state → property state

/-- One actual graph completion keeps a step-closed property at its decoded
source successor. The successor rank belongs only to this single completion. -/
theorem SourceResidual.decodedHolds_step
    {property : ProtocolState setup.program → Prop} (closed : StepClosed setup property)
    {rank : Nat} {before : (graph setup).Config}
    (residual : SourceResidual setup profile rank before)
    (holds : DecodedHolds property rank before)
    (event : (graph setup).EventId) (ready : before.cut.Ready event)
    (action : (graph setup).Action event) (after : (graph setup).Config)
    (member : after ∈ (before.step event ready action).support) :
    ∃ _next : SourceResidual setup profile (rank + 1) after,
      DecodedHolds property (rank + 1) after := by
  obtain ⟨successor, reached⟩ := residual.step event ready action after member
  refine ⟨successor, ?_⟩
  intro state decoded
  rw [successor.decode, Option.some.injEq] at decoded
  subst decoded
  exact closed _ _ _ (holds _ residual.decode) reached

/-- A finite actual graph path transports a source property to its actual
endpoint prefix, without a bound of one completion per native transition. -/
theorem SourceResidual.decodedHolds_path
    {property : ProtocolState setup.program → Prop} (closed : StepClosed setup property)
    {rank : Nat} {before after : (graph setup).Config}
    (residual : SourceResidual setup profile rank before)
    (holds : DecodedHolds property rank before)
    (path : Relation.ReflTransGen EventGraph.Config.Step before after) :
    ∃ next, Nonempty (SourceResidual setup profile next after) ∧
      DecodedHolds property next after := by
  induction path using Relation.ReflTransGen.head_induction_on generalizing rank with
  | refl => exact ⟨rank, ⟨residual⟩, holds⟩
  | @head current middle moved rest ih =>
      obtain ⟨event, ready, action, member⟩ := moved
      obtain ⟨next, valid⟩ := residual.decodedHolds_step closed holds event ready action middle
        member
      exact ih next valid

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
      exact residual.decodedHolds_path closed decoded
        (reactive_protocol_graph_steps runtime leaks initial horizon scheduler control next joint
          reached)

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
