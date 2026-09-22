/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProtocolEvaluation
import Vegas.Source.Setup

/-! # Private setup in the source protocol

One initial chance step draws the existing setup law. It has no strategic
owner and emits only each player's source view. Subsequent transitions are
exactly the source protocol steps. A history after a private draw need not be
a proper subgame root: information sets range across all supported draws.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

def initialConfig (setup : Setup (Player := Player) (L := L))
    (state : State L setup.context) : Config Player L setup.context :=
  ⟨state, [], Revelations.initial setup.context, fun _ => []⟩

/-- `none` is the single position before setup; `some` retains a complete
source position after the draw. The setup is never sampled again. -/
abbrev ProtocolState (setup : Setup (Player := Player) (L := L)) :=
  Option (SourceProgram.ProtocolState setup.program)

abbrev ProtocolView (setup : Setup (Player := Player) (L := L)) (who : Player) :=
  Option (SourceProgram.ProtocolView who setup.program)

def protocolObserve (setup : Setup (Player := Player) (L := L)) (who : Player)
    (state : setup.ProtocolState) : setup.ProtocolView who :=
  state.map (SourceProgram.ProtocolState.observe who setup.program)

def protocolMenu (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) (who : Player) :
    setup.ProtocolView who → Option (OwnAction Player L) → Prop
  | none, choice => choice = none
  | some view, choice => SourceProgram.ProtocolView.menu who setup.program admission view choice

def protocolStep (setup : Setup (Player := Player) (L := L)) :
    setup.ProtocolState → (Player → Option (OwnAction Player L)) → FinDist setup.ProtocolState
  | none, _ => setup.initialLaw.map
      (fun initial => some (SourceProgram.ProtocolState.entry setup.program
        (setup.initialConfig initial)))
  | some state, joint => (SourceProgram.ProtocolState.step setup.program state joint).map some

def executionProtocol (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) : ExecutionProtocol Player where
  State := setup.ProtocolState
  Action _ := OwnAction Player L
  init := none
  active state who := (setup.protocolObserve who state).elim False
    (fun view => SourceProgram.ProtocolView.actor who setup.program view = some who)
  available state who := (setup.protocolObserve who state).elim ∅
    (SourceProgram.ProtocolView.available who setup.program admission)
  terminal state := state.elim False (SourceProgram.ProtocolState.terminal setup.program)
  step state joint := setup.protocolStep state joint.1
  progress state _ := by
    cases state with
    | none => exact ⟨fun _ => none, fun _ impossible => impossible⟩
    | some state =>
        obtain ⟨joint, legal⟩ := SourceProgram.ProtocolState.progress setup.program admission state
        refine ⟨joint, fun who => ?_⟩
        have member := legal who
        cases chosen : joint who <;>
          simpa only [SourceProgram.ProtocolView.menu, chosen, protocolObserve,
            Option.map_some, Option.elim_some] using member

theorem protocol_singleMover (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) (state : setup.ProtocolState)
    {first second : Player}
    (actsFirst : (setup.executionProtocol admission).active state first)
    (actsSecond : (setup.executionProtocol admission).active state second) : first = second := by
  cases state with
  | none => exact actsFirst.elim
  | some state =>
      exact Option.some.inj (actsFirst.symm.trans
        ((SourceProgram.ProtocolState.actor_observe setup.program state first second).trans
          actsSecond))

def protocolSignals (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) :
    InfoSignals (setup.executionProtocol admission) where
  PublicSignal := Unit
  PrivateSignal := setup.ProtocolView
  initialPublic := ()
  initialPrivate _ := none
  publicSignal _ := ()
  privateSignal who event := setup.protocolObserve who event.target
  InfoState := setup.ProtocolView
  initInfo _ view _ := view
  pushInfo _ _ _ view _ := view

theorem protocol_info (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) (who : Player) :
    ∀ {state} (trace : (setup.executionProtocol admission).Trace state),
      (setup.protocolSignals admission).infoOf who trace = setup.protocolObserve who state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

def informationModel (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) :
    InformationModel (setup.executionProtocol admission) where
  toInfoSignals := setup.protocolSignals admission
  menu who view := {choice | setup.protocolMenu admission who view choice}
  menu_adequate := by
    intro who state trace choice
    rw [protocol_info]
    cases state <;> cases choice <;> simp [protocolMenu, protocolObserve,
      SourceProgram.ProtocolView.menu, LegalOption, executionProtocol]

def protocolRemaining (setup : Setup (Player := Player) (L := L)) : setup.ProtocolState → Nat
  | none => instructionCount setup.program + 1
  | some state => SourceProgram.ProtocolState.remaining setup.program state

theorem protocol_remaining_step (setup : Setup (Player := Player) (L := L))
    (before after : setup.ProtocolState) (joint : Player → Option (OwnAction Player L))
    (running : ¬ before.elim False (SourceProgram.ProtocolState.terminal setup.program))
    (reached : after ∈ (setup.protocolStep before joint).support) :
    setup.protocolRemaining after + 1 = setup.protocolRemaining before := by
  cases before with
  | none =>
      obtain ⟨initial, _, rfl⟩ := FinDist.support_map .. ▸ reached
      simp [protocolRemaining]
  | some state =>
      obtain ⟨next, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      exact SourceProgram.ProtocolState.remaining_step setup.program state next joint
        running supported

theorem protocol_terminates (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) :
    (setup.executionProtocol admission).WellFoundedPlay := by
  apply wellFoundedPlay_of_rank setup.protocolRemaining
  intro before after step
  obtain ⟨joint, legal, reached⟩ := step
  have consumed := setup.protocol_remaining_step before after joint legal.1 reached
  omega

theorem protocol_history_length (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) :
    ∀ {state} (trace : (setup.executionProtocol admission).Trace state),
      trace.length + setup.protocolRemaining state = instructionCount setup.program + 1
  | _, .start => by simp [Trace.length, protocolRemaining, executionProtocol]
  | _, .extend (source := before) (target := after) prior joint legal reached => by
      have earlier := setup.protocol_history_length admission prior
      have consumed := setup.protocol_remaining_step before after joint legal.1 reached
      simp only [Trace.length]
      omega

theorem protocol_bounded (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) :
    (setup.executionProtocol admission).BoundedHorizon (instructionCount setup.program + 1) := by
  intro state trace enough
  have count := setup.protocol_history_length admission trace
  cases state with
  | none => simp only [protocolRemaining] at count; omega
  | some state =>
      exact (SourceProgram.ProtocolState.remaining_zero_iff_terminal setup.program state).mp
        (by change trace.length + SourceProgram.ProtocolState.remaining _ _ = _ at count; omega)

end Vegas.SourceProgram.Setup
