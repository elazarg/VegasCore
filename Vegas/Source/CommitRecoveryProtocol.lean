/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryState
import Vegas.Source.SetupProtocol

/-! # Source execution with automatic commitment-phase recovery -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId}

namespace CommitRecoveryState

def Active {program : SourceProgram Player L Γ O} (state : CommitRecoveryState program)
    (who : Player) : Prop :=
  ProtocolState.actor program state.point = some who ∧ who ∉ state.excluded

def available {program : SourceProgram Player L Γ O} (state : CommitRecoveryState program)
    (who : Player) : Set (CommitRecoveryMove Player L) :=
  ProtocolView.recoveryAvailable who program (ProtocolState.observe who program state.point)

theorem progress {program : SourceProgram Player L Γ O} (state : CommitRecoveryState program) :
    ∃ joint, IsLegalJoint state.Active state.available joint := by
  classical
  obtain ⟨joint, legal⟩ := ProtocolState.progress program (CommitmentInterface.forfeiture program)
    state.point
  refine ⟨fun who => if who ∈ state.excluded then none else
    (joint who).map (fun action => (⟨action, false⟩ : CommitRecoveryMove Player L)), ?_⟩
  intro who
  have offered := legal who
  by_cases excluded : who ∈ state.excluded
  · simp only [excluded, ↓reduceIte]
    exact fun active => active.2 excluded
  · simp only [excluded, ↓reduceIte]
    cases chosen : joint who with
    | none =>
        rw [chosen] at offered
        exact fun active => offered ((ProtocolState.actor_observe_eq _ _ _).trans active.1)
    | some action =>
        rw [chosen] at offered
        refine ⟨⟨(ProtocolState.actor_observe_eq _ _ _).symm.trans offered.1, excluded⟩,
          offered.2, ?_⟩
        dsimp only
        split
        · intro impossible
          cases impossible
        · rfl

end CommitRecoveryState

/-- Every excluded owner is automatic; the next commitment attempt starts only
after the whole current block has closed. -/
def commitRecoveryProtocol (program : SourceProgram Player L Γ O)
    (initial : Config Player L Γ) : ExecutionProtocol Player where
  State := CommitRecoveryState program
  Action _ := CommitRecoveryMove Player L
  init := CommitRecoveryState.atPoint (ProtocolState.entry program initial) ∅ 0
  active := CommitRecoveryState.Active
  available := CommitRecoveryState.available
  terminal state := ProtocolState.terminal program state.point
  step state joint := state.step joint.1
  progress state _ := state.progress

namespace Setup

/-- A single private setup draw precedes all phase attempts. Retries never
resample the setup or erase its private inputs. -/
def commitRecoveryProtocol (setup : Setup (Player := Player) (L := L)) :
    ExecutionProtocol Player where
  State := Option (CommitRecoveryState setup.program)
  Action _ := CommitRecoveryMove Player L
  init := none
  active state who := state.elim False (fun state => state.Active who)
  available state who := state.elim ∅ (fun state => state.available who)
  terminal state := state.elim False (fun state => ProtocolState.terminal setup.program state.point)
  step state joint := match state with
    | none => setup.initialLaw.map fun inputs =>
        some (CommitRecoveryState.atPoint
          (ProtocolState.entry setup.program (setup.initialConfig inputs)) ∅ 0)
    | some current => (current.step joint.1).map some
  progress state _ := by
    cases state with
    | none => exact ⟨fun _ => none, fun _ impossible => impossible⟩
    | some current => exact current.progress

/-- The one setup draw and all retries fit this source instruction budget. -/
def commitRecoveryRank [Fintype Player] (setup : Setup (Player := Player) (L := L))
    (state : setup.commitRecoveryProtocol.State) : Nat :=
  state.elim ((Fintype.card Player + 1) * (instructionCount setup.program + 1))
    CommitRecoveryState.potential

theorem commitRecoveryRank_step [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    {before after : setup.commitRecoveryProtocol.State}
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal before joint)
    (supported : after ∈ (setup.commitRecoveryProtocol.step before ⟨joint, legal⟩).support) :
    setup.commitRecoveryRank after < setup.commitRecoveryRank before := by
  cases before with
  | none =>
      obtain ⟨inputs, _member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      simp only [commitRecoveryRank, Option.elim_some, Option.elim_none,
        CommitRecoveryState.potential,
        CommitRecoveryState.atPoint, Finset.card_empty, Nat.sub_zero,
        ProtocolState.remaining_entry]
      nlinarith
  | some current =>
      obtain ⟨next, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact current.step_potential_lt joint next legal.1 member

theorem commitRecovery_generation_bound
    (setup : Setup (Player := Player) (L := L))
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    ∀ current, state = some current → current.generation ≤ current.entryExcluded.card := by
  induction trace with
  | start => intro current impossible; cases impossible
  | @extend before after prior joint _ supported ih =>
      intro current equality
      cases before with
      | none =>
          obtain ⟨inputs, _member, target⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          have same := Option.some.inj (target.trans equality)
          subst current
          exact Nat.zero_le _
      | some previous =>
          obtain ⟨next, member, target⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          have same := Option.some.inj (target.trans equality)
          subst current
          exact previous.step_generation_bound (ih previous rfl) joint next member

theorem commitRecovery_history_budget [Fintype Player]
    (setup : Setup (Player := Player) (L := L)) :
    ∀ {state : setup.commitRecoveryProtocol.State}
      (trace : setup.commitRecoveryProtocol.Trace state),
      trace.length + setup.commitRecoveryRank state ≤
        (Fintype.card Player + 1) * (instructionCount setup.program + 1)
  | _, .start => by
      change 0 + ((Fintype.card Player + 1) * (instructionCount setup.program + 1)) ≤ _
      omega
  | _, .extend prior joint legal supported => by
      have earlier := setup.commitRecovery_history_budget prior
      have consumed := setup.commitRecoveryRank_step joint legal supported
      simp only [Trace.length]
      omega

theorem commitRecoveryProtocol_bounded [Fintype Player]
    (setup : Setup (Player := Player) (L := L)) :
    setup.commitRecoveryProtocol.BoundedHorizon
      ((Fintype.card Player + 1) * (instructionCount setup.program + 1)) := by
  intro state trace enough
  have budget := setup.commitRecovery_history_budget trace
  have zero : setup.commitRecoveryRank state = 0 := by omega
  cases state with
  | none =>
      simp only [commitRecoveryRank, Option.elim_none] at zero
      have positive := Nat.mul_pos (Nat.zero_lt_succ (Fintype.card Player))
        (Nat.zero_lt_succ (instructionCount setup.program))
      nlinarith
  | some current =>
      apply (ProtocolState.remaining_zero_iff_terminal setup.program current.point).mp
      simp only [commitRecoveryRank, Option.elim_some, CommitRecoveryState.potential,
        Nat.add_eq_zero_iff] at zero
      exact zero.2

end Setup
end Vegas.SourceProgram
