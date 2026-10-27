/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.IntendedGame
import GameTheory.Math.Probability.Conditioning

/-! # Conditioning the actual source initializer

Conditioning changes only the setup law. Source states, observations, menus and
post-initialization transition kernels are retained. The initialized source
law reconstructs by mixing the conditional source laws against the original
signal marginal. No signal is added to any player or scheduler observation.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open scoped ENNReal

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  {Signal : Type*} (signal : State L setup.context → Signal) (value : Signal)

/-- Restrict the existing initializer to a signal fiber. Unsupported fibers
retain the original law, matching the total fiber-posterior convention. -/
def conditionInitial : Setup (Player := Player) (L := L) :=
  { setup with initialLaw := fiberPosterior setup.initialLaw signal value }

@[simp] theorem conditionInitial_protocolObserve (who : Player) (state : setup.ProtocolState) :
    (setup.conditionInitial signal value).protocolObserve who state =
      setup.protocolObserve who state := rfl

@[simp] theorem conditionInitial_intendedMenu (who : Player) (view : setup.ProtocolView who) :
    (setup.conditionInitial signal value).intendedMenu who view =
      setup.intendedMenu who view := by
  cases view <;> rfl

/-- Only the initial chance transition depends on the conditioned law. -/
@[simp] theorem conditionInitial_protocolStep_some
    (state : SourceProgram.ProtocolState setup.program)
    (joint : Player → Option (OwnAction Player L)) :
    (setup.conditionInitial signal value).protocolStep (some state) joint =
      setup.protocolStep (some state) joint := rfl

/-- A positive conditional fiber introduces no new initial draw. -/
theorem conditionInitial_support_subset
    (supported : value ∈ (setup.initialLaw.map signal).support) :
    (setup.conditionInitial signal value).initialLaw.support ⊆ setup.initialLaw.support := by
  intro initial member
  exact (mem_support_fiberPosterior supported member).2

/-- Every conditional source transition is also possible in the original
source protocol. The only nontrivial case is the initializer. -/
theorem conditionInitial_protocolStep_support
    (supported : value ∈ (setup.initialLaw.map signal).support)
    (state : setup.ProtocolState) (joint : Player → Option (OwnAction Player L)) :
    ((setup.conditionInitial signal value).protocolStep state joint).support ⊆
      (setup.protocolStep state joint).support := by
  cases state with
  | none =>
      intro next member
      obtain ⟨initial, present, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      exact (PMF.mem_support_map_iff _ _ _).mpr
        ⟨initial, setup.conditionInitial_support_subset signal value supported present, rfl⟩
  | some state => exact Set.Subset.rfl

/-- The conditional initializer scales supported source atoms by the marginal
mass of the conditioning signal, without changing their typed data. -/
theorem conditionInitial_initialLaw_scale
    (supported : value ∈ (setup.initialLaw.map signal).support)
    (initial : State L setup.context) (same : signal initial = value) :
    (setup.initialLaw.map signal) value *
        (setup.conditionInitial signal value).initialLaw initial = setup.initialLaw initial := by
  classical
  change (setup.initialLaw.map signal) value *
    fiberPosterior setup.initialLaw signal value initial = _
  rw [fiberPosterior_disintegrate setup.initialLaw signal value supported initial]
  exact Set.indicator_of_mem
    (show initial ∈ {initial | signal initial = value} from same)
    (setup.initialLaw : State L setup.context → ℝ≥0∞)

/-- Mixing the actual source laws of the conditional setups reconstructs the
original source law for every source behavioral profile. -/
theorem run_conditionInitial_reconstruct (profile : BehavioralProfile setup.program) :
    (setup.initialLaw.map signal).bind
        (fun value => (setup.conditionInitial signal value).run profile) =
      setup.run profile := by
  change (setup.initialLaw.map signal).bind
    (fun value => (fiberPosterior setup.initialLaw signal value).bind
      (fun initial => SourceProgram.run setup.program profile initial)) = _
  rw [← PMF.bind_bind, fiberPosterior_reconstruct]
  rfl

/-- Conditional intended traces map to genuine intended traces of the same
program. Initial support restricts, while all later legal transitions agree. -/
def conditionInitial_trace (setup : Setup (Player := Player) (L := L))
    {Signal : Type*} (signal : State L setup.context → Signal) (value : Signal)
    (supported : value ∈ (setup.initialLaw.map signal).support) :
    ∀ {state : setup.ProtocolState},
      (setup.conditionInitial signal value).intendedProtocol.Trace state →
        setup.intendedProtocol.Trace state
  | _, .start => .start
  | _, .extend prior joint legal realized =>
      .extend (setup.conditionInitial_trace signal value supported prior) joint legal
        (setup.conditionInitial_protocolStep_support signal value supported _ _ realized)

@[simp] theorem conditionInitial_trace_length
    (setup : Setup (Player := Player) (L := L)) {Signal : Type*}
    (signal : State L setup.context → Signal) (value : Signal)
    (supported : value ∈ (setup.initialLaw.map signal).support) :
    ∀ {state : setup.ProtocolState}
      (trace : (setup.conditionInitial signal value).intendedProtocol.Trace state),
      (setup.conditionInitial_trace signal value supported trace).length = trace.length
  | _, .start => rfl
  | _, .extend prior _ _ _ =>
      congrArg (· + 1) (setup.conditionInitial_trace_length signal value supported prior)

/-- The source history map retains the exact typed program state and actions;
only proofs of initial reachability change. -/
def conditionInitial_history
    (supported : value ∈ (setup.initialLaw.map signal).support)
    (history : (setup.conditionInitial signal value).intendedProtocol.History) :
    setup.intendedProtocol.History :=
  ⟨history.state, setup.conditionInitial_trace signal value supported history.trace⟩

@[simp] theorem conditionInitial_history_state
    (supported : value ∈ (setup.initialLaw.map signal).support)
    (history : (setup.conditionInitial signal value).intendedProtocol.History) :
    (setup.conditionInitial_history signal value supported history).state = history.state := rfl

/-- The mapped conditional history exposes exactly the original local source
observation. It does not make the conditioning signal public. -/
theorem conditionInitial_history_observed
    (supported : value ∈ (setup.initialLaw.map signal).support)
    (history : (setup.conditionInitial signal value).intendedProtocol.History) (who : Player) :
    setup.intendedModel.infoOf who
        (setup.conditionInitial_history signal value supported history).trace =
      (setup.conditionInitial signal value).intendedModel.infoOf who history.trace := by
  obtain ⟨state, trace⟩ := history
  cases trace <;> rfl

end Vegas.SourceProgram.Setup
