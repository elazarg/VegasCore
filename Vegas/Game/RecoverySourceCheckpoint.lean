/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceCommitBlock
import Vegas.Compile.EventGraphSuffix
import Vegas.Compile.CompiledReadoutSuffix
import Vegas.Compile.ProtocolViewSuffix
import Vegas.Compile.EventGraphInputs
import Vegas.Source.ProtocolSuffix
import Vegas.Source.RegistryFailureExtension
import Vegas.Pending.PhaseApplication
import Vegas.Compile.EventGraphHistory
import Vegas.EventGraph.SequentialLaw

/-! # Reachable source recovery checkpoints at saved physical phase entries

Only the saved semantic entry is compared with a source program point. A live
concurrent cut may contain holes. Its existing native frontier invariants are
separate from this checkpoint, as is physical transcript correspondence.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A saved physical entry has one genuine reachable source recovery state,
with typed semantic values, source guard bookkeeping and effective history.
Static extra guards are retained through their exact failure extension. -/
structure RecoverySourceCheckpoint (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode)
    (state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)) where
  residual : ResidualProgram setup.program
  source : SourceProgram.Config Player L residual.context
  refs : ContextRefs (graphLayout setup.program) residual.context
  registry : Registry residual.context
  embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) residual.tail
  before : ContextRefsBefore refs embedding
  compiled : CompiledSuffix setup.program residual.tail refs source.revelations registry
    embedding before state.attempt.phase
  terminalAlignment : CompiledReadoutSuffix setup.program residual.tail refs embedding
  agrees : refs.Agrees source.state state.entry.native.config.store
  guards : Registry.FailureExtension source.registry registry source.state
  failures : Revelations.PreservesFailures source.revelations source.state
  unique : (residual.context.map Prod.fst).Nodup
  remaining : ∀ point, ProtocolState.remaining setup.program (residual.lift point) =
    ProtocolState.remaining residual.tail point
  actor : ∀ point, ProtocolState.actor setup.program (residual.lift point) =
    ProtocolState.actor residual.tail point
  atCommit : ∀ point, ProtocolState.atCommit setup.program (residual.lift point) =
    ProtocolState.atCommit residual.tail point
  owners : ∀ point, ProtocolState.commitOwners setup.program (residual.lift point) =
    ProtocolState.commitOwners residual.tail point
  commitEnd : ∀ point, ProtocolState.commitEnd setup.program (residual.lift point) =
    ProtocolState.commitEnd residual.tail point
  automatic : ∀ point,
    residual.lift (ProtocolState.automaticCommitBlock residual.tail point) =
      ProtocolState.automaticCommitBlock setup.program (residual.lift point)
  history : ∀ point, ProtocolState.history setup.program (residual.lift point) =
    ProtocolState.history residual.tail point
  withHistory : ∀ point past,
    residual.lift (ProtocolState.withHistory residual.tail point past) =
      ProtocolState.withHistory setup.program (residual.lift point) past
  step : ∀ point excluded joint,
    ProtocolState.recoveryStep setup.program (residual.lift point) excluded joint =
      (ProtocolState.recoveryStep residual.tail point excluded joint).map
        (fun result => (residual.lift result.1, result.2))
  menus : ∀ who point,
    ProtocolView.recoveryAvailable who setup.program
        (ProtocolState.observe who setup.program (residual.lift point)) =
      ProtocolView.recoveryAvailable who residual.tail
        (ProtocolState.observe who residual.tail point)
  readout : ∀ point, ProtocolState.readout setup.program (residual.lift point) =
    (ProtocolState.readout residual.tail point).map
      (cast (congrArg (State L) terminalAlignment.contextEq))
  trace : setup.commitRecoveryProtocol.Trace
    (some (CommitRecoveryState.atPoint
      (residual.lift (ProtocolState.entry residual.tail source)) state.entry.excluded
      state.generation))
  views : ProtocolViewSuffix setup.program residual.tail refs embedding residual.lift
  historyAlignment : state.entry.excluded = ∅ → source.history =
    decodeHistory setup.program (state.entry.native.config.history.map
      ((toEventGraph setup.program).fromModeCompletion mode))
  origin : ProtocolSuffix setup.program residual.tail residual.lift

namespace RecoverySourceCheckpoint

private theorem rawInitial_phase (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode)
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (initial : State L setup.context) :
    (⟨plan.phases, 0, ⟨EventGraphRuntime.State.initial (encodeInputs initial), ∅⟩,
      ⟨EventGraphRuntime.State.initial (encodeInputs initial), ∅⟩, []⟩ :
      PhaseRuntimeState ((toEventGraph setup.program).withMode mode)).attempt.phase = 0 := by
  cases phases : plan.phases with
  | nil =>
      have empty := plan.empty phases
      simp only [PhaseRuntimeState.attempt, List.head?_nil, Option.map_none,
        Option.getD_none, empty]
  | cons first rest =>
      have low := plan.first first (by rw [phases]; exact Option.mem_some_iff.mpr rfl)
      simpa only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
        Option.getD_some] using low

/-- The single supported setup draw provides the initial saved checkpoint
before the dispatcher services automatic phases. No setup is resampled. -/
def initial (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (initial : State L setup.context) (supported : initial ∈ setup.initialLaw.support) :
    RecoverySourceCheckpoint setup mode
      (⟨plan.phases, 0, ⟨EventGraphRuntime.State.initial (encodeInputs initial), ∅⟩,
        ⟨EventGraphRuntime.State.initial (encodeInputs initial), ∅⟩, []⟩ :
        PhaseRuntimeState ((toEventGraph setup.program).withMode mode)) where
  residual := ⟨setup.context, setup.obligations, setup.program, id⟩
  source := setup.initialConfig initial
  refs := ContextRefs.initial setup.context (outputLayout setup.program)
  registry := []
  embedding := outputEmbedding setup.program
  before := initialRefsBefore setup.program
  compiled := by
    rw [rawInitial_phase setup mode plan initial]
    exact CompiledSuffix.whole setup.program
  terminalAlignment := CompiledReadoutSuffix.initial setup.program
  agrees := initialConfig_agrees setup.program initial
  guards := Registry.FailureExtension.refl [] initial
  failures := Revelations.initial_preservesFailures initial
  unique := setup.namesNodup
  remaining := fun _ => rfl
  actor := fun _ => rfl
  atCommit := fun _ => rfl
  owners := fun _ => rfl
  commitEnd := fun _ => rfl
  automatic := fun _ => rfl
  history := fun _ => rfl
  withHistory := fun _ _ => rfl
  step := fun point excluded joint => (PMF.map_id _).symm
  menus := fun _ _ => rfl
  readout := fun point => by
    change _ = Option.map id _
    simp only [Option.map_id, id_eq]
  trace := by
    refine .extend .start (fun _ => none) ⟨(fun impossible => impossible),
      (fun _ impossible => impossible)⟩ ?_
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨initial, supported, rfl⟩

  views := ProtocolViewSuffix.initial setup.program
  origin := .initial
  historyAlignment := fun _ => rfl

/-- Unfinished live effects preserve the same saved checkpoint, irrespective
of the live concurrent cut or the permanent physical archive. -/
def transfer {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
    {state other : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (entry : other.entry = state.entry) (generation : other.generation = state.generation)
    (offset : other.attempt.phase = state.attempt.phase) :
    RecoverySourceCheckpoint setup mode other :=
  { checkpoint with
    compiled := by rw [offset]; exact checkpoint.compiled
    agrees := by rw [entry]; exact checkpoint.agrees
    trace := by rw [entry, generation]; exact checkpoint.trace
    historyAlignment := by rw [entry]; exact checkpoint.historyAlignment }

end RecoverySourceCheckpoint
end Vegas
