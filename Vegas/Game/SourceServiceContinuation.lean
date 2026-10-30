/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceReachedDecoding
import Vegas.Compile.EventGraphLaw

/-! # Full source continuations at compiled graph checkpoints

The suffix correspondence and source-position embedding identify the ordinary
graph runner's full terminal readout with the source continuation. Public defaults,
actual own choices and source metadata travel through the same configuration reader.
No additional source transition system or readout is introduced.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {profile : BehavioralProfile setup.program}

/-- The whole-program terminal reader factors through the existing suffix
configuration reader and the source-position embedding. -/
theorem SourceResidual.terminal_readout {rank : Nat} {config : (graph setup).Config}
    (residual : SourceResidual setup profile rank config) (final : (graph setup).Config) :
    setup.protocolReadout (sourceServicePrefix? setup (eventCount setup.program) final) =
      (decodeConfig? setup.program residual.program residual.refs residual.source.revelations
        residual.source.registry residual.embedding final.store final.history).bind fun terminal =>
          ProtocolState.readout setup.program
            (residual.lift (ProtocolState.terminalState residual.program terminal)) := by
  have count := residual.aligned.graphSuffix.countEq
  change rank + eventCount residual.program = eventCount setup.program at count
  have completionId : setup.eventGraph.fromModeCompletion .sequential = id := rfl
  have transport := residual.transport (eventCount residual.program) final.store
    (decodeHistory setup.program final.history) final.defaults
  rw [count] at transport
  unfold Setup.protocolReadout sourceServicePrefix? serviceSourcePrefix?
  rw [completionId, List.map_id, transport,
    decodeSourcePrefix?_terminal_state, Option.bind_map, Option.bind_map]
  rfl

variable [Finite Player]

/-- Finishing the ordinary compiled graph has exactly the full source
continuation law at its actual decoded source position. -/
theorem SourceResidual.runPlan_readout_law {rank : Nat} {config : (graph setup).Config}
    (residual : SourceResidual setup profile rank config) :
    ((graph setup).runPlan
      ((graph setup).policyPlan (compileEventProfile setup.program profile)
        (graph setup).canonicalScheduler) config.remaining config).map
      (fun final => decodeConfig? setup.program setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) [] (outputEmbedding setup.program)
        final.store final.history) = sourceContinuation setup profile rank config := by
  let := Fintype.ofFinite Player
  let run := (graph setup).runPlan
    ((graph setup).policyPlan (compileEventProfile setup.program profile)
      (graph setup).canonicalScheduler) config.remaining config
  let read := fun final : (graph setup).Config => decodeConfig? setup.program setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) [] (outputEmbedding setup.program) final.store final.history
  let tailRead := fun final : (graph setup).Config =>
    decodeConfig? setup.program residual.program residual.refs residual.source.revelations
      residual.source.registry residual.embedding final.store final.history
  let law := fun point : ProtocolState residual.program =>
    (ProtocolState.continuationLaw setup.program profile (residual.lift point)).map some
  let terminalLaw := fun terminal => law (ProtocolState.terminalState residual.program terminal)
  have harmonic : ∀ point, (ProtocolState.behavioralStateStep residual.program
      residual.residualProfile point).bind law = law point := by
    intro point
    have one := congrArg
      (fun distribution : PMF (ProtocolState setup.program) => distribution.bind
        (fun target => (ProtocolState.continuationLaw setup.program profile target).map some))
      (residual.commutes point)
    have stable := congrArg (fun distribution => distribution.map some)
      (ProtocolState.behavioralStateStep_continuation setup.program profile (residual.lift point))
    simp only [PMF.bind_map, PMF.map_bind] at one stable
    exact one.symm.trans stable
  have sourceLaw : (SourceProgram.runFrom residual.program residual.residualProfile
      residual.source).bind terminalLaw = sourceContinuation setup profile rank config := by
    have evaluated := ProtocolState.continuationLaw_bind_terminal residual.program
      residual.residualProfile law harmonic (ProtocolState.entry residual.program residual.source)
    rw [ProtocolState.continuationLaw_entry] at evaluated
    change (SourceProgram.runFrom residual.program residual.residualProfile
      residual.source).bind terminalLaw =
        (setup.continuationLaw profile (sourceServicePrefix? setup rank config)).map some
    rw [residual.decode]
    exact evaluated
  have history := residual.checkpoint.history
  have completionId : setup.eventGraph.fromModeCompletion .sequential = id := rfl
  rw [completionId, List.map_id] at history
  have compiled := CompiledPolicySuffix.runFrom_remaining_law setup.program profile
    residual.program residual.residualProfile residual.refs residual.source residual.embedding
    residual.refsBefore rank residual.aligned config residual.checkpoint.ordered
    residual.checkpoint.agrees history residual.checkpoint.defaults
  have terminalEq (terminal : SourceProgram.Config Player L residual.program.terminalCtx) :
      terminalLaw terminal = PMF.pure (ProtocolState.readout setup.program
        (residual.lift (ProtocolState.terminalState residual.program terminal))) :=
    ProtocolState.continuationLaw_terminal setup.program profile _
      (residual.lift_terminal _ (ProtocolState.terminal_terminalState _ terminal))
  have readEq (final : (graph setup).Config) : read final = (tailRead final).bind fun terminal =>
      ProtocolState.readout setup.program
        (residual.lift (ProtocolState.terminalState residual.program terminal)) := by
    have decoded := residual.terminal_readout final
    rw [sourceServicePrefix?_terminal_readout, completionId, List.map_id] at decoded
    exact decoded
  change run.map read = _
  calc
    _ = run.bind (fun final => PMF.pure (read final)) := rfl
    _ = run.bind (fun final => (tailRead final).elim (PMF.pure none) terminalLaw) := by
      apply bind_congr_on_support _
      intro final _
      rw [readEq]
      cases result : tailRead final with
      | none => rfl
      | some terminal => exact (terminalEq terminal).symm
    _ = (run.map tailRead).bind (fun result => result.elim (PMF.pure none) terminalLaw) := by
      rw [PMF.bind_map]
      rfl
    _ = ((SourceProgram.runFrom residual.program residual.residualProfile residual.source).map
        some).bind (fun result => result.elim (PMF.pure none) terminalLaw) := by
      change run.map tailRead = _ at compiled
      rw [compiled]
    _ = (SourceProgram.runFrom residual.program residual.residualProfile residual.source).bind
        terminalLaw := by rw [PMF.bind_map]; rfl
    _ = _ := sourceLaw
end Vegas
