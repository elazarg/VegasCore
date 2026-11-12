module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketLawApproximation
public import Vegas.Game.OnePacketAssessmentFidelity

@[expose] public section

/-! # Joint source readout and base payoff from clean continuation laws -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (initial : PMF (application setup timeouts leaks).State)
  (horizon : Nat) (scheduler : (application setup timeouts leaks).Scheduler)

local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu timeouts leaks) initial horizon scheduler

/-- A full typed source readout law determines the joint native readout and base payoff law. -/
theorem readoutExclusion_law_of_full_readout
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (native : PMF (E).History) (source : PMF (Config Player L setup.program.terminalCtx))
    (law : native.map (fun final => sourceReadout setup timeouts leaks final.state) =
      source.map some) :
    native.map (readoutExclusion setup timeouts leaks bounds initial horizon scheduler
      parameter utility excludedPayoff) =
      source.map (fun terminal => (some terminal,
        exclusionTerminalUtility setup parameter utility excludedPayoff terminal)) := by
  let attach := fun readout : Option (Config Player L setup.program.terminalCtx) =>
    (readout, exclusionReadoutUtility setup parameter utility excludedPayoff readout)
  change native.map _ = source.map (attach ∘ some)
  rw [← PMF.map_comp, ← law, PMF.map_comp]
  apply map_congr_on_support
  intro final supported
  have observed : sourceReadout setup timeouts leaks final.state ∈
      (native.map (fun last => sourceReadout setup timeouts leaks last.state)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨final, supported, rfl⟩
  rw [law] at observed
  obtain ⟨terminal, _reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp observed
  apply Prod.ext
  · rfl
  · funext who
    exact exclusionBase_eq_readout_of_readout setup timeouts parameter utility excludedPayoff leaks
      final.state terminal same.symm who

variable {setup timeouts leaks bounds horizon scheduler}

/-- Clean-boundary fidelity retains the complete typed source configuration
jointly with the actual native exclusion payoff vector. -/
theorem OnePacketAssessmentFidelity.continuation_jointLaw
    {intended : setup.intendedModel.BehavioralAssessment}
    {native : (onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralAssessment}
    (fidelity : OnePacketAssessmentFidelity setup timeouts leaks bounds horizon scheduler
      intended native)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (rank : Nat)
    (start : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (anchor : (application setup timeouts leaks).Execution)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (boundary : ReachedBoundary setup timeouts leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (valid : ProtocolState.Intended setup.program point) :
    ((bounds.onePacketMenu timeouts leaks).runFrom (initialLaw setup) horizon scheduler
        native.strategy start).map
        (readoutExclusion setup timeouts leaks bounds (initialLaw setup) horizon scheduler
          parameter utility excludedPayoff) =
      (setup.continuationLaw (setup.intendedOpeningProfile intended.strategy) (some point)).map
        (fun terminal => (some terminal,
          exclusionTerminalUtility setup parameter utility excludedPayoff terminal)) := by
  apply readoutExclusion_law_of_full_readout
  simpa only [sourceContinuation, decoded] using
    fidelity.continuation rank start anchor state boundary point decoded valid

end Vegas
