/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDecoderSlice
import Vegas.Game.SourceServiceFirstTurnRanks
import Vegas.Compile.EventGraphParameterReadout

/-! # Shared typed checkpoints at initialized first-turn completion ranks

The source syntax chooses one typed decoder slice before any initial draw or
runtime execution. Every supported first-turn rank endpoint decodes into that
same slice, with its fixed registry, publication bookkeeping and policy table.
The source state and action history are read from the actual completed store
and history. No source likelihood, posterior or traffic factor is assumed.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- All initialized rank endpoints have typed checkpoints in one static
compiler-aligned slice. The witnesses precede the supported initial draw and
actual stopped execution, so an arbitrary parameter may be retained with the
same seed in a later joint-law construction. -/
theorem sourceServiceFirstTurn_shared_checkpoint [Fintype Player]
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (rank : Nat) (within : rank ≤ (graph setup).order.eventCount) :
    ∃ (Γ : SourceCtx Player L) (names : Finset VarId)
      (tail : SourceProgram Player L Γ names) (tailProfile : BehavioralProfile tail)
      (refs : ContextRefs (graph setup).layout Γ) (registry : Registry Γ)
      (revelations : Revelations Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) tail)
      (refsBefore : ContextRefsBefore refs embedding)
      (lift : ProtocolState tail → ProtocolState setup.program)
      (liftView : ∀ who, ProtocolView who tail → ProtocolView who setup.program)
      (recover : ∀ who, ProtocolView who setup.program → Option (ProtocolView who tail)),
      rank + eventCount tail = eventCount setup.program ∧
      CompiledPolicySuffix setup.program profile tail tailProfile refs revelations registry
        embedding refsBefore rank ∧
      (∀ who, (tailProfile who).EffectiveDisclosures tail registry revelations) ∧
      Function.Injective lift ∧
      (∀ who state, ProtocolState.observe who setup.program (lift state) =
        liftView who (ProtocolState.observe who tail state)) ∧
      (∀ who state, recover who (ProtocolState.observe who setup.program (lift state)) =
        some (ProtocolState.observe who tail state)) ∧
      (∀ state, ProtocolState.behavioralStateStep setup.program profile (lift state) =
        (ProtocolState.behavioralStateStep tail tailProfile state).map lift) ∧
      (∀ more store history,
        decodeSourcePrefix? setup.program
            (ContextRefs.initial setup.context (outputLayout setup.program)) []
            (Revelations.initial setup.context) (outputRef setup.program) (rank + more)
            store history =
          (decodeSourcePrefix? tail refs registry revelations embedding.ref more store history).map
            lift) ∧
      ∀ initial ∈ setup.initialLaw.support,
        ∀ execution ∈ ((application setup leaks).runUntilHorizon scheduler
          (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
          (sourceServiceRankCompleted rank) horizon
          (.initial (application setup leaks)
            (EventGraphRuntime.State.initial (setup.eventInputs initial)))).support,
          execution.environmentRecall.length ≤ horizon ∧
          CompletionBoundary setup leaks scheduler
            (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
            rank execution ∧
          ∃ source : Config Player L Γ,
            source.registry = registry ∧ @source.revelations = @revelations ∧
            decodeState? refs execution.application.config.store = some source.state ∧
            SourceCheckpoint setup source refs rank execution.application.config ∧
            sourceServicePrefix? setup rank execution.application.config =
              some (lift (ProtocolState.entry tail source)) := by
  classical
  obtain ⟨Γ, names, tail, tailProfile, refs, registry, revelations, embedding, refsBefore,
    lift, liftView, recover, counted, aligned, tailEffective, injective, viewed, recovered,
    commutes, transport⟩ :=
    SourceProgram.exists_decoder_slice setup.program profile setup.program profile
      (ContextRefs.initial setup.context (outputLayout setup.program)) []
      (Revelations.initial setup.context) (outputEmbedding setup.program)
      (initialRefsBefore setup.program) 0 (CompiledPolicySuffix.whole setup.program profile)
      rank within
  have transported (more store history) :
      decodeSourcePrefix? setup.program
          (ContextRefs.initial setup.context (outputLayout setup.program)) []
          (Revelations.initial setup.context) (outputRef setup.program) (rank + more)
          store history =
        (decodeSourcePrefix? tail refs registry revelations embedding.ref more store history).map
          lift := transport more store history
  refine ⟨Γ, names, tail, tailProfile, refs, registry, revelations, embedding, refsBefore,
    lift, liftView, recover, counted, ?_, tailEffective effective, injective, viewed, recovered,
    commutes, transported, ?_⟩
  · simpa only [Nat.zero_add] using aligned
  · intro initial initialSupport execution reached
    obtain ⟨bounded, boundary⟩ :=
      (sourceServiceFirstTurn_rank_law (turns := turns) contract timely profile effective initial
        initialSupport rank within).1 execution reached
    refine ⟨bounded, boundary, ?_⟩
    obtain ⟨residual⟩ := boundary.sourceResidual (profile := profile)
    have decodedWhole := residual.decode
    have split := transported 0 execution.application.config.store
      (decodeHistory setup.program (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)))
    change sourceServicePrefix? setup (rank + 0) execution.application.config = _ at split
    rw [Nat.add_zero, decodeSourcePrefix?] at split
    cases decoded : decodeState? refs execution.application.config.store with
    | none =>
        rw [decoded, Option.map_none, Option.map_none, decodedWhole] at split
        cases split
    | some state =>
        let source : Config Player L Γ :=
          ⟨state, registry, revelations,
            decodeHistory setup.program (execution.application.config.history.map
              (setup.eventGraph.fromModeCompletion .sequential))⟩
        refine ⟨source, rfl, rfl, rfl, ?_, ?_⟩
        · exact ⟨decodeState?_agrees refs execution.application.config.store state decoded,
            rfl, boundary.ordered⟩
        · simpa only [decoded, Option.map_some] using split

end Vegas
