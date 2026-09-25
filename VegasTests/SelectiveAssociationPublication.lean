/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationOpeningService
import VegasTests.SelectiveAssociationPayoffs
import Vegas.EventGraph.ResolutionProvenance

/-! # Publication cannot improve a fixed guess

Every successful public result is the value of its earlier binding. A later
decision to withhold can remove a correct guess, but cannot create one. These
facts use the actual compiled graph and arbitrary legal native histories.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

variable {observation : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph)}

theorem native_binding_invariant
    {observation : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph)}
    (who : Player) (value : PublicationResult Bool) :
    (serviceApp observation).Invariant (fun state =>
      (nativeBindingRef who).get? state.config.store = some value) := by
  fin_cases who
  · exact nativeRuntime.reactiveStoreInvariant observation (.inr aliceBinding) value
  · exact nativeRuntime.reactiveStoreInvariant observation (.inr bobBinding) value
  · exact nativeRuntime.reactiveStoreInvariant observation (.inr carolBinding) value

theorem native_publication_binding (config : nativeGraph.Config)
    (reachable : config.Reachable nativeInputs) (who : Player) (bit : Bool)
    (published : (nativePublicationRef who).get? config.store = some (.success bit)) :
    (nativeBindingRef who).get? config.store = some (.success bit) := by
  obtain ⟨checks, codeEq, _, _⟩ := native_publication_rule who
  exact reachable.publication_binding (nativePublicationEvent who) who .bool
    (nativeBindingRef who) checks (native_publication_output who) codeEq bit published

theorem native_publication_correctness_le (config : nativeGraph.Config)
    (reachable : config.Reachable nativeInputs) (who : Player)
    (aliceResult : PublicationResult Bool) :
    correctness aliceResult (((nativePublicationRef who).get? config.store).getD .failure) ≤
      correctness aliceResult (((nativeBindingRef who).get? config.store).getD .failure) := by
  cases publication : (nativePublicationRef who).get? config.store with
  | none =>
      simpa only [Option.getD_none, correctness_failure_right] using
        correctness_nonneg aliceResult (((nativeBindingRef who).get? config.store).getD .failure)
  | some result =>
      cases result with
      | failure =>
          simpa only [Option.getD_some, correctness_failure_right] using
            correctness_nonneg aliceResult
              (((nativeBindingRef who).get? config.store).getD .failure)
      | success bit =>
          rw [native_publication_binding config reachable who bit publication]

theorem native_history_reachable (control : (serviceApp observation).Control)
    (trace : (serviceArena observation).Trace (some control)) :
    control.execution.application.config.Reachable nativeInputs := by
  have raw := (serviceMenu observation).toRawTrace (FinDist.pure nativeInitial) nativeHorizon
    (serviceScheduler observation) trace
  obtain ⟨inputs, selected, reachable⟩ := nativeRuntime.reactive_history_graph_reachable
    observation (FinDist.pure nativeInputs) nativeHorizon (serviceScheduler observation)
    (by rw [FinDist.map_pure]; exact raw)
  cases FinDist.mem_support_pure.mp selected
  exact reachable

/-- The inequality applies to every legal native history, independently of an
assessment's posterior weight for that history. -/
theorem native_history_correctness_le (control : (serviceApp observation).Control)
    (trace : (serviceArena observation).Trace (some control)) (who : Player)
    (aliceResult : PublicationResult Bool) :
    correctness aliceResult
        (((nativePublicationRef who).get? control.execution.application.config.store).getD
          .failure) ≤
      correctness aliceResult
        (((nativeBindingRef who).get? control.execution.application.config.store).getD .failure) :=
  native_publication_correctness_le control.execution.application.config
    (native_history_reachable control trace) who aliceResult

end VegasTests.SelectiveAssociation
