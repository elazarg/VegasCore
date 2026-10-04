/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.PrivateResolutionForkNormalizedBob
import Vegas.Game.SourceServiceProtectedDecisionLaw
import Vegas.Game.SourceServiceCanonicalPolicy
import Vegas.Game.SourceServiceImmediatePolicy

/-! # Bob's literal compiled source choice

The compiler reads the actual typed observation and completed own action list.
At Bob's TRUE source observation its normalized residual law is the original
source disclosure lottery. These are deterministic decoding resources; this
file does not certify any native scheduler fiber or substitute source beliefs
for native beliefs.
-/

noncomputable section

namespace Vegas.PrivateResolutionFork

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Math.Probability

abbrev bobContext : SourceCtx Player simpleExpr :=
  (4, .publication unitPayload) :: (3, .publicData .bool) :: (2, .publicData .bool) :: initialCtx

/-- The literal compiler references after the two samples and Alice's reveal. -/
def bobRefs : ContextRefs (graphLayout setup.program) bobContext :=
  (((ContextRefs.initial setup.context (outputLayout setup.program)).cons
    (outputRef setup.program sample0)).cons (outputRef setup.program sample1)).cons
      (outputRef setup.program aliceResolution)

/-- The real compiler at Bob's node uses the original source disclosure law,
after actual disclosure normalization, at this decoded local observation. -/
theorem normalized_compiled_bob_choice
    (profile : Profile sourceModel.behavioralSignature)
    (observation : (toEventGraph setup.program).PlayerObservation bob) (high disclose : Bool)
    (decoded : decodeObservation? bob bobRefs observation.store =
      some (sourceObserve bob (sourceAliceDone high disclose).state))
    (history : decodeCompletions setup.program observation.ownActions = []) :
    (compileEventProfile setup.program (normalizeDisclosureProfile setup.program []
      (Revelations.initial setup.context)
      (setup.decodeBehavioralProfile sourceAdmission profile))) bob bobResolution (by rfl)
        observation = sourceChoiceDisclosure bob (sourceBobInput disclose)
          (profile bob (sourceBobInput disclose)) := by
  change compilePolicyTable setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program)) (outputRef setup.program)
    bob (normalizeDisclosureProfile setup.program [] (Revelations.initial setup.context)
      (setup.decodeBehavioralProfile sourceAdmission profile) bob)
    (0 : Fin 1).succ.succ.succ observation.store
      (decodeCompletions setup.program observation.ownActions) = _
  simp only [setup, program, compilePolicyTable, Fin.cases_succ, Fin.cases_zero, dite_true]
  have current := decoded
  simp only [bobRefs, setup, program, sample0, sample1, aliceResolution] at current
  erw [current, history]
  exact normalized_decoded_bob_choice profile high disclose

/-- At an actual protected unrecorded Bob opportunity, normalized compiler
decisions render that same source lottery through the current canonical
packets and actual own recall. -/
theorem normalized_immediate_bob_choice
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph))
    (bound : nativeGraph.EventId → Nat)
    (profile : Profile sourceModel.behavioralSignature)
    (execution : (application setup leaks).Execution) (high disclose : Bool)
    (turn : execution.application.publicView.ownTurn? bob = some bobResolution)
    (clear : (runtime setup).serviceRisk leaks bound bob (execution.recall bob)
      (execution.observe (application setup leaks) bob) = false)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall bob) bobResolution = false)
    (fits : execution.application.publicView.InclusionFitsDeadline (runtime setup) bound
      bobResolution)
    (decoded : decodeObservation? bob bobRefs
      ((graph setup).playerStore bob execution.application.config.store) =
        some (sourceObserve bob (sourceAliceDone high disclose).state))
    (history : decodeCompletions setup.program
      ((setup.eventGraph.fromModeObservation .sequential bob
        ((graph setup).playerObserve bob execution.application.config)).ownActions) = []) :
    sourceServiceImmediatePolicy setup leaks bound (normalizeDisclosureProfile setup.program []
      (Revelations.initial setup.context)
      (setup.decodeBehavioralProfile sourceAdmission profile)) bob (execution.recall bob)
        (execution.observe (application setup leaks) bob) =
      (sourceChoiceDisclosure bob (sourceBobInput disclose)
        (profile bob (sourceBobInput disclose))).map fun decision =>
          (runtime setup).canonicalServiceDecision leaks bob (execution.recall bob)
            (execution.observe (application setup leaks) bob) bobResolution decision := by
  rw [sourceServiceImmediatePolicy_at_event clear turn,
    sourceServiceCanonicalOpportunity_protected bound _ bob bobResolution _ _ unrecorded fits,
    sourceServiceCanonicalPolicy_at_event setup leaks _ bob execution bobResolution turn
      (by rfl)]
  rw [normalized_compiled_bob_choice profile _ high disclose decoded history]

end Vegas.PrivateResolutionFork
