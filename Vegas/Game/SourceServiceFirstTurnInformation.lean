/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFirstTurnRanks
import Vegas.Game.SourceServicePrefixInformation
import Vegas.Compile.EventGraphParameterReadout

/-! # Effective whole source views on actual completion-rank input fibers

The current native view includes the focal graph observation and its own
completion actions. Successful decoding and the actual completed prefix
therefore recover the whole effective source observation at that rank. Own
native recall need not be equated separately. Original erased intentions are
not recovered by this statement.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem prefixCheckpoint_of_decode :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames)
      (refs : ContextRefs (graph setup).layout Γ) (registry : Registry Γ)
      (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef (graph setup).layout
        (outputLayout program event))
      (offset count : Nat) (state : ProtocolState program) (native : (graph setup).Config),
      native.cut.IsPrefix (offset + count) →
      decodeSourcePrefix? program refs registry revelations outputs count native.store
        (decodeHistory setup.program (native.history.map
          (setup.eventGraph.fromModeCompletion .sequential))) = some state →
      SourcePrefixCheckpoint setup program refs registry revelations outputs offset count state
        native := by
  intro Γ openNames program refs registry revelations outputs offset count
  induction count generalizing Γ openNames program refs registry revelations outputs offset with
  | zero =>
      intro state native ordered decoded
      cases program <;> simp only [decodeSourcePrefix?] at decoded <;>
        obtain ⟨source, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
      all_goals
        refine ⟨⟨source, registry, revelations, _⟩, rfl, rfl, rfl, ?_⟩
        exact ⟨decodeState?_agrees refs native.store source read, rfl,
          by simpa only [Nat.add_zero] using ordered⟩
  | succ count ih =>
      intro state native ordered decoded
      have nextOrdered : native.cut.IsPrefix ((offset + 1) + count) := by
        rw [show (offset + 1) + count = offset + (count + 1) by omega]
        exact ordered
      cases program with
      | ret payoffs =>
          simp only [decodeSourcePrefix?] at decoded
          cases decoded
      | sample name fresh law next =>
          rw [decodeSourcePrefix?_sample] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact ih next _ _ _ _ (offset + 1) rest native nextOrdered read
      | commit name owner fresh guard next =>
          rw [decodeSourcePrefix?_commit] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact ih next _ _ _ _ (offset + 1) rest native nextOrdered read
      | reveal published owner name fresh binding unresolved next =>
          rw [decodeSourcePrefix?_reveal] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact ih next _ _ _ _ (offset + 1) rest native nextOrdered read

/-- Equal current physical views at two actual normalized first-turn rank
endpoints determine the whole effective decoded source view. Each endpoint's
checkpoint and successful decoder are derived from initialized rank support.
The initial draws may differ and remain arbitrarily correlated. -/
theorem sourceServiceFirstTurn_prefix_view_eq_of_observe_eq [Finite Player]
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (rank : Nat) (within : rank ≤ (graph setup).order.eventCount)
    (leftInitial rightInitial : State L setup.context)
    (leftSupport : leftInitial ∈ setup.initialLaw.support)
    (rightSupport : rightInitial ∈ setup.initialLaw.support)
    (left right : (application setup leaks).Execution)
    (leftReached : left ∈ ((application setup leaks).runUntilHorizon scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
        (normalizeDisclosureProfile setup.program [] (Revelations.initial setup.context) profile))
      (sourceServiceRankCompleted rank) horizon
      (.initial (application setup leaks)
        (EventGraphRuntime.State.initial (setup.eventInputs leftInitial)))).support)
    (rightReached : right ∈ ((application setup leaks).runUntilHorizon scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
        (normalizeDisclosureProfile setup.program [] (Revelations.initial setup.context) profile))
      (sourceServiceRankCompleted rank) horizon
      (.initial (application setup leaks)
        (EventGraphRuntime.State.initial (setup.eventInputs rightInitial)))).support)
    (focal : Player)
    (same : left.observe (application setup leaks) focal =
      right.observe (application setup leaks) focal) :
    (sourceServicePrefix? setup rank left.application.config).map
        (ProtocolState.observe focal setup.program) =
      (sourceServicePrefix? setup rank right.application.config).map
        (ProtocolState.observe focal setup.program) := by
  classical
  let _ := Fintype.ofFinite Player
  let normalized := normalizeDisclosureProfile setup.program []
    (Revelations.initial setup.context) profile
  have effective (who : Player) : (normalized who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context) :=
    (profile who).normalizeDisclosureFrom_effective setup.program []
      (Revelations.initial setup.context) (fun view => PMF.pure view.2)
  have leftBoundary := ((sourceServiceFirstTurn_rank_law (turns := turns) contract timely
    normalized effective leftInitial leftSupport rank within).1 left leftReached).2
  have rightBoundary := ((sourceServiceFirstTurn_rank_law (turns := turns) contract timely
    normalized effective rightInitial rightSupport rank within).1 right rightReached).2
  obtain ⟨leftResidual⟩ := leftBoundary.sourceResidual (profile := normalized)
  obtain ⟨rightResidual⟩ := rightBoundary.sourceResidual (profile := normalized)
  have leftDecoded := leftResidual.decode
  have rightDecoded := rightResidual.decode
  have first := prefixCheckpoint_of_decode setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program)) []
    (Revelations.initial setup.context) (outputRef setup.program) 0 rank _ _
    (by simpa only [Nat.zero_add] using leftBoundary.ordered) leftDecoded
  have second := prefixCheckpoint_of_decode setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program)) []
    (Revelations.initial setup.context) (outputRef setup.program) 0 rank _ _
    (by simpa only [Nat.zero_add] using rightBoundary.ordered) rightDecoded
  have sourceEq := SourcePrefixCheckpoint.source_view_eq_of_observe_eq focal setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program)) []
    (Revelations.initial setup.context) (outputRef setup.program) 0 rank _ _ left right
    first second same
  rw [leftDecoded, rightDecoded, Option.map_some, Option.map_some, sourceEq]

end Vegas
