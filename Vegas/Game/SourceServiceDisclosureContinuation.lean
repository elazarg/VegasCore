/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceActiveDisclosureLaw

/-! # Physical continuations of effective source disclosures

A failed guarded disclosure has no retained fresh opening. Its actual timed
continuation is the existing replay execution, with all private observations
and recall retained.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- An unavailable guarded opening leaves exactly the real replay execution,
independently of the source disclosure and timing probabilities. -/
theorem sourceServiceTimedPolicy_active_reveal_absent
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.reveal published owner name fresh binding unresolved next))
    (refs : ContextRefs (graphLayout setup.program) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published owner name fresh binding unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.reveal published owner name fresh binding unresolved next) profile
      refs source.revelations source.registry embedding refsBefore rank)
    (execution : (application setup leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
      (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = source.history)
    (valid : execution.application.BindingInvariant)
    (recalled : execution.InputRecall (application setup leaks))
    (origins : (runtime setup).ResolutionEvidenceOrigins leaks execution)
    (effective : (profile owner).EffectiveDisclosures
      (.reveal published owner name fresh binding unresolved next)
        source.registry source.revelations)
    (network : (runtime setup).NetworkPolicy leaks) (remaining : List Player) (ticks : Nat) :
    let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    ∀ (owned : (graph setup).actor? event = some owner)
      (_granted : execution.application.serviceGrant = some event)
      (_unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
      (_counted : (execution.recall owner).length + 1 + remaining.count owner =
        rosterOffset setup rosters owner event + (rosters event).count owner)
      (_absent : rosterOpening? setup leaks owner event
        (execution.observe (application setup leaks) owner) = none),
    let app := application setup leaks
    let players := sourceServiceTimedPolicy setup leaks rosters timing wholeProfile
    let phase := remaining.map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
    (app.invoke players owner execution).bind
      ((runtime setup).runInteractionPlan leaks players network phase) =
      (app.invoke (fun _ => app.replayPolicy) owner execution).bind
        ((runtime setup).runInteractionPlan leaks (fun _ => app.replayPolicy) network phase) := by
  intro index event owned granted unsent counted absent app players phase
  rw [sourceServiceTimedPolicy_active_reveal_law setup leaks rosters timing fresh binding
    unresolved next wholeProfile profile refs source embedding refsBefore rank aligned execution
    agree history valid recalled origins effective network remaining ticks owned granted unsent
    counted]
  let replay := (app.invoke (fun _ => app.replayPolicy) owner execution).bind
    ((runtime setup).runInteractionPlan leaks (fun _ => app.replayPolicy) network phase)
  have replayed (other : Player → app.Policy) (same : other = fun _ => app.replayPolicy) :
      (app.invoke other owner execution).bind
        ((runtime setup).runInteractionPlan leaks other network phase) = replay := by
    subst same
    rfl
  change _ = replay
  refine (FinDist.bind_congr (g := fun _ => replay) fun disclose _ => ?_).trans
    (FinDist.bind_const _ _)
  refine (FinDist.bind_congr (g := fun _ => replay) fun slot _ => ?_).trans
    (FinDist.bind_const _ _)
  dsimp only
  apply replayed
  funext who past view
  by_cases equal : who = owner
  · subst who
    simp only [Function.update_self, ReactiveApplication.scheduledPolicy]
    split
    · split
      · rfl
      · rename_i candidate raw found
        split_ifs at found
        cases found.symm.trans absent
    · rfl
  · rw [Function.update_of_ne equal]

end Vegas.SourceProgram.RevealService
