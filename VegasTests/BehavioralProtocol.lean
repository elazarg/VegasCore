/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.BehavioralSubgame
import Vegas.Expr.Simple

/-! # Randomized source play with an infinite player universe

Player zero chooses between a valid binding and irreversible forfeiture with
equal probability. The policy is legal exactly when the site admits forfeiture.
The protocol preserves both probabilities and the retained binding after a prefix.
-/

noncomputable section

namespace VegasTests.BehavioralProtocol

open Vegas Vegas.SourceProgram GameTheory.Protocol GameTheory.Math.Probability

private def guard : SourceGuard simpleExpr ([] : SourceCtx Nat simpleExpr) 0 0 .bool where
  schema := []
  schemaNames := by decide
  subjectFresh := by decide
  code := .constBool true
  reads := fun impossible => nomatch impossible

def program : SourceProgram Nat simpleExpr [] ∅ :=
  .commit 0 0 (by decide) guard <|
  .reveal 1 0 0 (by decide) .here (by decide) <|
  .ret []

private def initial : Config Nat simpleExpr [] :=
  ⟨Env.empty _, [], Revelations.initial [], fun _ => []⟩

private def choice (bit : Bool) : PublicationResult Bool :=
  if bit then .success true else .failure

private def lottery : FinDist (PublicationResult Bool) :=
  (FinDist.uniformOfFintype (α := Bool)).map choice

def profile (who : Nat) : BehavioralPolicy who program :=
  (fun _ _ => lottery, (fun _ _ => FinDist.pure true, PUnit.unit))

theorem admitted (who : Nat) :
    (profile who).Admitted program (CommitmentInterface.forfeiture program) := by
  refine ⟨?_, trivial⟩
  intro _ _ value _
  cases value <;> trivial

/-- A random action with positive failure mass is rejected as a whole by the
value-only interface. Translation does not condition it on successful draws. -/
theorem not_value_only :
    ¬ (profile 0).Admitted program (CommitmentInterface.values program) := by
  intro allowed
  have impossible := allowed.1 rfl (initial.view 0) .failure (by
    change PublicationResult.failure ∈ lottery.support
    rw [lottery, FinDist.support_map]
    exact ⟨false, FinDist.mem_support_uniformOfFintype false, rfl⟩)
  simp [CommitmentInterface.values, CommitmentAdmission.Admits] at impossible

private abbrev admission := CommitmentInterface.forfeiture program
private abbrev model := informationModel program admission initial

/-- Actual randomized protocol execution, with Nat as the player carrier. -/
example :
    (model.runSingleMoverBehavioralFrom (protocol_singleMover program admission initial)
      (fun who => (profile who).toProtocol program admission (admitted who))
      2 (executionProtocol program admission initial).initHistory).map
        (fun final => ProtocolState.readout program final.state) =
      (runFrom program profile initial).map some :=
  protocol_runBehavioral_eq program admission initial profile admitted

/-- Encoding retains the complete mixed binding law, including failure mass. -/
example :
    ((profile 0).toProtocol program admission (admitted 0)
      (ProtocolState.observe 0 program (ProtocolState.entry program initial))).map
        (fun selected => OwnAction.binding (L := simpleExpr) 0 0 .bool selected.1) = lottery := by
  rw [BehavioralPolicy.toProtocol, FinDist.map_toSubtype]
  simp only [BehavioralPolicy.protocolAction, program, ProtocolState.entry,
    ProtocolState.observe, Sum.elim_inl, dite_true, profile,
    FinDist.map_comp, Function.comp_def, OwnAction.binding_commit]
  exact FinDist.map_id _

/-- Even a replacement policy that would bind differently cannot revise a
retained hidden binding. Randomized disclosure leaves that stored choice fixed. -/
example (replacement : BehavioralProfile program) (value : PublicationResult Bool) :
    (ProtocolState.continuationLaw program replacement
      (Sum.inr (Sum.inl (commitSuccessor 0 guard initial value)))).map
        (fun state => state.get (.there .here)) = FinDist.pure value := by
  simp [ProtocolState.continuationLaw, program, runFrom, runWith,
    FinDist.map_bind, commitSuccessor, Env.get, Env.cons]

/-- The semantic horizon can be enlarged without changing behavioral SPE. -/
example (policies : GameTheory.Profile model.behavioralSignature)
    (utility : (executionProtocol program admission initial).History → Nat → ℝ)
    (largerBound : (executionProtocol program admission initial).BoundedHorizon 10) :
    model.IsBehavioralSubgamePerfect (protocol_singleMover program admission initial)
      (protocol_bounded program admission initial) policies utility ↔
    model.IsBehavioralSubgamePerfect (protocol_singleMover program admission initial)
      largerBound policies utility :=
  model.isBehavioralSubgamePerfect_bound_iff _ _ _ _ _

end VegasTests.BehavioralProtocol
