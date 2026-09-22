/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.SetupProtocolBehavioral
import Vegas.Expr.Simple
import GameTheory.Protocol.SubgamePerfect

/-! # Private types do not create publicly identifiable subgames

Alice receives a private bit in setup; Bob then commits and reveals a guess.
The two setup draws lie in one Bob information set. His policy must be shared
across them, and neither individual draw starts a proper subgame.
-/

noncomputable section

namespace VegasTests.SetupProtocol

open Vegas Vegas.SourceProgram GameTheory.Protocol GameTheory.Math.Probability

private abbrev context : SourceCtx Bool simpleExpr := [(0, .privateInput false .bool)]

private def guard : SourceGuard simpleExpr context true 1 .bool where
  schema := []
  schemaNames := by decide
  subjectFresh := by decide
  code := .constBool true
  reads := fun impossible => nomatch impossible

def program : SourceProgram Bool simpleExpr context ∅ :=
  .commit 1 true (by decide) guard <|
  .reveal 2 true 1 (by decide) .here (by decide) <|
  .ret []

def initial (bit : Bool) : State simpleExpr context := Env.cons bit (Env.empty _)

def setup : Setup (Player := Bool) (L := simpleExpr) where
  context := context
  namesNodup := by decide
  initialLaw := (FinDist.uniformOfFintype (α := Bool)).map initial
  obligations := ∅
  program := program
  accounts := rfl

private def admission : CommitmentInterface program := CommitmentInterface.values program

private abbrev game := setup.executionProtocol admission
private abbrev model := setup.informationModel admission

private def afterSetup (bit : Bool) : setup.ProtocolState :=
  some (ProtocolState.entry program (setup.initialConfig (initial bit)))

private theorem setup_legal : game.Legal game.init (fun _ => none) :=
  ⟨fun impossible => impossible, fun _ impossible => impossible⟩

def drawHistory (bit : Bool) : game.History :=
  ⟨afterSetup bit, .extend .start (fun _ => none) setup_legal (by
    change afterSetup bit ∈ (setup.initialLaw.map _).support
    rw [FinDist.support_map]
    refine ⟨initial bit, ?_, rfl⟩
    rw [show setup.initialLaw = (FinDist.uniformOfFintype (α := Bool)).map initial from rfl,
      FinDist.support_map]
    exact ⟨bit, FinDist.mem_support_uniformOfFintype bit, rfl⟩)⟩

theorem bob_cannot_tell (first second : Bool) :
    model.infoOf true (drawHistory first).trace = model.infoOf true (drawHistory second).trace := by
  change some (Sum.inl _) = some (Sum.inl _)
  congr 2
  apply Prod.ext
  · change SourceObservation.mk _ = SourceObservation.mk _
    congr 1
    funext name cell member
    cases member with
    | here => rfl
    | there impossible => nomatch impossible
  · rfl

/-- The owner receives the type through the ordinary source observation. -/
example (bit : Bool) :
    (sourceObserve false (setup.initialConfig (initial bit)).state).cells.get .here =
      some bit := rfl

/-- A supplied type realization is not an extra subgame at which Bob may
optimize as if he knew the bit. This uses the actual setup history tree. -/
theorem draw_not_subgame (bit : Bool) : ¬ model.IsSubgameRoot (drawHistory bit) := by
  intro proper
  have reached := proper true (drawHistory bit) (drawHistory (!bit))
    (ExecutionProtocol.HistoryReaches.refl _ _) (by intro impossible; exact impossible)
    rfl (by intro impossible; exact impossible) rfl (bob_cannot_tell bit (!bit))
  obtain ⟨fuel, path⟩ := reached
  have equal := path.eq_of_trace_length_eq rfl
  have states := congrArg ExecutionProtocol.History.state equal
  have configs := Sum.inl.inj (Option.some.inj states)
  have bits := congrArg
    (fun config : Config Bool simpleExpr context => config.state.get .here) configs
  cases bit <;> cases bits

/-- Legal policies give the same answer at the two private-type draws. -/
example (policy : model.Policy true) :
    policy.act (model.infoOf true (drawHistory false).trace) =
      policy.act (model.infoOf true (drawHistory true).trace) := by
  rw [bob_cannot_tell false true]

/-- Local randomization does not give Bob access to the private setup draw. -/
example (policy : model.BehavioralPolicy true) :
    (policy (model.infoOf true (drawHistory false).trace)).map Subtype.val =
      (policy (model.infoOf true (drawHistory true).trace)).map Subtype.val := by
  rw [bob_cannot_tell false true]

/-- Continuing after the draw retains the actual type under every randomized
source profile; it does not draw a fresh type from the prior. -/
example (profile : BehavioralProfile program) (bit : Bool) :
    (setup.continuationLaw profile (drawHistory bit).state).map
      (fun state => state.get (.there (.there .here))) = FinDist.pure bit := by
  simp [Setup.continuationLaw, drawHistory, afterSetup, setup, ProtocolState.continuationLaw,
    ProtocolState.entry, program, runFrom, runWith, Setup.initialConfig, initial,
    FinDist.map_bind, Env.get, Env.cons]

example : model.IsSubgameRoot game.initHistory := model.initHistory_isSubgameRoot

example : game.BoundedHorizon 3 := setup.protocol_bounded admission

end VegasTests.SetupProtocol
