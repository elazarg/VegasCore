/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.Compiler
import Vegas.Protocol.Application
import Vegas.Protocol.Graph
import Vegas.Core.ExprSimple

/-! # Typed ordered-protocol regression

This exercises operational representation only. It makes no source-adequacy,
settlement-correspondence, or equilibrium claim.
-/

noncomputable section

namespace VegasTests.OrderedProtocol

open Vegas Vegas.EventGraph Vegas.Protocol
open Interaction Interaction.OrderedProtocol GameTheory.Math.Probability

abbrev Player := Fin 2

local instance : DecidableEq (TypedValue simpleExpr) := fun left right =>
  if hty : left.ty = right.ty then
    match left, right, hty with
    | ⟨ty, leftValue⟩, ⟨_, rightValue⟩, rfl =>
        if hvalue : leftValue = rightValue then
          isTrue (by cases hvalue; rfl)
        else isFalse (by intro heq; cases heq; exact hvalue rfl)
  else isFalse (by intro heq; exact hty (congrArg TypedValue.ty heq))

private def noField {name : VarId} {ty : BaseTy} :
    HasVar ([] : CtxSimple) name ty → Nat := fun binding => nomatch binding

private def rejectingGuard : EventGuard simpleExpr where
  ty := .option .bool
  code := {
    actionName := 10
    Context := []
    expr := .isNone (.var 10 .here)
    fieldOf := noField }
  choiceReads := ∅
  read_mem binding := nomatch binding

private def publicChance : EventDist simpleExpr where
  ty := .bool
  code := {
    Context := []
    dist := DistExpr.point true
    fieldOf := noField }
  reads := ∅
  read_mem binding := nomatch binding

/-- Heterogeneous retained code: automatic disclosure of an initial sealed
integer, public chance, a rejecting nullable Boolean commitment, and its
commit-produced reveal. -/
private def code : Protocol.Code Player simpleExpr where
  initial := [⟨.int, some 0⟩]
  operations :=
    [.reveal ⟨0, .int⟩, .chance publicChance,
      .commit 0 rejectingGuard, .reveal ⟨3, .option .bool⟩]

private def setup : code.InitialInput
  | ⟨0, _⟩ => (7 : Int)

private def hosting : Hosting code where
  deadline _ := 1
  resolution? site :=
    if site.val = 2 ∨ site.val = 3 then some ⟨.option .bool, none⟩ else none
  bindingMode _ := .opaque
  disclosureMode _ := .manual

private abbrev model := Vegas.Protocol.runtime code hosting
private abbrev ModelState :=
  Interaction.OrderedProtocol.State Player (TypedValue simpleExpr)

private def inputs : List (InitialInput BaseTy (TypedValue simpleExpr)) :=
  code.runtimeInitialInputs setup

private def invalid : TypedValue simpleExpr := ⟨.option .bool, some true⟩

theorem runtime_layout_retains_all_operations :
    model.code.initial.length = 1 ∧ model.code.sites.length = 4 ∧
      model.code.sites[0]?.map (·.kind) =
        some (.reveal (.initial 0) .manual) ∧
      model.code.sites[1]?.map (·.kind) = some .chance ∧
      model.code.sites[2]?.map (·.tag) = some (.option .bool) ∧
      model.code.sites[3]?.map (·.kind) =
        some (.reveal (.operation 2) .manual) := by
  decide

theorem setup_remains_separate :
    inputs = [⟨.int, ⟨.int, 7⟩⟩] ∧
      model.code.initial[0]?.map (·.automaticPublic) = some false := by
  constructor <;> rfl

theorem retained_guard_rejects_invalid_opening :
    model.capabilities.validate 2 [] [] invalid = .reject := by
  decide

theorem malformed_is_an_application_rejection (state : ModelState) :
    model.handle state ⟨(1, 0), .malformed ⟨.bool, false⟩⟩ = none :=
  model.handle_malformed state 1 ⟨.bool, false⟩

theorem only_selected_sites_have_resolutions :
    model.code.sites[0]?.bind (·.resolution?) = none ∧
      model.code.sites[1]?.bind (·.resolution?) = none ∧
      model.code.sites[2]?.bind (·.resolution?) =
        some ⟨.option .bool, none⟩ ∧
      model.code.sites[3]?.bind (·.resolution?) =
        some ⟨.option .bool, none⟩ := by
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> rfl

private def commitSite := model.code.sites[2]'(by decide)
private def revealSite := model.code.sites[3]'(by decide)

/-- A concrete checkpoint after the two automatic heterogeneous operations.
The later regression starts here so it does not choose a witness from a chance
support. -/
private def commitCheckpoint : ModelState where
  visible := { pc := 2, store := [(1, ⟨.int, 7⟩), (2, ⟨.bool, true⟩)] }
  bound := [(0, ⟨.int, 7⟩), (1, ⟨.int, 7⟩), (2, ⟨.bool, true⟩)]
  effective := [(0, ⟨.int, 7⟩), (1, ⟨.int, 7⟩), (2, ⟨.bool, true⟩)]
  snapshots := []
  candidates := .empty

private def prepared : ModelState :=
  model.privateStep commitCheckpoint 0 (.prepare 9 invalid)

private def selected : ModelState :=
  model.acceptCommitment prepared commitSite 2 (0, 9)

theorem opaque_commit_accepts_guard_invalid_openable :
    model.handle prepared ⟨(0, 0), .commitment 2 (0, 9)⟩ = some selected := by
  rfl

theorem opaque_selection_does_not_publish :
    selected.visible.store.lookup 4 = none := by
  rfl

private def expired : ModelState :=
  (model.resolve selected revealSite .expired).get (by decide)

theorem expiry_uses_configured_disclosure_and_preserves_candidate :
    expired.visible.store.lookup 4 = some ⟨.option .bool, none⟩ ∧
      expired.candidates.lookup (0, 9) = .openable invalid := by
  constructor <;> rfl

/-- Every checked source compilation receives protocol code by total graph
lowering; this is only a structural coverage fact. -/
theorem checked_source_operation_count (source : WFProgram Player simpleExpr) :
    (ToEventGraph.compile source.core).graph.protocolCode.operations.length =
      (ToEventGraph.compile source.core).graph.nodeCount := by
  simp

end VegasTests.OrderedProtocol
