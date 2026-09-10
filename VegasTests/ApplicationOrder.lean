/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors.
-/

import Vegas.Compile.ApplicationOrder
import VegasTests.ApplicationEarlyBinding

/-! # Source-ordered admission on a generated application

Premature traffic remains legal message-pool traffic, but inclusion is rejected
until its emitted instruction is current.  A rejected envelope is not left
pending: the owner explicitly resubmits it with a fresh serial after the first
binding completes.
-/

noncomputable section

namespace VegasTests.ApplicationOrder

open Vegas Vegas.EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability
open VegasTests.ApplicationEarlyBinding

abbrev Player := ApplicationEarlyBinding.Player

def firstSite : SourceDecisionSite (0 : Player) source.prog [] 0 .bool
    (.constBool true) := .here _ _

def firstCode : BindingCode Player simpleExpr :=
  firstSite.bindingCode source.fresh compilerInitial 0

def ordered := image.orderedApplication

def earlyActions : List ordered.Action :=
  [.privateCommand 1 (.register 1 ⟨.bool, false⟩),
    .submit 1 (.binding secondCode.node (1, 1)), .include (1, 0)]

/-- The same early-binding script accepted by the graph-enabled image is
rejected by ordered admission. The private preparation remains, while the
included packet and false receipt stay publicly auditable. -/
theorem early_binding_rejected :
    (ordered.run earlyActions initialExecution).map (fun result =>
      (result.application.memory.done 0,
        result.application.memory.done 1,
        result.application.prepared.lookup (1, 1),
        result.pool.pending,
        result.pool.ledger,
        result.receipts)) =
      FinDist.pure (false, false, some ⟨.bool, false⟩, [],
        [⟨(1, 0), .binding secondCode.node (1, 1)⟩], [((1, 0), false)]) := by
  simp only [earlyActions, MessageApplication.run_cons, MessageApplication.run_nil,
    MessageApplication.step, FinDist.pure_bind, FinDist.map_pure]
  rfl

def completeActions : List ordered.Action := earlyActions ++
  [.privateCommand 0 (.register 0 ⟨.bool, true⟩),
    .submit 0 (.binding firstCode.node (0, 0)), .include (0, 0),
    .submit 1 (.binding secondCode.node (1, 1)), .include (1, 1)]

/-- Once owner zero completes the head binding, owner one resubmits the earlier
rejected payload. The fresh envelope is accepted, while the rejected ledger
entry and receipt are retained and the first conditional pair becomes active. -/
theorem bindings_advance_in_source_order :
    (ordered.run completeActions initialExecution).map (fun result =>
      (result.application.memory.done 0,
        result.application.memory.done 1,
        result.application.memory.accepted 0,
        result.application.memory.accepted 1,
        result.pool.ledger,
        result.receipts,
        image.activeAddress? result.application.memory)) =
      FinDist.pure (true, true,
        some (.opaque ((0 : Player), 0)), some (.opaque ((1 : Player), 1)),
        [⟨(1, 0), .binding secondCode.node (1, 1)⟩,
          ⟨(0, 0), .binding firstCode.node (0, 0)⟩,
          ⟨(1, 1), .binding secondCode.node (1, 1)⟩],
        [((1, 0), false), ((0, 0), true), ((1, 1), true)],
        some (firstConditionalSite.choice.publicationNode source.fresh compilerInitial).val) := by
  change (ordered.run
    [.privateCommand 1 (.register 1 ⟨.bool, false⟩),
      .submit 1 (.binding secondCode.node (1, 1)), .include (1, 0),
      .privateCommand 0 (.register 0 ⟨.bool, true⟩),
      .submit 0 (.binding firstCode.node (0, 0)), .include (0, 0),
      .submit 1 (.binding secondCode.node (1, 1)), .include (1, 1)] initialExecution).map _ = _
  simp only [
    MessageApplication.run_cons, MessageApplication.run_nil,
    MessageApplication.step, FinDist.pure_bind, FinDist.map_pure]
  rfl

/-- A payload constructor that does not match the current binding instruction
is rejected by the ordinary typed dispatch after passing address admission. -/
theorem wrong_kind_at_current_rejected :
    ordered.handle initialNative ⟨((0 : Player), 0), .choice firstCode.node ⟨.bool, true⟩⟩ =
      none := by
  rfl

/-- An environment request for a future sample address stutters. This fixture
has no sample instruction, so the assertion also covers an unknown address. -/
theorem off_head_sample_stutters :
    ordered.environmentStep initialNative (.sample 99) = FinDist.pure initialNative := by
  rfl

end VegasTests.ApplicationOrder

/-- info: 'VegasTests.ApplicationOrder.early_binding_rejected' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationOrder.early_binding_rejected

/-- info: 'VegasTests.ApplicationOrder.bindings_advance_in_source_order' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationOrder.bindings_advance_in_source_order

/-- info: 'VegasTests.ApplicationOrder.wrong_kind_at_current_rejected' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationOrder.wrong_kind_at_current_rejected
