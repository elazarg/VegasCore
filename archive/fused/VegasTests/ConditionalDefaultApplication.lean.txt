/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors.
-/

import Vegas.Compile.BindingTimeoutCompilation
import VegasTests.ConditionalApplicationImage

/-! # Conditional publication from a generated public binding fallback

This regression attaches a source-certified fallback to the generated binding
in the three-node conditional application. The actual shared message runner
includes the permissionless binding expiry and then the owner's cleartext
publication. Negative checks keep opaque openings, public defaults, dynamic
typing, authentication, deadlines, and replay as separate runtime boundaries.
-/

noncomputable section

namespace VegasTests.ConditionalDefaultApplication

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction Interaction.MessageApplication
open VegasTests.ConditionalApplicationImage
open GameTheory.Math.Probability

abbrev Player := ConditionalApplicationImage.Player

/-- The original binding guard accepts this public fallback in every source
environment. -/
def fallback : SourceDecisionSite.PublicFallback initialSite where
  expr := .constBool false
  legal _ := rfl

def timedBindingCode : BindingCode Player simpleExpr :=
  fallback.bindingTimeoutCode source.fresh compilerInitial 10

def timedImage : ApplicationImage Player simpleExpr :=
  fallback.installBindingTimeout source.fresh compilerInitial 10 (image 10)

theorem timed_lookup : timedImage.lookup timedBindingCode.node =
    some (.bind timedBindingCode) := by
  exact fallback.lookup_installBindingTimeout source.fresh compilerInitial 10
    (image 10) bindingCode.node (image_lookup_binding 10)

def initialExecution : timedImage.application.State :=
  MessageApplication.State.initial timedImage.application initialNative

def actions : List timedImage.application.Action :=
  [.privateCommand 0 (.register 0 ⟨.bool, true⟩),
    .environment (.advance 11),
    .submit 1 (.expireBinding timedBindingCode.node), .include (1, 0),
    .submit 0 (.conditional (conditionalCode 10).endpoint.publicationNode
      (.cleartext ⟨.bool, false⟩)), .include (0, 0)]

/-- The generated fallback and default-aware conditional endpoint execute as
one real native run. The fallback is public, while the conflicting private
preparation remains unchanged and unexposed. -/
theorem default_run_reaches_terminal :
    (timedImage.application.run actions initialExecution).map (fun execution =>
      (execution.application.memory.finished compiled.graph.nodeCount,
        compiled.readPublicTerminal? execution.application.memory,
        execution.application.memory.accepted 0,
        execution.application.prepared.lookup (0, 0),
        execution.application.frozen 0,
        execution.receipts)) =
      FinDist.pure (true, some (Env.cons (x := 2) (some false) (Env.empty Val)),
        some (.publicDefault ⟨.bool, false⟩), some ⟨.bool, true⟩, none,
        [((1, 0), true), ((0, 0), true)]) := by
  simp only [actions, MessageApplication.run_cons, MessageApplication.run_nil,
    MessageApplication.step, ApplicationImage.application, FinDist.pure_bind, FinDist.map_pure]
  rfl

def opaqueState (secret : Bool) : ApplicationImage.State Player simpleExpr :=
  (initialNative.register 0 0 ⟨.bool, secret⟩).bind timedBindingCode (0, 0)

def defaultState (clock : Nat) : ApplicationImage.State Player simpleExpr :=
  (initialNative.defaultBind timedBindingCode ⟨.bool, false⟩).advance clock

def invalidDefaultState (clock : Nat) : ApplicationImage.State Player simpleExpr :=
  (initialNative.defaultBind timedBindingCode ⟨.option .bool, none⟩).advance clock

/-- Opaque and public-default dispositions accept only their own publication
forms; neither branch manufactures evidence for the other. -/
theorem disposition_forms_are_separate (secret : Bool) :
    timedImage.handle (opaqueState secret)
        ⟨(0, 0), .conditional 2 (.cleartext ⟨.bool, secret⟩)⟩ = none ∧
      timedImage.handle (defaultState 11)
        ⟨(0, 0), .conditional 2 (.opening (0, 0) ⟨.bool, false⟩)⟩ = none := by
  constructor
  · cases secret <;> rfl
  · rfl

/-- Cleartext publication retains independent owner, value, and dynamic-type
checks at the generated conditional endpoint. -/
theorem malformed_cleartext_rejected :
    timedImage.handle (defaultState 11)
        ⟨(0, 0), .conditional 2 (.cleartext ⟨.bool, true⟩)⟩ = none ∧
      timedImage.handle (defaultState 11)
        ⟨(1, 0), .conditional 2 (.cleartext ⟨.bool, false⟩)⟩ = none ∧
      timedImage.handle (defaultState 11)
        ⟨(0, 0), .conditional 2 (.cleartext ⟨.option .bool, none⟩)⟩ = none := by
  exact ⟨rfl, rfl, rfl⟩

/-- A dynamically ill-typed raw default cannot enable either owner decline or
permissionless conditional expiry. -/
theorem invalid_default_rejects_resolution :
    timedImage.handle (invalidDefaultState 11)
        ⟨(0, 0), .conditional 2 .decline⟩ = none ∧
      timedImage.handle (invalidDefaultState 11)
        ⟨(1, 0), .conditional 2 .expire⟩ = none := by
  exact ⟨rfl, rfl⟩

/-- Conditional expiry is strict even after the binding fallback has already
completed its source node. -/
theorem conditional_deadline_is_strict :
    timedImage.handle (defaultState 10)
      ⟨(1, 0), .conditional 2 .expire⟩ = none := by
  rfl

abbrev Payload := ApplicationImage.Payload Player simpleExpr

def submitAndInclude (state : timedImage.application.State) (sender : Player)
    (payload : Payload) : timedImage.application.State :=
  let submitted := state.pool.submit sender payload
  timedImage.application.includePending { state with pool := submitted.2 } submitted.1

def defaultIncluded : timedImage.application.State :=
  submitAndInclude
    ⟨(initialNative.register 0 0 ⟨.bool, true⟩).advance 11,
      MessagePool.empty Player Payload, []⟩
    1 (.expireBinding timedBindingCode.node)

def published : timedImage.application.State :=
  submitAndInclude defaultIncluded 0
    (.conditional (conditionalCode 10).endpoint.publicationNode
      (.cleartext ⟨.bool, false⟩))

def replayed : timedImage.application.State :=
  let replay := published.pool.replay 0 (0, 0)
  timedImage.application.includePending { published with pool := replay.state } (0, 0)

/-- Replaying the accepted cleartext packet is retained as rejected traffic
and cannot overwrite the completed conditional publication. -/
theorem replay_cannot_overwrite :
    replayed.application = published.application ∧
      replayed.receipts = published.receipts ++ [((0, 0), false)] ∧
      Store.getAs replayed.application.memory.store 2 (.option .bool) =
        some (some false) := by
  exact ⟨rfl, rfl, rfl⟩

end VegasTests.ConditionalDefaultApplication

/-- info: 'VegasTests.ConditionalDefaultApplication.default_run_reaches_terminal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ConditionalDefaultApplication.default_run_reaches_terminal

/-- info: 'VegasTests.ConditionalDefaultApplication.disposition_forms_are_separate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ConditionalDefaultApplication.disposition_forms_are_separate
