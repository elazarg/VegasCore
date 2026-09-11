/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationBindingTimeouts
import Vegas.Compile.BindingTimeoutCompilation
import VegasTests.ApplicationBindingDefault
import VegasTests.GeneratedBindingPolicy

/-! # Generated binding-timeout regressions

These checks use the actual application-image message handler and shared
transactional inclusion.  The source-certified fallback is attached to the
generated initial binding instruction. They cover binding admission, deadline
checks, and replay; conditional-publication continuation is tested separately.
-/

noncomputable section

namespace VegasTests.ApplicationBindingTimeouts

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction Interaction.MessageApplication
open VegasTests.PersistentDisclosure VegasTests.GeneratedPersistentDisclosure
open VegasTests.GeneratedBindingPolicy

abbrev Player := TestPlayer
abbrev Payload := ApplicationImage.Payload Player simpleExpr

def timeout : PublicFallbackCode simpleExpr .bool where
  deadline := 10
  value := ApplicationBindingDefault.fallback.compiled source.fresh compilerInitial

def timedCode : BindingCode Player simpleExpr :=
  { code with timeout := some timeout }

/-- A minimal executable image retaining the source-generated binding code. -/
def timedImage : ApplicationImage Player simpleExpr where
  instructions := [.bind timedCode]

def untimedImage : ApplicationImage Player simpleExpr where
  instructions := [.bind code]

def prepared (clock : Nat) : ApplicationImage.State Player simpleExpr :=
  (((ApplicationImage.State.initial
    (ApplicationImage.Memory.initial GeneratedPersistentDisclosure.compiled.graph)).register
    0 0 ⟨.bool, true⟩).advance clock)

def submitAndInclude (runtime : ApplicationImage Player simpleExpr)
    (state : ApplicationImage.State Player simpleExpr) (sender : Player)
    (payload : ApplicationImage.Payload Player simpleExpr) : runtime.application.State :=
  let submitted := (MessagePool.empty Player Payload).submit sender payload
  runtime.application.includePending ⟨state, submitted.2, []⟩ submitted.1

def atBoundary := submitAndInclude timedImage (prepared 10) 1 (.expireBinding 0)
def expired := submitAndInclude timedImage (prepared 11) 1 (.expireBinding 0)

/-- The deadline is strict. Rejected traffic is still included in the ledger
and receives a negative receipt. -/
theorem boundary_rejects :
    atBoundary.application = prepared 10 ∧
      atBoundary.receipts = [((1, 0), false)] ∧
      atBoundary.pool.ledger = [⟨(1, 0), .expireBinding 0⟩] := by
  exact ⟨rfl, rfl, rfl⟩

/-- An overdue fallback packet authored by a nonowner is accepted when the
runtime includes it. It records the certified public value without replacing
the owner's private preparation by a handle or by the fallback. Message
authorship and environment-controlled inclusion remain distinct authorities. -/
theorem overdue_accepts :
    expired.receipts = [((1, 0), true)] ∧
      expired.application.memory.accepted 0 =
        some (.publicDefault ⟨.bool, false⟩) ∧
      expired.application.memory.done 0 = true ∧
      expired.application.memory.store 0 = none ∧
      expired.application.prepared.lookup (0, 0) = some ⟨.bool, true⟩ ∧
      expired.application.frozen 0 = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def replayed : timedImage.application.State :=
  let replay := expired.pool.replay 1 (1, 0)
  timedImage.application.includePending { expired with pool := replay.state } (1, 0)

/-- Replaying the already accepted expiry cannot execute the binding again. -/
theorem replay_cannot_overwrite :
    replayed.application = expired.application ∧
      replayed.receipts = expired.receipts ++ [((1, 0), false)] := by
  exact ⟨rfl, rfl⟩

def lateBinding : timedImage.application.State :=
  let submitted := expired.pool.submit 0 (.binding 0 (0, 0))
  timedImage.application.includePending { expired with pool := submitted.2 } submitted.1

/-- An ordinary binding arriving after the default is retained as rejected
traffic and cannot turn the public fallback into an opaque disposition. -/
theorem late_binding_cannot_overwrite :
    lateBinding.application = expired.application ∧
      lateBinding.receipts = expired.receipts ++ [((0, 0), false)] ∧
      lateBinding.application.memory.accepted 0 =
        some (.publicDefault ⟨.bool, false⟩) := by
  exact ⟨rfl, rfl, rfl⟩

def boundFirst : timedImage.application.State :=
  submitAndInclude timedImage (prepared 11) 0 (.binding 0 (0, 0))

def expiryAfterBinding : timedImage.application.State :=
  let submitted := boundFirst.pool.submit 1 (.expireBinding 0)
  timedImage.application.includePending { boundFirst with pool := submitted.2 } submitted.1

/-- The ordinary canonical binding wins the race when included first. Its
accepted handle and frozen preparation prevent the fallback from installing. -/
theorem binding_first_blocks_expiry :
    boundFirst.application.memory.accepted 0 = some (.opaque (0, 0)) ∧
      boundFirst.application.frozen 0 = some ⟨.bool, true⟩ ∧
      expiryAfterBinding.application = boundFirst.application ∧
      expiryAfterBinding.receipts = boundFirst.receipts ++ [((1, 0), false)] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

def noTimeout := submitAndInclude untimedImage (prepared 11) 1 (.expireBinding 0)

/-- A binding instruction without timeout code rejects the new packet. -/
theorem absent_timeout_rejects :
    noTimeout.application = prepared 11 ∧
      noTimeout.receipts = [((1, 0), false)] := by
  exact ⟨rfl, rfl⟩

def blockedCode : BindingCode Player simpleExpr :=
  { timedCode with requires := [7] }

def blockedImage : ApplicationImage Player simpleExpr where
  instructions := [.bind blockedCode]

def missingPrerequisite :=
  submitAndInclude blockedImage (prepared 11) 1 (.expireBinding 0)

/-- A passed deadline does not bypass generated public prerequisites. -/
theorem missing_prerequisite_rejects :
    missingPrerequisite.application = prepared 11 ∧
      missingPrerequisite.receipts = [((1, 0), false)] := by
  exact ⟨rfl, rfl⟩

/-- The complete generated image, decorated at its initial source decision. -/
def generatedTimedImage : ApplicationImage Player simpleExpr :=
  ApplicationBindingDefault.fallback.installBindingTimeout
    source.fresh compilerInitial 10 image

theorem generated_lookup : generatedTimedImage.lookup 0 = some (.bind timedCode) := by
  apply ApplicationBindingDefault.fallback.lookup_installBindingTimeout
    source.fresh compilerInitial 10 image 0
  apply applicationPlan.image_lookup_of_mem (fun _ => 10) (.bind code)
  change _ ∈ [ApplicationInstruction.bind code, _, _, _, _, _]
  simp

def generatedPending : generatedTimedImage.application.State :=
  ⟨prepared 11, ((MessagePool.empty Player Payload).submit 1 (.expireBinding 0)).2, []⟩

/-- A real pending expiry in the complete generated artifact advances the
original source decision to false, despite the owner's private preparation of true. -/
theorem generated_expiry_source_successor :
    ∃ next : CoupledAt GeneratedPersistentDisclosure.compiled.graph BindingSourceCoupling.nextBuild,
      next.current.source = source.env.cons false ∧
        (generatedTimedImage.application.includePending generatedPending (1, 0)).application.Refines
          next.current.graph.1 := by
  have hrefines : generatedPending.application.Refines
      BindingSourceCoupling.checkpoint.current.graph.1 :=
    ((Vegas.ApplicationImage.State.initial_refines
      GeneratedPersistentDisclosure.compiled.graph).register
      0 0 ⟨.bool, true⟩).advance 11
  have hresult := SourceDecisionSite.PublicFallback.expiry_include_source_coupling
    (P := Player) (L := simpleExpr) (Γ := []) (name := 0) (who := 0) (ty := .bool)
    (.constBool true) _ ApplicationBindingDefault.fallback source.fresh compilerInitial 10
    BindingSourceCoupling.checkpoint generatedTimedImage generatedPending hrefines
    (by decide) 0 generated_lookup (1, 0) (by rfl)
  obtain ⟨next, hsource, hnext, _⟩ := hresult
  exact ⟨next, hsource, hnext⟩

end VegasTests.ApplicationBindingTimeouts

/-- info: 'VegasTests.ApplicationBindingTimeouts.overdue_accepts' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationBindingTimeouts.overdue_accepts

/-- info: 'VegasTests.ApplicationBindingTimeouts.binding_first_blocks_expiry' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationBindingTimeouts.binding_first_blocks_expiry

/-- info: 'VegasTests.ApplicationBindingTimeouts.generated_expiry_source_successor'
depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationBindingTimeouts.generated_expiry_source_successor
