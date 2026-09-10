/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedOwnerFrame
import VegasTests.WindowedSourceCoverage

/-! # Owner-frame regression under raw foreign traffic -/

noncomputable section

namespace VegasTests.WindowedOwnerFrame

open Vegas Vegas.EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability
open VegasTests.WindowedSourceCoverage

abbrev Payload := ApplicationImage.Payload TestPlayer simpleExpr

def owner : TestPlayer := 0
def other : TestPlayer := 1
def slot : Nat := GeneratedBindingPolicy.code.sourceSlot

def canonical : Payload := .binding GeneratedBindingPolicy.code.node (owner, slot)

def ownerRegistered : runtime.application.PolicyExecution :=
  { initial with native := { initial.native with
      application := { initial.native.application with
        base := ({ initial.native.application.base with
          prepared := IdealCommitments.empty }).register owner slot ⟨.bool, true⟩ }
      pool := MessagePool.empty TestPlayer Payload } }

def start : runtime.application.PolicyExecution :=
  { ownerRegistered with native := { ownerRegistered.native with
      pool := (ownerRegistered.native.pool.submit owner canonical).2 } }

def constantPlayers (command : runtime.application.PlayerCommand) :
    TestPlayer → runtime.application.PlayerPolicy :=
  fun _ _ _ => FinDist.pure command

/-- This execution is genuinely supported by three raw player invocations.
The owner frame retains hidden preparation, allocation, and the previously
pending packet, although unrelated submission makes the complete pool differ. -/
theorem raw_foreign_traffic_preserves_owner_frame
    (registered submitted final : runtime.application.PolicyExecution)
    (hregistered : registered ∈ (runtime.application.playerStep other start
      (.privateCommand (.register slot ⟨.bool, false⟩))).support)
    (hsubmitted : submitted ∈ (runtime.application.playerStep other registered
      (.submit (.malformed [99]))).support)
    (hreplayed : final ∈ (runtime.application.playerStep other submitted
      (.replay (other, 0))).support) :
    final.native.application.base.prepared.lookup (owner, slot) =
        some ⟨.bool, true⟩ ∧
      final.native.pool.nextSerial owner = 1 ∧
      final.native.pool.lookup (owner, 0) = some ⟨(owner, 0), canonical⟩ ∧
      final.native.pool ≠ start.native.pool := by
  have hregisteredRun : registered ∈ (runtime.application.runPolicies
      (constantPlayers (.privateCommand (.register slot ⟨.bool, false⟩)))
      (runtime.blockEnvironment [owner, other]) [.player other] start).support := by
    simpa [constantPlayers, MessageApplication.runPolicies, MessageApplication.invoke]
      using hregistered
  have hsubmittedRun : submitted ∈ (runtime.application.runPolicies
      (constantPlayers (.submit (.malformed [99])))
      (runtime.blockEnvironment [owner, other]) [.player other] registered).support := by
    simpa [constantPlayers, MessageApplication.runPolicies, MessageApplication.invoke]
      using hsubmitted
  have hreplayedRun : final ∈ (runtime.application.runPolicies
      (constantPlayers (.replay (other, 0)))
      (runtime.blockEnvironment [owner, other]) [.player other] submitted).support := by
    simpa [constantPlayers, MessageApplication.runPolicies, MessageApplication.invoke]
      using hreplayed
  have frame1 := runtime.runPolicies_other_frame owner
    (constantPlayers (.privateCommand (.register slot ⟨.bool, false⟩)))
    (runtime.blockEnvironment [owner, other]) [.player other] (by simp)
    (by simp [owner, other]) start registered hregisteredRun
  have frame2 := runtime.runPolicies_other_frame owner
    (constantPlayers (.submit (.malformed [99])))
    (runtime.blockEnvironment [owner, other]) [.player other] (by simp)
    (by simp [owner, other]) registered submitted hsubmittedRun
  have frame3 := runtime.runPolicies_other_frame owner
    (constantPlayers (.replay (other, 0)))
    (runtime.blockEnvironment [owner, other]) [.player other] (by simp)
    (by simp [owner, other]) submitted final hreplayedRun
  have hpreparedStart : start.native.application.base.prepared.lookup (owner, slot) =
      some ⟨.bool, true⟩ := by
    simp [start, ownerRegistered, owner, slot, ApplicationImage.State.register,
      IdealCommitments.sealValue, IdealCommitments.lookup, IdealCommitments.empty]
  have hserialStart : start.native.pool.nextSerial owner = 1 := by
    simp [start, ownerRegistered, owner, canonical, MessagePool.submit, MessagePool.empty]
  have hlookupStart : start.native.pool.lookup (owner, 0) =
      some ⟨(owner, 0), canonical⟩ := by
    simp [start, ownerRegistered, owner, canonical, MessagePool.lookup,
      MessagePool.submit, MessagePool.empty]
  refine ⟨(frame3.2.1 slot).trans ((frame2.2.1 slot).trans
      ((frame1.2.1 slot).trans hpreparedStart)),
    frame3.2.2.1.trans (frame2.2.2.1.trans (frame1.2.2.1.trans hserialStart)),
    frame3.2.2.2 _ _ (frame2.2.2.2 _ _
      (frame1.2.2.2 (owner, 0) ⟨(owner, 0), canonical⟩ hlookupStart)), ?_⟩
  intro hpools
  have hlength := congrArg (fun pool : MessagePool TestPlayer Payload => pool.pending.length) hpools
  simp only [MessageApplication.playerStep, MessageApplication.advance,
    PlayerCommand.toAction, MessageApplication.step, FinDist.pure_bind,
    FinDist.mem_support_pure] at hregistered hsubmitted hreplayed
  subst registered
  subst submitted
  subst final
  simp [start, ownerRegistered, owner, other, slot, canonical, MessagePool.submit,
    MessagePool.replay, MessagePool.observe, MessagePool.View.known?,
    MessagePool.empty] at hlength

end VegasTests.WindowedOwnerFrame
