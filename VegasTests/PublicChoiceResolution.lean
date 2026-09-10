/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.PublicChoiceResolution
import VegasTests.PublicChoiceSourceCoupling
import Interaction.MessagePoolFreshness

/-! # Generated public-expression timeout regression

The fallback reads the public source input; it is not an arbitrary constant
chosen from a nonempty guard. A non-owner submits expiry through the shared
policy runtime; its subsequent inclusion has the exact written-source successor.
-/

noncomputable section

namespace VegasTests.PublicChoiceResolution

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.ApplicationImage

def resolution : PublicResolutionChoice firstSite where
  expr := .var 0 .here
  legal := by
    intro env
    simp [firstSite, firstGuard, evalGuard, evalExpr]
    rfl

def timedImage : Vegas.ApplicationImage (Fin 2) simpleExpr :=
  resolution.install source.fresh compilerInitial 10 image

def timeoutCode : PublicChoiceCode (Fin 2) simpleExpr :=
  resolution.timeoutCode source.fresh compilerInitial 10

theorem timeout_lookup : timedImage.lookup firstAddress = some (.publicChoice timeoutCode) :=
  resolution.lookup_install source.fresh compilerInitial 10 image firstAddress image_lookup_first

/-- Vary the actual public input while retaining the same emitted expression. -/
def publicInputState (input : Bool) : Vegas.ApplicationImage.State (Fin 2) simpleExpr :=
  { initialState.advance 11 with memory :=
      { (initialState.advance 11).memory with
        store := initialState.memory.store.set 0 ⟨.bool, input⟩ } }

/-- The real handler follows both public input values, not a constant default. -/
theorem handler_tracks_public_input (input : Bool) :
    timedImage.handle (publicInputState input) ⟨(1, 0), .expireChoice firstAddress⟩ =
      some ((publicInputState input).publish timeoutCode input) := by
  cases input <;> rfl

def start (clock : Nat) : timedImage.application.PolicyExecution :=
  PolicyExecution.initial timedImage.application
    (MessageApplication.State.initial timedImage.application (initialState.advance clock))

def players : Fin 2 → timedImage.application.PlayerPolicy :=
  fun player _ _ =>
    if player = 1 then FinDist.pure (.submit (.expireChoice firstAddress))
    else FinDist.pure .wait

def environment : timedImage.application.EnvironmentPolicy :=
  fun _ _ => FinDist.pure (.include (1, 0))

/-- Reaching the deadline does not make the strict timeout eligible. -/
theorem at_deadline_rejects :
    timedImage.handle (start 10).native.application
      ⟨(1, 0), .expireChoice firstAddress⟩ = none := by
  rfl

/-- The undecorated generated code still rejects the same permissionless packet. -/
theorem undecorated_rejects :
    image.handle (initialState.advance 11) ⟨(1, 0), .expireChoice firstAddress⟩ = none :=
  image.handle_expireChoice_no_timeout _ firstAddress firstCode image_lookup_first (1, 0) rfl

private theorem expiry_run :
    timedImage.application.runPolicies players environment [.player 1, .environment] (start 11) =
      (timedImage.application.playerStep 1 (start 11)
        (.submit (.expireChoice firstAddress))).bind fun submitted =>
          timedImage.application.environmentPolicyStep submitted (.include (1, 0)) := by
  simp [MessageApplication.runPolicies, MessageApplication.invoke, players, environment]

/-- A real non-owner expiry run executes the source's guarded public choice.
The owner's history remains empty: no owner command is forged or inserted. -/
theorem other_sender_source_successor
    (included : timedImage.application.PolicyExecution)
    (hincluded : included ∈ (timedImage.application.runPolicies players environment
      [.player 1, .environment] (start 11)).support) :
    included.principalHistory 0 = [] ∧
      ∃ next : CoupledAt ApplicationImage.compiled.graph PublicChoiceSourceCoupling.nextBuild,
        next.current.source = (source.env.cons true).cons true ∧
          included.native.application.Refines next.current.graph.1 := by
  rw [expiry_run] at hincluded
  simp only [FinDist.support_bind, Set.mem_iUnion] at hincluded
  obtain ⟨submitted, hsubmitted, hincluded⟩ := hincluded
  have hnative : submitted.native ∈ ((timedImage.application.playerStep 1 (start 11)
      (.submit (.expireChoice firstAddress))).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨submitted, hsubmitted, rfl⟩
  rw [timedImage.application.playerStep_native] at hnative
  simp only [PlayerCommand.toAction, MessageApplication.step,
    FinDist.mem_support_pure] at hnative
  have happlication : submitted.native.application = (start 11).native.application := by
    simpa using congrArg MessageInterface.State.application hnative
  have hlookup : submitted.native.pool.lookup (1, 0) =
      some ⟨(1, 0), .expireChoice firstAddress⟩ := by
    rw [hnative]
    exact (start 11).native.pool.lookup_submit_fresh 1 (.expireChoice firstAddress) (by rfl)
  have hrefines : submitted.native.application.Refines
      PublicChoiceSourceCoupling.checkpoint.current.graph.1 := by
    rw [happlication]
    exact (Vegas.ApplicationImage.State.initial_refines ApplicationImage.compiled.graph).advance 11
  have hresult := PublicResolutionChoice.expiry_include_source_coupling
    (P := Fin 2) (L := simpleExpr) (Γ := InitialContext)
    (name := 1) (publicName := 2) (who := 0) (ty := .bool)
    firstGuard firstTail resolution source.fresh compilerInitial 10
    PublicChoiceSourceCoupling.checkpoint timedImage submitted included
    hrefines first_publicly_validatable (by rw [happlication]; decide)
    firstAddress timeout_lookup (1, 0) hlookup hincluded
  rcases hresult with ⟨_, hhistory, _, _, next, hsource, hrefinesNext⟩
  refine ⟨?_, next, hsource, hrefinesNext⟩
  rw [hhistory]
  exact timedImage.application.playerStep_other_history 1 0 (by decide)
    (start 11) (.submit (.expireChoice firstAddress)) submitted hsubmitted

/-- An accepted timeout cannot be overwritten by a replayed expiry request. -/
theorem expiry_after_publication_rejects (id : MessageId (Fin 2)) :
    timedImage.handle (initialState.publish timeoutCode true)
      ⟨id, .expireChoice firstAddress⟩ = none :=
  timedImage.handle_expireChoice_after_publication initialState firstAddress timeoutCode
    timeout_lookup id true

end VegasTests.PublicChoiceResolution

/-- info: 'VegasTests.PublicChoiceResolution.other_sender_source_successor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PublicChoiceResolution.other_sender_source_successor
