/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedOwnedCheckpoint
import VegasTests.GeneratedBindingPolicy

/-! # Paired execution of an actual focal-owned checkpoint block

This checks information agreement across the first complete generated block
of the persistent-disclosure application.  It is a paired-block regression,
not a settlement theorem: timeout selectors are absent and no terminal
resolution is assumed.
-/

noncomputable section

namespace VegasTests.WindowedOwnedCheckpoint

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.PersistentDisclosure
open VegasTests.GeneratedPersistentDisclosure

def deadlineOf : Nat → Nat := fun _ => 10

def noBinding (code : BindingCode TestPlayer simpleExpr) :
    Option (PublicFallbackCode simpleExpr code.ty) := none

def noChoice (code : PublicChoiceCode TestPlayer simpleExpr) :
    Option (PublicFallbackCode simpleExpr code.guard.ty) := none

def windowOf : Nat → Nat := fun _ => 10

def runtime : WindowedApplication TestPlayer simpleExpr :=
  applicationPlan.windowed deadlineOf noBinding noChoice windowOf

def initial : runtime.application.PolicyExecution :=
  applicationPlan.windowedInitialExecution deadlineOf noBinding noChoice windowOf

def replacement
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand) : runtime.application.PlayerPolicy :=
  fun history view => FinDist.pure (command history view)

def players (profile : SourceBehavioralProfile source.prog)
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand) :
    TestPlayer → runtime.application.PlayerPolicy :=
  applicationPlan.windowedPlayers profile deadlineOf noBinding noChoice windowOf 0
    (replacement command)

/-- Any two supported executions of the actual initial binding block retain
focal policy agreement.  The whole source profile and every command selected
by the pure raw focal policy remain arbitrary; the other player uses the
generated reference lift. -/
theorem initial_owned_block_agreement
    (profile : SourceBehavioralProfile source.prog)
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (left right : runtime.application.PolicyExecution)
    (hleft : left ∈ (runtime.application.runPolicies (players profile command)
      (runtime.blockEnvironment [0, 1])
      (WindowedApplication.blockInvocations [0, 1]) initial).support)
    (hright : right ∈ (runtime.application.runPolicies (players profile command)
      (runtime.blockEnvironment [0, 1])
      (WindowedApplication.blockInvocations [0, 1]) initial).support) :
    WindowedApplication.PolicyAgreement runtime 0 left right := by
  have checkpoint := ApplicationPlan.WindowedCheckpoint.initial
    DisclosureAccounting.persistentChecked applicationPlan profile deadlineOf noBinding
      noChoice windowOf (runtime.blockService [0, 1]) 0 (replacement command)
  have agreement : WindowedApplication.PolicyAgreement runtime 0 initial initial :=
    ⟨⟨ApplicationImage.State.AgreesFor.refl _ _, rfl⟩, rfl, rfl, rfl⟩
  let rest := (applicationPlan.instructions deadlineOf).tail
  have hhead : applicationPlan.instructions deadlineOf =
      .bind GeneratedBindingPolicy.code :: rest := by rfl
  exact checkpoint.owned_block_agreement checkpoint agreement command rfl
    (.bind GeneratedBindingPolicy.code) rest hhead rfl (by decide) left right hleft hright

end VegasTests.WindowedOwnedCheckpoint

/-- info: 'VegasTests.WindowedOwnedCheckpoint.initial_owned_block_agreement' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedOwnedCheckpoint.initial_owned_block_agreement
