/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedApplication
import Interaction.MessageApplicationLocality

/-! # Owner-local state through other players' polls

Private registrations are owner-scoped. Other players' polls therefore preserve
an owner's prepared slots as well as public state and accepted snapshots. The
message runner separately preserves the owner's allocation counter and every
existing pending lookup. These are native-state facts, not consequences of the
owner's observation: preparations and counters are not exposed in that view.
-/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Arbitrary other-player polls retain exactly the state needed to service an
owner's submitted commitment. They may add pending traffic and rebroadcast
messages, but cannot replace an already-selected envelope or register a value
in the owner's namespace. No delivery or inclusion occurs in this segment. -/
theorem runPolicies_other_frame (runtime : WindowedApplication P L) (owner : P)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (henvironment : Invocation.environment ∉ schedule)
    (howner : Invocation.player owner ∉ schedule)
    (execution next : runtime.application.PolicyExecution)
    (hnext : next ∈
      (runtime.application.runPolicies players environment schedule execution).support) :
    (next.native.application.base.memory, next.native.application.active,
      next.native.application.base.frozen) =
        (execution.native.application.base.memory, execution.native.application.active,
          execution.native.application.base.frozen) ∧
      (∀ slot, next.native.application.base.prepared.lookup (owner, slot) =
        execution.native.application.base.prepared.lookup (owner, slot)) ∧
      next.native.pool.nextSerial owner = execution.native.pool.nextSerial owner ∧
      ∀ id message, execution.native.pool.lookup id = some message →
        next.native.pool.lookup id = some message := by
  let project (state : State P L) :=
    ((state.base.memory, state.active, state.base.frozen),
      fun slot => state.base.prepared.lookup (owner, slot))
  have hprivate : ∀ state actor command, owner ≠ actor →
      project (runtime.application.privateStep state actor command) = project state := by
    intro state actor command hne
    cases command with
    | register slot value =>
        apply Prod.ext
        · rfl
        · funext selected
          change (state.base.prepared.sealValue actor slot value).state.lookup (owner, selected) =
            state.base.prepared.lookup (owner, selected)
          unfold IdealCommitments.sealValue
          split
          · rfl
          · simp only [IdealCommitments.lookup, hne, false_and, ↓reduceIte]
  obtain ⟨hproject, hserial, hlookup⟩ := runtime.application.runPolicies_other_frame owner
    project hprivate players environment schedule henvironment howner execution next hnext
  exact ⟨congrArg Prod.fst hproject, fun slot => congrFun (congrArg Prod.snd hproject) slot,
    hserial, hlookup⟩

/-- A fresh private registration followed by submission retains its exact
value through arbitrary polls of other principals. Other traffic cannot fill
the owner's slot before registration or replace it afterwards. -/
theorem runPolicies_register_submit_prepared
    (runtime : WindowedApplication P L) (owner : P) (slot : Nat) (value : TypedValue L)
    (payload : ApplicationImage.Payload P L)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (before after : List (@Invocation P))
    (hbeforeEnvironment : Invocation.environment ∉ before)
    (hbeforeOwner : Invocation.player owner ∉ before)
    (hafterEnvironment : Invocation.environment ∉ after)
    (hafterOwner : Invocation.player owner ∉ after)
    (execution polled : runtime.application.PolicyExecution)
    (hempty : execution.native.application.base.prepared.lookup (owner, slot) = none)
    (hbranch : polled ∈
      ((runtime.application.runPolicies players environment before execution).bind fun middle =>
        (runtime.application.playerStep owner middle
          (.privateCommand (.register slot value))).bind fun registered =>
            (runtime.application.playerStep owner registered (.submit payload)).bind
              fun submitted =>
                runtime.application.runPolicies players environment after submitted).support) :
    polled.native.application.base.prepared.lookup (owner, slot) = some value := by
  simp only [FinDist.support_bind, Set.mem_iUnion] at hbranch
  obtain ⟨middle, hmiddle, registered, hregistered, submitted, hsubmitted, hafter⟩ := hbranch
  have hbeforeFrame := runtime.runPolicies_other_frame owner players environment before
    hbeforeEnvironment hbeforeOwner execution middle hmiddle
  have hafterFrame := runtime.runPolicies_other_frame owner players environment after
    hafterEnvironment hafterOwner submitted polled hafter
  rw [hafterFrame.2.1 slot]
  have hmiddleEmpty : middle.native.application.base.prepared.lookup (owner, slot) = none :=
    (hbeforeFrame.2.1 slot).trans hempty
  simp only [MessageApplication.playerStep, PlayerCommand.toAction,
    MessageApplication.advance, MessageApplication.step, FinDist.pure_bind,
    FinDist.mem_support_pure] at hregistered hsubmitted
  subst registered
  subst submitted
  exact (IdealCommitments.seal_first middle.native.application.base.prepared
    owner slot value hmiddleEmpty).2

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.runPolicies_other_frame' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_other_frame

/-- info: 'Vegas.WindowedApplication.runPolicies_register_submit_prepared'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_register_submit_prepared
