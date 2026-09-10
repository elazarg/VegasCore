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

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.runPolicies_other_frame' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_other_frame
