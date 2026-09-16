/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PreparationInvariant
import Vegas.Pending.StepLaw

/-! # Accepted compiled commitments realize the prepared binding choice -/

noncomputable section
namespace Vegas.GraphRuntime

open Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

/-- Any packet successfully handled at a compiled owner's current binding is
forced to be the canonical current-site commitment. The handler then installs
exactly the choice encoded in the owner's immutable preparation. -/
theorem accepted_bind_installs_prepared_choice
    (runtime : GraphRuntime Player L Δ)
    (name : VarId) (owner : Player) {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst)
    (tail : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (execution : runtime.application.PolicyExecution)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (site clock enteredAt : Nat) (encoded : L.Val (R.result payload))
    (message : Message Player (Payload Player L)) (id : MessageId Player)
    (accepted : State Player L Δ)
    (application : execution.native.application =
      .running (.bind name owner fresh tail) ideal values bindings candidates
        site clock enteredAt)
    (invariant : PreparationInvariant runtime owner execution)
    (prepared : preparedRaw (execution.principalHistory owner) site =
      some ⟨R.result payload, encoded⟩)
    (lookup : execution.native.pool.lookup id = some message)
    (handled : runtime.handle execution.native.application message = some accepted) :
    message.payload = .commitment site (owner, .prepared site) ∧
      accepted = .running tail (VEnv.cons encoded ideal) (PublicValues.consSealed values)
        ((name, (owner, .prepared site)) :: bindings)
        (candidates.accept (owner, .prepared site)) (site + 1) clock clock := by
  rcases message with ⟨⟨senderId, serial⟩, wirePayload⟩
  rw [application] at handled
  cases wirePayload with
  | opening packetSite handle raw => simp [GraphRuntime.handle] at handled
  | withhold packetSite => simp [GraphRuntime.handle] at handled
  | malformed raw => simp [GraphRuntime.handle] at handled
  | commitment packetSite handle =>
      simp only [GraphRuntime.handle] at handled
      split at handled
      · rename_i acceptedConditions
        simp only [Bool.and_eq_true, decide_eq_true_eq] at acceptedConditions
        obtain ⟨⟨packetSiteEq, senderEq⟩, handleOwner⟩ := acceptedConditions
        subst packetSite
        change senderId = owner at senderEq
        subst senderId
        let message : Message Player (Payload Player L) :=
          ⟨(owner, serial), .commitment site handle⟩
        change execution.native.pool.lookup id = some message at lookup
        rcases invariant with ⟨authorship, agreement, commitments⟩
        have safe := authorship.2.1 message (List.mem_of_find?_eq_some lookup)
        have submitted : message.payload ∈ runtime.application.submittedPayloads
            (execution.principalHistory owner) := by
          change (runtime.application.submittedPayloads
            (execution.principalHistory message.id.1))[message.id.2]? =
              some message.payload at safe
          rw [List.getElem?_eq_some_iff] at safe
          rw [List.mem_iff_getElem]
          exact ⟨message.id.2, safe.1, safe.2⟩
        obtain ⟨canonical, _raw, _wasPrepared⟩ := commitments site handle submitted
        have candidate : candidates.lookup (owner, .prepared site) =
            .openable ⟨R.result payload, encoded⟩ := by
          have agrees := agreement site
          rw [prepared] at agrees
          rwa [application] at agrees
        constructor
        · simp only [canonical]
        · rw [canonical] at handled
          simp only [candidate, advanceBind, Raw.as?_mk, Option.getD_some] at handled
          exact (Option.some.inj handled).symm
      · contradiction

/-- The shared environment-policy inclusion of such an accepted arbitrary pool
identifier has the same exact application successor. This is independent of
which environment policy selected the identifier. -/
theorem environmentInclude_bind_installs_prepared_choice
    (runtime : GraphRuntime Player L Δ)
    (name : VarId) (owner : Player) {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst)
    (tail : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (execution next : runtime.application.PolicyExecution)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (site clock enteredAt : Nat) (encoded : L.Val (R.result payload))
    (message : Message Player (Payload Player L)) (id : MessageId Player)
    (accepted : State Player L Δ)
    (application : execution.native.application =
      .running (.bind name owner fresh tail) ideal values bindings candidates
        site clock enteredAt)
    (invariant : PreparationInvariant runtime owner execution)
    (prepared : preparedRaw (execution.principalHistory owner) site =
      some ⟨R.result payload, encoded⟩)
    (lookup : execution.native.pool.lookup id = some message)
    (handled : runtime.handle execution.native.application message = some accepted)
    (supported : next ∈ (runtime.application.environmentPolicyStep execution
      (.include id)).support) :
    message.payload = .commitment site (owner, .prepared site) ∧
      next.native.application =
        .running tail (VEnv.cons encoded ideal) (PublicValues.consSealed values)
          ((name, (owner, .prepared site)) :: bindings)
          (candidates.accept (owner, .prepared site)) (site + 1) clock clock := by
  obtain ⟨canonicalPacket, acceptedEq⟩ :=
    accepted_bind_installs_prepared_choice runtime name owner fresh tail execution ideal values
      bindings candidates site clock enteredAt encoded message id accepted application invariant
      prepared lookup handled
  have nativeMem : next.native ∈
      ((runtime.application.environmentPolicyStep execution (.include id)).map
        MessageInterface.PolicyExecution.native).support := by
    rw [GameTheory.Math.Probability.FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  rw [runtime.application.environmentStep_native] at nativeMem
  simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
    MessageApplication.step, GameTheory.Math.Probability.FinDist.mem_support_pure] at nativeMem
  rw [runtime.application.includePending_accept execution.native id message accepted lookup
    handled] at nativeMem
  exact ⟨canonicalPacket, (congrArg (fun state => state.application) nativeMem).trans
    acceptedEq⟩

end Vegas.GraphRuntime
