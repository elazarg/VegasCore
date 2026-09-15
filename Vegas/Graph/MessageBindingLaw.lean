/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessagePolicyLaws
import Vegas.Graph.MessageStepLaw
import Interaction.MessageApplicationImmediateService

/-! # Reserved inclusion realizes the graph's binding choice

The command compiler and native handler compose through the shared policy
runner. This statement retains the actual ledger and successful receipt; it
does not assume that acceptance simulates a graph step.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- A previously prepared canonical candidate is included with exactly its
immutable graph value. Arbitrary other pending messages remain permissible. -/
theorem compiled_bind_submit_include
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (name : VarId) (owner : Player) {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (tail : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner (.bind name owner fresh tail))
    (players : Player → runtime.application.PlayerPolicy)
    (execution : runtime.application.PolicyExecution)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (site clock enteredAt : Nat)
    (encoded : L.Val (R.result payload))
    (application : execution.native.application =
      .running (.bind name owner fresh tail) ideal values bindings candidates site clock enteredAt)
    (hplayer : players owner (execution.principalHistory owner)
      (MessageApplication.State.observe runtime.application execution.native owner) =
        compileAt runtime owner whole (.bind name owner fresh tail) policy site
          (execution.principalHistory owner)
          (MessageApplication.State.observe runtime.application execution.native owner))
    (prepared : preparedRaw (execution.principalHistory owner) site =
      some ⟨R.result payload, encoded⟩)
    (unsubmitted : submittedAt (execution.principalHistory owner) site = false)
    (candidate : candidates.lookup (owner, .prepared site) =
      .openable ⟨R.result payload, encoded⟩)
    (serialFresh : execution.native.pool.lookup
      (owner, execution.native.pool.nextSerial owner) = none) :
    (runtime.application.runPolicies players (runtime.application.includeLatestFrom owner)
      [.player owner, .environment] execution).map (fun out =>
        (out.native.application, out.native.pool.ledger, out.native.receipts)) =
      FinDist.pure
        (.running tail (VEnv.cons encoded ideal) (PublicValues.consSealed values)
            ((name, (owner, .prepared site)) :: bindings)
            (candidates.accept (owner, .prepared site)) (site + 1) clock clock,
          execution.native.pool.ledger ++
            [⟨(owner, execution.native.pool.nextSerial owner),
              .commitment site (owner, .prepared site)⟩],
          execution.native.receipts ++
            [((owner, execution.native.pool.nextSerial owner), true)]) := by
  apply runtime.application.submit_include_accepts players owner
    (.commitment site (owner, .prepared site)) execution _ ?_ serialFresh ?_
  · rw [hplayer]
    apply compileAt_bind_prepared runtime whole site name owner fresh tail policy
      (execution.principalHistory owner) _ _ ?_ prepared unsubmitted
    change execution.native.application.publicView.pc = site
    rw [application]
    rfl
  · change runtime.handle execution.native.application _ = _
    rw [application]
    exact runtime.handle_bind_openable fresh tail ideal values bindings candidates
      site clock enteredAt _ (owner, .prepared site) encoded rfl candidate

end Vegas.GraphRuntime
