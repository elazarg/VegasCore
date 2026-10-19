/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalShadowNormalization
import Vegas.Pending.PhaseBindingOpaqueStep

/-! # Literal activation and pending-message draws under dynamic shadows

The original observation rule is sampled once on the identical pending pool.
No pending observation is erased and no independence from its contents is
assumed. Only the repairing owner's private application projection can differ.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Actual common-draw activation coupling after arbitrary prior recovery.
Each branch retains the full external prefix and the same logical mask. -/
theorem activation_external_coupling (memory : BindingShadow graph) (owner : Player)
    (owned : memory.OwnBindings owner) (left right : (app).Execution)
    (frame : PhaseStateFrame memory owner left.application right.application)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = right.recall who) (actor : Player) :
    ∃ paired : PMF ((app).Execution × (app).Execution),
      paired.map Prod.fst = left.environmentStep app (.activate actor) ∧
      paired.map Prod.snd = right.environmentStep app (.activate actor) ∧
      ∀ pair ∈ paired.support,
        PhaseStateFrame memory owner pair.1.application pair.2.application ∧
        pair.1.network = pair.2.network ∧
        pair.1.recall = left.recall ∧ pair.2.recall = right.recall ∧
        phaseExternalObservation runtime leaks owner pair.1 =
          phaseExternalObservation runtime leaks owner pair.2 := by
  let finish (before : (app).Execution) (selected : Finset (MessageId Player)) :
      (app).Execution :=
    { before with
      network := before.network.learn actor selected
      environmentRecall := before.environmentRecall ++
        [⟨before.observeEnvironment app, .activate actor⟩] }
  let paired := (leaks actor left.network.pending).map fun selected =>
    (finish left selected, finish right selected)
  have before : left.observeEnvironment app = right.observeEnvironment app := by
    change (⟨left.network.publicView, left.application.publicView, left.receipts⟩ :
      (app).EnvironmentView) = ⟨_, _, _⟩
    rw [network, receipts, frame.publicView owned]
    rfl
  refine ⟨paired, ?_, ?_, ?_⟩
  · simp only [paired, ReactiveApplication.Execution.environmentStep, PMF.map_comp]
    rfl
  · simp only [paired, ReactiveApplication.Execution.environmentStep, PMF.map_comp]
    change (leaks actor left.network.pending).map (finish right) = _
    rw [network]
    rfl
  · intro pair supported
    obtain ⟨selected, _drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    have nextNetwork : (finish left selected).network = (finish right selected).network := by
      change left.network.learn actor selected = right.network.learn actor selected
      rw [network]
    have nextService : (finish left selected).environmentRecall =
        (finish right selected).environmentRecall := by
      change left.environmentRecall ++ [_] = right.environmentRecall ++ [_]
      rw [service, before]
    refine ⟨frame, nextNetwork, rfl, rfl, ?_⟩
    exact phaseExternalObservation_congr runtime leaks _ _ owner nextNetwork receipts nextService
      (frame.publicView owned) (frame.playerView_other owned) recalled

end Vegas.EventGraphRuntime.BindingShadow
