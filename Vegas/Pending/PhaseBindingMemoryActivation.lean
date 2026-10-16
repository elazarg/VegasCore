/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingForeignCompletionMemory

/-! # Original private leak draws through all-value physical memory -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A player activation samples the SAME original leak draw on both sides.
The complete learned network and scheduler entry agree, and both private words
are unchanged. No target activation outcome or new observation law is assumed. -/
theorem activation_memory_coupling (memory : BindingShadow graph) (owner : Player)
    (owned : memory.OwnBindings owner) (left right : (app).Execution)
    (application : left.application = memory.phased owner right.application)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall) (actor : Player) :
    ∃ paired : PMF ((app).Execution × (app).Execution),
      paired.map Prod.fst = left.environmentStep app (.activate actor) ∧
      paired.map Prod.snd = right.environmentStep app (.activate actor) ∧
      ∀ pair ∈ paired.support,
        pair.1.application = memory.phased owner pair.2.application ∧
        pair.1.network = pair.2.network ∧ pair.1.receipts = pair.2.receipts ∧
        pair.1.environmentRecall = pair.2.environmentRecall ∧
        pair.1.recall = left.recall ∧ pair.2.recall = right.recall := by
  let finish (physical : (app).Execution) (selected : Finset (MessageId Player)) :
      (app).Execution :=
    { physical with
      network := physical.network.learn actor selected
      environmentRecall := physical.environmentRecall ++
        [⟨physical.observeEnvironment app, .activate actor⟩] }
  let paired := (leaks actor left.network.pending).map fun selected =>
    (finish left selected, finish right selected)
  have before : left.observeEnvironment app = right.observeEnvironment app := by
    change (⟨left.network.publicView, left.application.publicView, left.receipts⟩ :
      (app).EnvironmentView) = ⟨_, _, _⟩
    rw [network, receipts, application, phased_publicView owned]
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
    refine ⟨application, ?_, receipts, ?_, rfl, rfl⟩
    · change left.network.learn actor selected = right.network.learn actor selected
      rw [network]
    · change left.environmentRecall ++ [_] = right.environmentRecall ++ [_]
      rw [service, before]

end Vegas.EventGraphRuntime.BindingShadow
