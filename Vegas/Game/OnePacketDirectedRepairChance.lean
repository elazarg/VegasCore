/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketDirectedRepairResponse

/-! # Actual chance steps through directed binding repair

Every supported original public sample has a supported repaired sample retaining
the complete directed frame. The paired draw comes from the existing common-draw
coupling of the actual runtime sampler, rather than an assumed posterior law.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime
open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

namespace DirectedBindingFrame

variable {memory : BindingMemory (runtime setup) leaks} {owner : Player}
  {original repaired : (application setup leaks).Execution}

/-- A supported actual public draw has a supported repaired counterpart with the
same concrete private-memory frame. The original sample outcome is retained
jointly with the network, scheduler history, and all foreign decision inputs. -/
theorem sample_step (frame : DirectedBindingFrame memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (event : (graph setup).EventId) (ready : original.application.config.cut.Ready event)
    (payload : L.Ty) (law : EventGraph.PublicDist (graph setup).layout payload)
    (outputEq : (graph setup).outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .sample payload law)
    (node : nodeView (graph setup) event = .sample payload law outputEq codeEq)
    (nextOriginal : (application setup leaks).Execution)
    (left : nextOriginal ∈ (original.environmentStep (application setup leaks)
      (.application (.executeSample event))).support) :
    ∃ nextRepaired : (application setup leaks).Execution,
      nextRepaired ∈ (repaired.environmentStep (application setup leaks)
        (.application (.executeSample event))).support ∧
      DirectedBindingFrame memory owner nextOriginal nextRepaired := by
  obtain ⟨coupled, first, second, framed⟩ := frame.toFrame.sample_coupling onlyBindings
    event ready payload law outputEq codeEq node
  have firstSupport : nextOriginal ∈ (coupled.map Prod.fst).support := by
    rw [first]
    exact left
  obtain ⟨pair, supported, same⟩ := PMF.support_map .. ▸ firstSupport
  have right : pair.2 ∈ (repaired.environmentStep (application setup leaks)
      (.application (.executeSample event))).support := by
    rw [← second, PMF.support_map]
    exact ⟨pair, supported, rfl⟩
  refine ⟨pair.2, right, ?_⟩
  have nextFrame := framed pair supported
  rw [same] at nextFrame
  exact frame.environmentStep (.application (.executeSample event)) nextOriginal pair.2
    left right nextFrame

end DirectedBindingFrame

end Vegas
