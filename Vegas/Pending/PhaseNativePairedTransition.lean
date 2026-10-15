/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativePlayerInput

/-! # Coupled native and physical protocol transition probability laws -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (nativeLeaks leaks plan)

/-- Native failures before normalization record exactly the owners excluded by
the corresponding actual physical transition. -/
def PairedPublicRecord (first : (N).ProtocolState) (second : (P).ProtocolState) : Prop :=
  match first, second with
  | none, none => True
  | some native, some physical => PublicExclusionRecord
      (⟨native.execution.application, physical.execution.application.current.excluded⟩ :
        RecoveryState graph)
  | _, _ => False

/-- Couple both actual protocol transition PMFs, preserving the complete native
projection until exclusion and the exact first-failure owner labels at exit. -/
theorem exists_paired_transition (bounds : MessageBounds graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
    (current : (P).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅)
    (joint : Player → Option (P).Action)
    (legal : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Legal (some current) joint) :
    ∃ paired : PMF ((N).ProtocolState × (P).ProtocolState),
      paired.map Prod.fst = (N).transition (inputs.map State.initial) horizon
        (nativeScheduler runtime leaks plan scheduler) (some (control runtime leaks plan current))
        (jointActions runtime leaks plan joint) ∧
      paired.map Prod.snd = (P).transition (inputs.map (PhaseRuntimeState.initial plan)) horizon
        scheduler (some current) joint ∧
      ∀ pair ∈ paired.support,
        ((∀ next, pair.2 = some next → next.execution.application.current.excluded = ∅) →
          pair.1 = protocolState runtime leaks plan pair.2) ∧
        PairedPublicRecord runtime leaks plan pair.1 pair.2 := by
  classical
  rcases current with ⟨remaining, actor, current⟩
  cases actor with
  | some who =>
      let response := (joint who).getD ⟨none⟩
      have permitted : response ∈ PhaseCount.onePacketActions runtime leaks bounds who
          (current.recall who) (current.observe P who) := by
        have localLegal := legal.2 who
        cases chosen : joint who with
        | none =>
            rw [chosen] at localLegal
            exact (localLegal rfl).elim
        | some actual =>
            rw [chosen] at localLegal
            have available : actual ∈ PhaseCount.onePacketActions runtime leaks bounds who
                (current.recall who) (current.observe P who) := localLegal.2
            simpa only [response, chosen, Option.getD_some] using available
      have same := respond_of_onePacket runtime leaks plan bounds current
        (PhaseCount.countRecall_history runtime leaks
          ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace))
        who response permitted
      let next : (P).ProtocolState := some ⟨remaining, none, current.respond P who response⟩
      refine ⟨PMF.pure (protocolState runtime leaks plan next, next), ?_, ?_, ?_⟩
      · rw [PMF.pure_map]
        change PMF.pure _ = PMF.pure _
        congr 1
        cases selected : joint who <;>
          simp only [next, protocolState, control, jointActions, selected, Option.map_none,
            Option.map_some, Option.getD_none, Option.getD_some]
        all_goals erw [same]
        all_goals simp [response, selected, action]
      · rw [PMF.pure_map]
        rfl
      · intro pair member
        cases (PMF.mem_support_pure_iff _ _).mp member
        refine ⟨fun _clear => rfl, ?_⟩
        have afterClear : (current.respond P who response).application.current.excluded = ∅ := by
          rcases response with ⟨transmission⟩
          cases transmission <;> exact clear
        have afterTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
            (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace next :=
          .extend trace joint legal (PMF.mem_support_pure_iff _ _ |>.mpr rfl)
        exact clear_publicRecord runtime leaks plan bounds inputs horizon scheduler afterTrace
          afterClear
  | none =>
      cases remaining with
      | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
      | succ remaining =>
          let commands := scheduler current.environmentRecall (current.observeEnvironment P)
          have existsKernel chosen := exists_paired_environmentStep runtime leaks plan bounds
            ordered maximal inputs horizon scheduler trace clear chosen
          let kernel chosen := Classical.choose (existsKernel chosen)
          have marginals chosen := Classical.choose_spec (existsKernel chosen)
          let package := fun chosen (pair : (N).Execution × (P).Execution) =>
            (some (⟨remaining, (command runtime leaks plan chosen).actor? N, pair.1⟩ : (N).Control),
              some (⟨remaining, chosen.actor? P, pair.2⟩ : (P).Control))
          refine ⟨commands.bind (fun chosen => (kernel chosen).map (package chosen)), ?_, ?_, ?_⟩
          · rw [PMF.map_bind]
            have schedulerEq := nativeScheduler_at_clear runtime leaks plan bounds inputs horizon
              scheduler trace clear
            change _ = (nativeScheduler runtime leaks plan scheduler
              (execution runtime leaks plan current).environmentRecall
              ((execution runtime leaks plan current).observeEnvironment N)).bind _
            rw [schedulerEq, PMF.bind_map]
            apply bind_congr_on_support
            intro chosen _supported
            rw [PMF.map_comp]
            have first := (marginals chosen).1
            change (kernel chosen).map Prod.fst = _ at first
            change _ = ((execution runtime leaks plan current).environmentStep N
              (command runtime leaks plan chosen)).map
                (fun next => some (⟨remaining, (command runtime leaks plan chosen).actor? N,
                  next⟩ : (N).Control))
            rw [← first, PMF.map_comp]
            rfl
          · rw [PMF.map_bind]
            change _ = commands.bind _
            apply bind_congr_on_support
            intro chosen _supported
            rw [PMF.map_comp]
            have second := (marginals chosen).2.1
            change (kernel chosen).map Prod.snd = _ at second
            rw [← second, PMF.map_comp]
            rfl
          · intro pair supported
            rw [PMF.mem_support_bind_iff] at supported
            obtain ⟨chosen, _chosen, supported⟩ := supported
            rw [PMF.mem_support_map_iff] at supported
            obtain ⟨result, supported, rfl⟩ := supported
            constructor
            · intro afterClear
              have same := (marginals chosen).2.2.1 result supported (afterClear _ rfl)
              have actorEq : (command runtime leaks plan chosen).actor? N = chosen.actor? P := by
                cases chosen <;> rfl
              simp only [package, protocolState]
              rw [same, actorEq]
              rfl
            · exact (marginals chosen).2.2.2 result supported

end Vegas.EventGraphRuntime.PhaseNativeProjection
