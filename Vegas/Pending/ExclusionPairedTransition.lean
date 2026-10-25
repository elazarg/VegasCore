/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionClearHistory

/-! # Coupled actual protocol transitions up to permanent exclusion

The coupling retains both marginals and the exact first excluded-owner record,
including outcomes at which recovery automatically completes later events.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- The native outcome before automatic completion records exactly the owners
excluded in the paired recovery outcome. -/
def PairedExclusionRecord (first : (runtime.reactiveApplication leaks).ProtocolState)
    (second : (runtime.recoveryApplication leaks).ProtocolState) : Prop :=
  match first, second with
  | none, none => True
  | some native, some recovery => ExclusionEvidence 0 ∅ (⟨native.execution.application,
      recovery.execution.application.excluded⟩ : RecoveryState graph)
  | _, _ => False

/-- Couple the actual transition laws from a clear initialized recovery prefix,
with arbitrary player responses and the actual projected scheduler. -/
theorem exists_paired_transition (initial : PMF (RecoveryState graph)) (horizon : Nat)
    (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    (current : (runtime.recoveryApplication leaks).Control)
    (trace : ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).Trace
      (some current)) (empty : current.execution.application.excluded = ∅)
    (valid : ExclusionEvidence 0 ∅ current.execution.application)
    (joint : Player → Option (runtime.recoveryApplication leaks).Action) :
    ∃ paired : PMF ((runtime.reactiveApplication leaks).ProtocolState ×
        (runtime.recoveryApplication leaks).ProtocolState),
      paired.map Prod.fst = (runtime.reactiveApplication leaks).transition
        (initial.map RecoveryState.native) horizon (nativeScheduler runtime leaks scheduler)
        (some (control runtime leaks current)) (jointActions runtime leaks joint) ∧
      paired.map Prod.snd = (runtime.recoveryApplication leaks).transition initial horizon scheduler
        (some current) joint ∧
      ∀ pair ∈ paired.support,
        ((∀ next, pair.2 = some next → next.execution.application.excluded = ∅) →
          pair.1 = protocolState runtime leaks pair.2) ∧
        PairedExclusionRecord runtime leaks pair.1 pair.2 := by
  classical
  have restored := liftExecution_execution_of_history_clear runtime leaks initial horizon
    scheduler current trace empty
  rcases current with ⟨remaining, actor, current⟩
  cases actor with
  | some who =>
      let next : (runtime.recoveryApplication leaks).ProtocolState :=
        some ⟨remaining, none, current.respond (runtime.recoveryApplication leaks) who
          ((joint who).getD ⟨none⟩)⟩
      refine ⟨PMF.pure (protocolState runtime leaks next, next), ?_, ?_, ?_⟩
      · rw [PMF.pure_map]
        cases selected : joint who <;>
          simp only [next, ReactiveApplication.transition, control, protocolState,
            jointActions, selected, Option.map_none, Option.map_some, Option.getD_none,
            Option.getD_some, respond_of_empty runtime leaks current empty]
        rfl
      · rw [PMF.pure_map]
        rfl
      · intro pair member
        cases (PMF.mem_support_pure_iff _ _).mp member
        refine ⟨fun _clear => rfl, ?_⟩
        have invariant : (runtime.recoveryApplication leaks).Invariant (ExclusionEvidence 0 ∅) :=
          ⟨fun _ who submission valid => valid.submit who submission,
            fun _ message next valid accepted => valid.handle runtime message next accepted,
            fun _ command next valid reached => valid.environment runtime command next reached⟩
        have nextRecord := invariant.respond current who ((joint who).getD ⟨none⟩) valid
        exact nextRecord
  | none =>
      cases remaining with
      | zero =>
          refine ⟨PMF.pure (some (control runtime leaks ⟨0, none, current⟩),
            some ⟨0, none, current⟩), ?_, ?_, ?_⟩
          · rw [PMF.pure_map]; rfl
          · rw [PMF.pure_map]; rfl
          · intro pair member
            cases (PMF.mem_support_pure_iff _ _).mp member
            refine ⟨fun _clear => rfl, ?_⟩
            exact valid
      | succ remaining =>
          let commands := scheduler current.environmentRecall
            (current.observeEnvironment (runtime.recoveryApplication leaks))
          let kernel := pairedEnvironmentStep runtime leaks current
          have marginals chosen := pairedEnvironmentStep_spec runtime leaks current chosen
          let package := fun chosen (pair : (runtime.reactiveApplication leaks).Execution ×
              (runtime.recoveryApplication leaks).Execution) =>
            (some (⟨remaining, (command runtime leaks chosen).actor?
                (runtime.reactiveApplication leaks), pair.1⟩ :
                  (runtime.reactiveApplication leaks).Control),
              some (⟨remaining, chosen.actor? (runtime.recoveryApplication leaks), pair.2⟩ :
                (runtime.recoveryApplication leaks).Control))
          refine ⟨commands.bind (fun chosen => (kernel chosen).map (package chosen)), ?_, ?_, ?_⟩
          · rw [PMF.map_bind]
            have schedulerEq : nativeScheduler runtime leaks scheduler
                (execution runtime leaks current).environmentRecall
                ((execution runtime leaks current).observeEnvironment
                  (runtime.reactiveApplication leaks)) =
                commands.map (command runtime leaks) := by
              change (scheduler
                  (liftExecution runtime leaks (execution runtime leaks current)).environmentRecall
                  ((liftExecution runtime leaks
                    (execution runtime leaks current)).observeEnvironment
                      (runtime.recoveryApplication leaks))).map (command runtime leaks) = _
              rw [restored]
            change _ = (nativeScheduler runtime leaks scheduler
              (execution runtime leaks current).environmentRecall
              ((execution runtime leaks current).observeEnvironment
                (runtime.reactiveApplication leaks))).bind _
            rw [schedulerEq, PMF.bind_map]
            apply bind_congr_on_support
            intro chosen _supported
            rw [PMF.map_comp]
            have first := (marginals chosen).1
            change (kernel chosen).map Prod.fst = _ at first
            change _ = ((execution runtime leaks current).environmentStep
              (runtime.reactiveApplication leaks) (command runtime leaks chosen)).map
                (fun next => some (⟨remaining, (command runtime leaks chosen).actor?
                  (runtime.reactiveApplication leaks), next⟩ :
                    (runtime.reactiveApplication leaks).Control))
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
            · intro clear
              have same := (marginals chosen).2.2.1 result supported empty (clear _ rfl)
              have actorEq : (command runtime leaks chosen).actor?
                  (runtime.reactiveApplication leaks) =
                  chosen.actor? (runtime.recoveryApplication leaks) := by
                cases chosen <;> rfl
              simp only [package, protocolState]
              rw [same, actorEq]
              rfl
            · exact (marginals chosen).2.2.2 result supported empty valid

end Vegas.EventGraphRuntime.RecoveryProjection
