module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.EventGraphSourceResidual
public import Vegas.Pending.ExclusionCompletion

@[expose] public section

/-! # Source prefixes along automatic runtime paths

Automatic completions of defaulted owners follow the ordinary source kernel.
The actual runtime drain retains every source view reached before draining.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {profile : BehavioralProfile setup.program}

/-- An automatic native completion is one deterministic step of the original
source behavioral kernel and retains every previously reached observation. -/
theorem SourceResidual.completeAutomatic_sourceStep [Fintype Player] {rank : Nat}
    {state : EventGraphRuntime.State setup.informationGraph}
    (residual : SourceResidual setup profile rank state.config)
    (event : setup.informationGraph.EventId) (eligible : state.AutomaticReady event) :
    ∃ next : SourceResidual setup profile (rank + 1)
        (state.completeAutomatic event eligible).config,
      ProtocolState.behavioralStateStep setup.program profile
          (residual.lift (ProtocolState.entry residual.program residual.source)) =
        PMF.pure (next.lift (ProtocolState.entry next.program next.source)) ∧
      ∀ focal r, r ≤ ProtocolView.position focal setup.program
          (ProtocolState.observe focal setup.program
            (residual.lift (ProtocolState.entry residual.program residual.source))) →
        ProtocolView.atRank focal setup.program r (ProtocolState.observe focal setup.program
          (next.lift (ProtocolState.entry next.program next.source))) =
        ProtocolView.atRank focal setup.program r (ProtocolState.observe focal setup.program
          (residual.lift (ProtocolState.entry residual.program residual.source))) := by
  obtain ⟨owner, acting, inactive⟩ := eligible.owned
  obtain ⟨action, supported⟩ := state.completeAutomatic_step event eligible
  obtain ⟨next, reached, mass⟩ := residual.step_mass event eligible.1 action
    (state.completeAutomatic event eligible).config supported
  refine ⟨next, ?_, ?_⟩
  · have noActor : ProtocolView.actor owner setup.program
        (ProtocolState.observe owner setup.program
          (residual.lift (ProtocolState.entry residual.program residual.source))) = none := by
      have currentRank : state.config.cut.IsPrefix event.val :=
        ⟨event.isLt.le, fun query =>
          setup.informationGraph.sequentialize_mem_completed_iff_lt_of_ready _ eligible.1⟩
      have rankEq : event.val = rank := currentRank.unique residual.checkpoint.ordered
      have inside : rank < eventCount setup.program := rankEq ▸ event.isLt
      have decoded := residual.decode
      change decodeSourcePrefix? setup.program _ _ _ _ rank state.config.store
        (decodeHistory setup.program state.config.history) state.config.defaults = _ at decoded
      have actor := decodeSourcePrefix?_actor owner rank setup.program _ _ _ _ _ _ _ _
        decoded inside
      rw [actor, eventOwner?_eq_actor]
      have eventEq : (⟨rank, inside⟩ : setup.informationGraph.EventId) = event :=
        Fin.ext rankEq.symm
      change (setup.informationGraph.actor? ⟨rank, inside⟩).filter
        (fun player => decide (player ∉ state.config.defaulted)) = none
      rw [eventEq, acting]
      simp [inactive]
    rw [ProtocolState.behavioralStateStep_of_actor_none _ _ _ owner noActor,
      ← ProtocolState.step_eq_of_actor_none owner setup.program _
        (fun _ => decodeEventAction setup.program event action) noActor]
    apply pmf_eq_pure_of_support_subset_singleton
    apply ((PMF.apply_eq_one_iff _ _).mp ?_).le
    rw [mass]
    obtain ⟨target, graphLaw⟩ := state.config.step_eq_pure_of_actor event eligible.1 action
      owner acting
    have same : (state.completeAutomatic event eligible).config = target :=
      (PMF.mem_support_pure_iff _ _).mp (graphLaw ▸ supported)
    rw [graphLaw, same, PMF.pure_apply_self]
  · intro focal r within
    exact ProtocolView.atRank_step focal setup.program _ _ _ reached r within

/-- A finite native automatic path is an ordinary source prefix of the same
length and retains all views at source ranks reached before that path. -/
theorem SourceResidual.automatic_path_sourcePrefix [Fintype Player] {rank : Nat}
    {before after : EventGraphRuntime.State setup.informationGraph}
    (residual : SourceResidual setup profile rank before.config)
    (path : Relation.ReflTransGen EventGraphRuntime.State.AutomaticStep before after) :
    ∃ count nextRank, ∃ next : SourceResidual setup profile nextRank after.config,
      nextRank = rank + count ∧
      (fun law => law.bind (ProtocolState.behavioralStateStep setup.program profile))^[count]
          (PMF.pure (residual.lift (ProtocolState.entry residual.program residual.source))) =
        PMF.pure (next.lift (ProtocolState.entry next.program next.source)) ∧
      ∀ focal r, r ≤ ProtocolView.position focal setup.program
          (ProtocolState.observe focal setup.program
            (residual.lift (ProtocolState.entry residual.program residual.source))) →
        ProtocolView.atRank focal setup.program r (ProtocolState.observe focal setup.program
          (next.lift (ProtocolState.entry next.program next.source))) =
        ProtocolView.atRank focal setup.program r (ProtocolState.observe focal setup.program
          (residual.lift (ProtocolState.entry residual.program residual.source))) := by
  induction path using Relation.ReflTransGen.head_induction_on generalizing rank with
  | refl => exact ⟨0, rank, residual, by omega, rfl, fun _ _ _ => rfl⟩
  | @head before middle moved rest ih =>
      obtain ⟨event, eligible, rfl⟩ := moved
      obtain ⟨first, firstLaw, firstViews⟩ := residual.completeAutomatic_sourceStep event eligible
      obtain ⟨count, nextRank, next, rankEq, restLaw, restViews⟩ := ih first
      refine ⟨count + 1, nextRank, next, by omega, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, PMF.pure_bind, firstLaw]
        exact restLaw
      · intro focal r within
        have member : first.lift (ProtocolState.entry first.program first.source) ∈
            (ProtocolState.behavioralStateStep setup.program profile
              (residual.lift (ProtocolState.entry residual.program residual.source))).support := by
          rw [firstLaw, PMF.mem_support_pure_iff]
        have firstWithin : r ≤ ProtocolView.position focal setup.program
            (ProtocolState.observe focal setup.program
              (first.lift (ProtocolState.entry first.program first.source))) := by
          classical
          have beforeCount := ProtocolView.position_add_remaining focal setup.program
            (residual.lift (ProtocolState.entry residual.program residual.source))
          have afterCount := ProtocolView.position_add_remaining focal setup.program
            (first.lift (ProtocolState.entry first.program first.source))
          unfold ProtocolState.behavioralStateStep at member
          split at member
          · have same := (PMF.mem_support_pure_iff _ _).mp member
            rw [same]
            exact within
          · rename_i running
            obtain ⟨joint, _supported, reached⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
            have progress := ProtocolState.remaining_step setup.program _ _ joint running reached
            omega
        exact (restViews focal r firstWithin).trans (firstViews focal r within)

/-- Native draining advances to its actual source rank by deterministic source
steps and preserves the source observation at every previously reached rank. -/
theorem SourceResidual.drain_sourcePrefix [Fintype Player] {rank : Nat}
    {state : EventGraphRuntime.State setup.informationGraph}
    (residual : SourceResidual setup profile rank state.config) :
    ∃ count nextRank, ∃ next : SourceResidual setup profile nextRank state.drain.config,
      nextRank = rank + count ∧
      (fun law => law.bind (ProtocolState.behavioralStateStep setup.program profile))^[count]
          (PMF.pure (residual.lift (ProtocolState.entry residual.program residual.source))) =
        PMF.pure (next.lift (ProtocolState.entry next.program next.source)) ∧
      ∀ focal r, r ≤ ProtocolView.position focal setup.program
          (ProtocolState.observe focal setup.program
            (residual.lift (ProtocolState.entry residual.program residual.source))) →
        ProtocolView.atRank focal setup.program r (ProtocolState.observe focal setup.program
          (next.lift (ProtocolState.entry next.program next.source))) =
        ProtocolView.atRank focal setup.program r (ProtocolState.observe focal setup.program
          (residual.lift (ProtocolState.entry residual.program residual.source))) :=
  residual.automatic_path_sourcePrefix state.drain_trace

end Vegas
