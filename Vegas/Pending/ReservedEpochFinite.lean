/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochScheduler
import Vegas.Pending.PhaseFiniteNature

/-! # Finite joint scheduler environments -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

instance {Player : Type} [Fintype Player] (length : Nat) : Fintype (Tape Player length) := by
  classical
  exact Fintype.ofInjective
    (fun tape : Tape Player length => (tape.order, tape.activation, tape.processing)) (by
      intro first second same
      cases first
      cases second
      cases same
      rfl)

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem implementation_support_finite {length : Nat} (packetBudget : Nat)
    (prior : PMF (Tape Player length))
    (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView) :
    ((implementation runtime leaks packetBudget prior).scheduler past view).support.Finite := by
  have imageFinite : (Set.range fun tape : Tape Player length =>
      command runtime leaks packetBudget tape past.length view).Finite := Set.finite_range _
  apply imageFinite.subset
  intro selected supported
  rw [ReactiveApplication.SchedulerImplementation.scheduler_eq] at supported
  change selected ∈ ((((implementation runtime leaks packetBudget prior).posterior past).bind
    fun tape => (family runtime leaks packetBudget tape past view).map
      (fun selected => (selected, tape))).map Prod.fst).support at supported
  rw [PMF.support_map] at supported
  obtain ⟨response, supported, rfl⟩ := supported
  rw [PMF.support_bind] at supported
  obtain ⟨tape, _, chosen⟩ := Set.mem_iUnion₂.mp supported
  change response ∈ ((family runtime leaks packetBudget tape past view).map
    (fun selected => (selected, tape))).support at chosen
  rw [PMF.support_map] at chosen
  obtain ⟨selected, chosen, rfl⟩ := chosen
  exact ⟨tape, ((family_support runtime leaks packetBudget tape past view selected).mp
    chosen).symm⟩

theorem implementation_finiteNature [leaks.FiniteSupport] {length : Nat}
    (packetBudget : Nat) (prior : PMF (Tape Player length))
    (initial : PMF (app).State) (finiteInitial : initial.support.Finite) :
    (app).FiniteNature initial (implementation runtime leaks packetBudget prior).scheduler :=
  phaseApplication_finiteNature runtime leaks initial _ finiteInitial
    (implementation_support_finite runtime leaks packetBudget prior)

end Vegas.EventGraphRuntime.ReservedEpoch
