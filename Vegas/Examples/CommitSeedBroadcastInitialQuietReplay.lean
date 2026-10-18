/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastFirstLateOccupation
import Vegas.Examples.CommitSeedBroadcastInitialQuietMass
import Interaction.ReactiveRecallReplay
import GameTheoryExtensions.Analysis.Protocol.ContinuationOwnPlay

/-! # Original quiet-prefix likelihood through actual native recall replay -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- Replay only each owner's original initial WAIT; every later own input
keeps the original behavioral response law. -/
def initialQuietProfile (profile : ∀ owner, rawModel.BehavioralPolicy owner) :
    ∀ owner, rawModel.BehavioralPolicy owner := fun owner =>
  rawMenu.recallReplayPolicy initial horizon scheduler owner [initialWaitEntry owner]
    (profile owner)

theorem initialQuietProfile_after_first (profile : ∀ owner, rawModel.BehavioralPolicy owner)
    (owner : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (nonempty : past ≠ []) :
    initialQuietProfile profile owner (some (past, view)) = profile owner (some (past, view)) := by
  cases past with
  | nil => exact (nonempty rfl).elim
  | cons first rest =>
      simp only [initialQuietProfile, ReactiveApplication.ResponseMenu.recallReplayPolicy,
        List.length_cons, List.getElem?_cons_succ, List.getElem?_nil, Option.isSome_none,
        Bool.false_eq_true, dite_false]

theorem initialQuietProfile_first (profile : ∀ owner, rawModel.BehavioralPolicy owner)
    (owner : Player) (view : app.PlayerView) :
    (initialQuietProfile profile owner (some ([], view))).map Subtype.val =
      PMF.pure (some (⟨none⟩ : app.Action)) := by
  have permitted : (⟨none⟩ : app.Action) ∈ rawMenu.actions owner [] view :=
    (PhaseCount.onePacketMenu_in_raw runtime leaks bounds) owner [] view
      (PhaseCount.silence_onePacket runtime leaks bounds owner [] view)
  simp only [initialQuietProfile, ReactiveApplication.ResponseMenu.recallReplayPolicy,
    List.length_nil, List.getElem?_cons_zero, Option.isSome_some, dite_true, Option.get_some,
    initialWaitEntry, permitted, PMF.pure_map]

private theorem decodeProfile_map_some (profile : ∀ owner, rawModel.BehavioralPolicy owner)
    (owner : Player) (past : List app.PlayerEntry) (view : app.PlayerView) :
    (rawMenu.decodeProfile initial horizon scheduler profile owner past view).map some =
      (profile owner (some (past, view))).map Subtype.val := by
  have law := congrFun (app.encode_decodePolicy
    (rawMenu.embedPolicy initial horizon scheduler owner (profile owner))) (some (past, view))
  have projected := congrArg
    (fun distribution : PMF ((app.information initial horizon scheduler).Choice owner
        (some (past, view))) => distribution.map Subtype.val) law
  simpa only [ReactiveApplication.encodePolicy, ReactiveApplication.ResponseMenu.decodeProfile,
    ReactiveApplication.ResponseMenu.embedPolicy, PMF.map_comp, Function.comp_def,
    ReactiveApplication.ResponseMenu.rawChoice] using projected

theorem initialQuietProfile_initial (profile : ∀ owner, rawModel.BehavioralPolicy owner)
    (owner : Player) :
    rawMenu.decodeProfile initial horizon scheduler (initialQuietProfile profile) owner
      ((initialCallback owner).recall owner) ((initialCallback owner).observe app owner) =
        PMF.pure ⟨none⟩ := by
  have recalled : (initialCallback owner).recall owner = [] := by fin_cases owner <;> rfl
  rw [recalled]
  have mapped := (decodeProfile_map_some (initialQuietProfile profile) owner []
    ((initialCallback owner).observe app owner)).trans (initialQuietProfile_first profile owner _)
  apply pmf_map_injective (Option.some_injective _)
  simpa only [PMF.pure_map] using mapped

private theorem initial_response_atom (profile : ∀ owner, rawModel.BehavioralPolicy owner)
    (owner : Player) :
    (((profile owner (some ([], (initialWaitEntry owner).beforeView))).map Subtype.val)
      (some (initialWaitEntry owner).action)).toReal =
      (rawMenu.decodeProfile initial horizon scheduler profile owner []
        ((initialCallback owner).observe app owner) ⟨none⟩).toReal := by
  have equal := congrArg (fun distribution : PMF (Option app.Action) =>
    distribution (some (⟨none⟩ : app.Action)))
    (decodeProfile_map_some profile owner [] ((initialCallback owner).observe app owner))
  have atom := pmf_map_apply_of_injective
    (rawMenu.decodeProfile initial horizon scheduler profile owner []
      ((initialCallback owner).observe app owner)) (Option.some_injective _) ⟨none⟩
  have normalized :
      (rawMenu.decodeProfile initial horizon scheduler profile owner []
        ((initialCallback owner).observe app owner) ⟨none⟩) =
      ((profile owner (some ([], (initialWaitEntry owner).beforeView))).map Subtype.val)
        (some (initialWaitEntry owner).action) := atom.symm.trans equal
  exact congrArg ENNReal.toReal normalized.symm

/-- Only the original first action contributes to the density. Every later
record, including all raw aliases, uses the same original response atom. -/
theorem initialQuietProfile_ownReach (profile : ∀ owner, rawModel.BehavioralPolicy owner)
    (owner : Player) (later : List app.PlayerEntry) :
    rawModel.ownPlayReachProbability (profile owner)
        (app.recallOwnPlay (initialWaitEntry owner :: later)) =
      (rawMenu.decodeProfile initial horizon scheduler profile owner []
        ((initialCallback owner).observe app owner) ⟨none⟩).toReal *
          rawModel.ownPlayReachProbability (initialQuietProfile profile owner)
            (app.recallOwnPlay (initialWaitEntry owner :: later)) := by
  induction later using List.reverseRecOn with
  | nil =>
      have replayAtom : rawModel.ownPlayReachProbability (initialQuietProfile profile owner)
          (app.recallOwnPlay [initialWaitEntry owner]) = 1 := by
        simp only [ReactiveApplication.recallOwnPlay, ReactiveApplication.ownPlayFrom,
          List.nil_append, InformationModel.ownPlayReachProbability, mul_one]
        change (((initialQuietProfile profile owner
          (some ([], (initialWaitEntry owner).beforeView))).map Subtype.val)
            (some (⟨none⟩ : app.Action))).toReal = 1
        rw [initialQuietProfile_first, PMF.pure_apply_self, ENNReal.toReal_one]
      rw [replayAtom, mul_one]
      simp only [ReactiveApplication.recallOwnPlay, ReactiveApplication.ownPlayFrom,
        List.nil_append, InformationModel.ownPlayReachProbability, mul_one]
      change (((profile owner (some ([], (initialWaitEntry owner).beforeView))).map Subtype.val)
        (some (initialWaitEntry owner).action)).toReal = _
      exact initial_response_atom profile owner
  | append_singleton later entry ih =>
      have nonempty : initialWaitEntry owner :: later ≠ [] := List.cons_ne_nil _ _
      change rawModel.ownPlayReachProbability (profile owner)
          (app.recallOwnPlay ((initialWaitEntry owner :: later) ++ [entry])) = _
      rw [app.recallOwnPlay_append, InformationModel.ownPlayReachProbability]
      change _ = _ * rawModel.ownPlayReachProbability (initialQuietProfile profile owner)
        (app.recallOwnPlay ((initialWaitEntry owner :: later) ++ [entry]))
      rw [app.recallOwnPlay_append, InformationModel.ownPlayReachProbability,
        initialQuietProfile_after_first profile owner _ _ nonempty, ih]
      ring

/-- The full genuine history keeps the original transition coefficient. Its
three initial response factors are the exact initialized quiet density. -/
theorem initialQuietProfile_historyReach (profile : ∀ owner, rawModel.BehavioralPolicy owner)
    (control : app.Control) (trace : rawProtocol.Trace (some control))
    (recorded : ∀ owner, ∃ later,
      control.execution.recall owner = initialWaitEntry owner :: later) :
    (rawModel.historyReachWeight profile ⟨some control, trace⟩).toReal =
      initialQuietReach (rawMenu.decodeProfile initial horizon scheduler profile) *
        (rawModel.historyReachWeight (initialQuietProfile profile)
          ⟨some control, trace⟩).toReal := by
  obtain ⟨records, recordEq, _provenance, chance, _nonnegative, _nature, factor⟩ :=
    rawModel.exists_continuation_ownPlay_factor (.start : rawProtocol.Trace rawProtocol.init)
      trace (TracePrefix.start trace)
  have recordsEq (owner) : records owner = rawModel.ownPlay owner trace := by
    simpa only [InfoSignals.ownPlay, List.append_nil] using (recordEq owner).symm
  have universal (selected : ∀ owner, rawModel.BehavioralPolicy owner) :
      (rawModel.historyReachWeight selected ⟨some control, trace⟩).toReal =
        chance * ∏ owner, rawModel.ownPlayReachProbability (selected owner)
          (app.recallOwnPlay (control.execution.recall owner)) := by
    have own (owner) : rawModel.ownPlay owner trace =
        app.recallOwnPlay (control.execution.recall owner) := by
      change (rawMenu.signals initial horizon scheduler).ownPlay owner trace = _
      rw [← rawMenu.ownPlay_toRawTrace initial horizon scheduler owner trace,
        app.trace_ownPlay]
      rfl
    simpa only [InformationModel.historyReachWeight, InformationModel.runBehavioral, Trace.length,
      Nat.sub_zero, recordsEq, ExecutionProtocol.initHistory, own] using factor selected
  rw [universal, universal]
  have product :
      (∏ owner, rawModel.ownPlayReachProbability (profile owner)
        (app.recallOwnPlay (control.execution.recall owner))) =
      (∏ owner, (rawMenu.decodeProfile initial horizon scheduler profile owner []
        ((initialCallback owner).observe app owner) ⟨none⟩).toReal) *
          ∏ owner, rawModel.ownPlayReachProbability (initialQuietProfile profile owner)
            (app.recallOwnPlay (control.execution.recall owner)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro owner _member
    obtain ⟨later, same⟩ := recorded owner
    rw [same]
    exact initialQuietProfile_ownReach profile owner later
  rw [product]
  have density : (∏ owner, (rawMenu.decodeProfile initial horizon scheduler profile owner []
      ((initialCallback owner).observe app owner) ⟨none⟩).toReal) =
      initialQuietReach (rawMenu.decodeProfile initial horizon scheduler profile) := by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp only [Fin.prod_univ_zero, mul_one]
    unfold initialQuietReach
    change _ = (rawMenu.decodeProfile initial horizon scheduler profile alice []
      ((initialCallback alice).observe app alice) ⟨none⟩).toReal *
      (rawMenu.decodeProfile initial horizon scheduler profile bob []
        ((initialCallback bob).observe app bob) ⟨none⟩).toReal *
      (rawMenu.decodeProfile initial horizon scheduler profile carol []
        ((initialCallback carol).observe app carol) ⟨none⟩).toReal
    rw [show Fin.succ (0 : Fin 2) = (bob : Player) by decide,
      show Fin.succ (Fin.succ (0 : Fin 1)) = (carol : Player) by decide]
    simp only [alice, mul_assoc]
  rw [density]
  ring

end Vegas.Examples.CommitSeedBroadcast
