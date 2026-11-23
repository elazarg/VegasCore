module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Interaction.ReactiveConditionedMenu
public import Interaction.ReactiveHistory
public import GameTheory.Analysis.Protocol.CounterfactualReach

@[expose] public section

/-! # History reach on an observed component of a reactive initializer -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open scoped ENNReal

variable {Principal : Type} [DecidableEq Principal] [Finite Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  {Signal : Type*} {initial : PMF app.State} {component : Signal → PMF app.State}
  {horizon : Nat} {scheduler : app.Scheduler} {key : Signal}
  (included : (component key).support ⊆ initial.support)
  (read : Principal → app.Info → Signal)
  (strategies : ∀ k who, (menu.information (component k) horizon scheduler).BehavioralPolicy who)

local notation "M" => menu.information initial horizon scheduler
local notation "C" => menu.information (component key) horizon scheduler
local notation "E" => menu.protocol (component key) horizon scheduler
local notation "embed" => menu.traceOfInitialSupportSubset (horizon := horizon)
  (scheduler := scheduler) included
local notation "glued" => menu.signalStrategy (initial := initial) read strategies

private theorem joint_probability_component
    (knows : ∀ {state} (_ : (E).Trace state) who, (E).active state who →
      read who (app.observe who state) = key)
    {state} (trace : (E).Trace state) (joint : Principal → Option app.Action)
    (legal : (E).Legal state joint) :
    (((M).behavioralJoint glued (embed trace) legal.1) ⟨joint, legal⟩).toReal =
      (((C).behavioralJoint (strategies key) trace legal.1) ⟨joint, legal⟩).toReal := by
  rw [InformationModel.behavioralJoint_prob_eq_prod, InformationModel.behavioralJoint_prob_eq_prod]
  apply Finset.prod_congr rfl
  intro who mover
  have active := (ExecutionProtocol.mem_movers _).mp mover
  have correct := knows trace who active
  have obs : (app.observe who state).isSome := (app.observe_isSome who state).mpr active
  have orig := menu.info initial horizon scheduler who (embed trace)
  have cond := menu.info (component key) horizon scheduler who trace
  obtain ⟨pair, hv⟩ := Option.isSome_iff_exists.mp obs
  rw [hv] at correct orig cond
  let a := (M).choicesOfLegal (embed trace) ⟨joint, legal⟩ who
  let b := (C).choicesOfLegal trace ⟨joint, legal⟩ who
  have left := pmf_map_apply_of_injective (glued who ((M).infoOf who (embed trace)))
    Subtype.val_injective a
  have right := pmf_map_apply_of_injective (strategies key who ((C).infoOf who trace))
    Subtype.val_injective b
  change (glued who _ a).toReal = (strategies key who _ b).toReal
  rw [← left, ← right]
  change (((glued who _).map Subtype.val) (joint who)).toReal =
    (((strategies key who _).map Subtype.val) (joint who)).toReal
  change (M).infoOf who (embed trace) = some pair at orig
  change (C).infoOf who trace = some pair at cond
  rw [orig, cond]
  exact congrArg (fun k => (((strategies k who (some pair)).map Subtype.val)
    (joint who)).toReal) correct

/-- History reach of the locally selected profile differs from component reach by exactly
the initial mass factor, at every initialized history including off-path decisions. -/
theorem signalStrategy_historyReachWeight (scale : ENNReal) (finite : scale ≠ ⊤)
    (atoms : ∀ st ∈ (component key).support, initial st = scale * component key st)
    (knows : ∀ {state} (_ : (E).Trace state) who, (E).active state who →
      read who (app.observe who state) = key)
    {control : app.Control} (trace : (E).Trace (some control)) :
    (M).historyReachWeight glued ⟨_, embed trace⟩ =
      scale * (C).historyReachWeight (strategies key) ⟨_, trace⟩ := by
  have calcReach : ∀ {state} (t : (E).Trace state), state ≠ none →
      ((M).historyReachWeight glued ⟨_, embed t⟩).toReal =
        scale.toReal * ((C).historyReachWeight (strategies key) ⟨_, t⟩).toReal := by
    intro state t
    induction t with
    | start => intro h; exact (h rfl).elim
    | @extend before after prior joint legal realized ih =>
      intro _
      simp only [traceOfInitialSupportSubset, InformationModel.historyReachProbability_extend]
      have same := menu.joint_probability_component included read strategies knows prior joint legal
      cases before with
      | none =>
        obtain rfl := menu.trace_at_root prior
        obtain ⟨st, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp realized
        let enter := fun st : app.State =>
          some (⟨horizon, none, Execution.initial app st⟩ : app.Control)
        have inj : Function.Injective enter := by
          intro a b eq
          exact congrArg (fun c : app.Control => c.execution.application) (Option.some.inj eq)
        have masses := congrArg ENNReal.toReal (atoms st member)
        rw [ENNReal.toReal_mul] at masses
        unfold InformationModel.stepProb
        rw [same]
        have rootMass {init : PMF app.State}
            (p : ∀ i, (menu.information init horizon scheduler).BehavioralPolicy i) :
            ((menu.information init horizon scheduler).historyReachWeight p
              (menu.protocol init horizon scheduler).initHistory).toReal = 1 := by
          change ((PMF.pure (menu.protocol init horizon scheduler).initHistory)
            (menu.protocol init horizon scheduler).initHistory).toReal = 1
          simp
        rw [show ((M).historyReachWeight glued ⟨none, embed .start⟩).toReal = 1
          from rootMass glued, show ((C).historyReachWeight (strategies key)
            ⟨none, .start⟩).toReal = 1 from rootMass (strategies key), one_mul, one_mul]
        change _ * ((initial.map enter) (enter st)).toReal =
          scale.toReal * (_ * (((component key).map enter) (enter st)).toReal)
        rw [pmf_map_apply_of_injective _ inj, pmf_map_apply_of_injective _ inj, masses]
        ring
      | some before =>
        rw [ih (by simp)]
        unfold InformationModel.stepProb
        rw [same]
        exact mul_assoc _ _ _
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _)
    (ENNReal.mul_ne_top finite (PMF.apply_ne_top _ _))).mp
  rw [ENNReal.toReal_mul]
  exact calcReach trace (by simp)

end Interaction.ReactiveApplication.ResponseMenu
