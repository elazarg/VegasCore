/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.ProgramPayments
import Vegas.Game.SourceServiceSpec

/-! # A checked native service for the conditional payment program

The roster builder activates Alice once at each of the two source
instructions, includes her latest response, advances the clock and expires the
instruction. The full bounded raw response menu still admits silence, failed
binding, withholding and malformed packets. The service certificate comes from
the proved roster constructor rather than additional scheduling assumptions.
-/

noncomputable section

namespace Vegas.Examples.ProgramPaymentsRuntime

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open ProgramPayments

def leaks (bonus : Int) :
    MessageNetwork.ObservationRule Player (WitnessedPacket (graph (setup bonus))) :=
  fun _ _ => PMF.pure ∅

instance (bonus : Int) : (leaks bonus).FiniteSupport where
  support_finite _ _ := by
    rw [leaks, PMF.support_pure]
    exact Set.finite_singleton ∅

def rawValues : Finset (Raw simpleExpr) := by
  classical
  exact Finset.univ.image fun bit : Bool => (⟨.bool, bit⟩ : Raw simpleExpr)

def bounds (bonus : Int) : MessageBounds (graph (setup bonus)) where
  candidateCount := 2
  values := rawValues

theorem binding_values_covered (bonus : Int) : (bounds bonus).CoversBindingValues := by
  classical
  intro event
  change Fin 2 at event
  fin_cases event
  · change ∀ bit : Bool, (⟨.bool, bit⟩ : Raw simpleExpr) ∈ rawValues
    intro bit
    exact Finset.mem_image.mpr ⟨bit, Finset.mem_univ bit, rfl⟩
  · trivial

theorem initial_values_covered (bonus : Int) :
    ∀ state ∈ (initialLaw (setup bonus)).support, (bounds bonus).CandidateValues state := by
  intro state supported
  change state ∈ ((setup bonus).initialLaw.map
    (fun initial => EventGraphRuntime.State.initial (graph := graph (setup bonus))
      ((setup bonus).eventInputs initial))).support
    at supported
  obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
  intro candidate raw opened
  rcases candidate with ⟨owner, slot⟩
  rw [EventGraphRuntime.State.initial_candidate] at opened
  cases slot with
  | initial input => exact Fin.elim0 input
  | prepared serial => cases opened

def rosters (bonus : Int) : (graph (setup bonus)).EventId → List Player :=
  fun _ => [.alice]

theorem opportunities (bonus : Int) : ActorOpportunities (setup bonus) (rosters bonus) := by
  intro event owner _
  cases owner
  exact List.mem_singleton_self Player.alice

/-- Every field of this actual roster service is proved, including coverage of
the binding alphabet and the absence of initial opening candidates. -/
def rosterService (bonus : Int) : SourceServiceSpec Player simpleExpr where
  setup := setup bonus
  leaks := leaks bonus
  bounds := bounds bonus
  rosters := rosters bonus
  network := (runtime (setup bonus)).idleNetwork (leaks bonus)
  values := binding_values_covered bonus
  initialValues := initial_values_covered bonus
  capacity := by change 2 ≤ 2; decide
  opportunities := opportunities bonus
  initialFinite := inferInstance
  leaksFinite := inferInstance

/-- The checked roster is an instance of the existing asynchronous contract. -/
def service (bonus : Int) : AsyncServiceSpec Player simpleExpr :=
  (rosterService bonus).toAsync

theorem service_horizon (bonus : Int) : (service bonus).horizon = 9 := rfl

end Vegas.Examples.ProgramPaymentsRuntime
