import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C10 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.cliqueNum : ℤ) ≥ 2) (hn2 : (G.edgeFinset.card : ℤ) ≤ 2 * (G.minDegree : ℤ)) :
    (G.minDegree : ℤ) ≥ -(G.maxDegree : ℤ) - 2 * (G.indepNum : ℤ) + 4 := by
  have s1 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    linarith [hw]
  have s2 : (G.cliqueNum : ℤ) ≥ 2 := by linarith [hn1]
  have s3 : (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_card_int G
    linarith [hw]
  have s4 : (Fintype.card V : ℤ) ≥ 2 := by linarith [s2, s3]
  have s5 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
    have hw := tau_le_edges_int G
    linarith [hw]
  have s6 : -(G.edgeFinset.card : ℤ) + 2 * (G.minDegree : ℤ) ≥ 0 := by linarith [hn2]
  have s7 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    linarith [hw]
  have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s9 : 2 * (G.minDegree : ℤ) + 4 * (G.indepNum : ℤ) ≥ 5 := by linarith [s2, s7, s3, s5, s6, s8]
  have s10 : (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 3 := by have hr := s9; omega
  have s11 : 3 * (G.maxDegree : ℤ) + 3 * (G.minDegree : ℤ) + 6 * (G.indepNum : ℤ) ≥ 10 := by linarith [s1, s4, s5, s6, s10, s8]
  have s12 : (G.maxDegree : ℤ) + (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 4 := by have hr := s11; omega
  linarith [s12]
