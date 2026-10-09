import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C26 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : -2 * (G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≤ 0) (hn2 : (G.indepNum : ℤ) ≤ 6) :
    (G.vertexCoverNum.toNat : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) + 2 * (G.maxDegree : ℤ) - 3 := by
  have s1 : (G.edgeFinset.card : ℤ) ≥ 0 := by positivity
  have s2 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp1
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) ≥ 1 := by linarith [s1, s2]
  have s4 : (G.cliqueNum : ℤ) ≥ 1 := by
    have hw := omega_ge_one_int G (by omega)
    linarith [hw]
  have s5 : 2 * (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
  have s6 : 2 * (G.maxDegree : ℤ) ≥ 1 := by linarith [s4, s5]
  have s7 : (G.maxDegree : ℤ) ≥ 1 := by have hr := s6; omega
  have s8 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int G (by omega)
    linarith [hw]
  have s9 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int G (by omega)
    linarith [hw]
  have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s11 : 4 * (G.edgeFinset.card : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by linarith [s4, s8, s5, s9, s10, s2]
  have s12 : 2 * (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by have hr := s11; omega
  have s13 : 2 * (G.edgeFinset.card : ℤ) + 2 * (G.maxDegree : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [s7, s12]
  linarith [s13]
