import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C47 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.cliqueNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≤ 0) :
    (G.maxDegree : ℤ) ≤ 2 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) - 5 := by
  have s1 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    linarith [hw]
  have s2 : (G.edgeFinset.card : ℤ) ≥ 0 := by positivity
  have s3 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp1
    linarith [hw]
  have s4 : (Fintype.card V : ℤ) ≥ 1 := by linarith [s2, s3]
  have s5 : (G.cliqueNum : ℤ) ≥ 1 := by
    have hw := omega_ge_one_int G (by omega)
    linarith [hw]
  have s6 : -(G.cliqueNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s7 : (Fintype.card V : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by
    have hw := tau_le_card_sub_one_int G (by omega)
    linarith [hw]
  have s8 : 2 * (Fintype.card V : ℤ) ≥ 3 := by linarith [s5, s6, s7]
  have s9 : (Fintype.card V : ℤ) ≥ 2 := by have hr := s8; omega
  have s10 : 2 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 5 := by linarith [s1, s9, s3]
  linarith [s10]
