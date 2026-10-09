import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C58 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hp2 : G.IsBipartite) (hn1 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≤ 0) (hn2 : (G.indepNum : ℤ) - 2 * (G.diam : ℤ) ≤ 0) :
    (G.indepNum : ℤ) ≥ -2 * (G.diam : ℤ) + 3 := by
  have s1 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := radius_le_diam_int G (isTree_connected G hp1)
    linarith [hw]
  have s2 : (G.edgeFinset.card : ℤ) ≥ 0 := by positivity
  have s3 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp1
    linarith [hw]
  have s4 : (Fintype.card V : ℤ) ≥ 1 := by linarith [s2, s3]
  have s5 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int G (by omega)
    linarith [hw]
  have s6 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G (isTree_connected G hp1)
    linarith [hw]
  have s7 : -(G.indepNum : ℤ) + 2 * (G.diam : ℤ) ≥ 0 := by linarith [hn2]
  have s8 : (Fintype.card V : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by
    have hw := tau_le_card_sub_one_int G (by omega)
    linarith [hw]
  have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s10 : 4 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s6, s7, s8, s9]
  have s11 : (G.radius.toNat : ℤ) ≥ 1 := by have hr := s10; omega
  have s12 : (G.indepNum : ℤ) + 2 * (G.diam : ℤ) ≥ 3 := by linarith [s1, s5, s11]
  linarith [s12]
