import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C6 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.edgeFinset.card : ℤ) - 2 * (G.diam : ℤ) ≤ 0) (hn2 : (Fintype.card V : ℤ) - 2 * (G.maxDegree : ℤ) ≤ 0) :
    (G.minDegree : ℤ) ≤ (G.maxDegree : ℤ) + 2 * (G.radius.toNat : ℤ) - 2 := by
  have s1 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    linarith [hw]
  have s2 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    linarith [hw]
  have s3 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G (isTree_connected G hp1)
    linarith [hw]
  have s4 : -(G.edgeFinset.card : ℤ) + 2 * (G.diam : ℤ) ≥ 0 := by linarith [hn1]
  have s5 : -(Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) ≥ 0 := by linarith [hn2]
  have s6 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp1
    linarith [hw]
  have s7 : 4 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s2, s3, s4, s5, s6]
  have s8 : (G.radius.toNat : ℤ) ≥ 1 := by have hr := s7; omega
  have s9 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 2 := by linarith [s1, s8]
  linarith [s9]
