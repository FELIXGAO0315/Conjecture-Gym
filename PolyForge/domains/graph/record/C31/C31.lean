import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C31 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hp2 : G.IsTree) (hn1 : (G.edgeFinset.card : ℤ) ≥ 5) (hn2 : (G.edgeFinset.card : ℤ) - (G.diam : ℤ) ≤ 0) :
    (Fintype.card V : ℤ) ≥ -2 * (G.radius.toNat : ℤ) + 12 := by
  have s1 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G (isTree_connected G hp2)
    linarith [hw]
  have s2 : (G.edgeFinset.card : ℤ) ≥ 5 := by linarith [hn1]
  have s3 : -(G.edgeFinset.card : ℤ) + (G.diam : ℤ) ≥ 0 := by linarith [hn2]
  have s4 : 2 * (G.radius.toNat : ℤ) ≥ 5 := by linarith [s1, s2, s3]
  have s5 : (G.radius.toNat : ℤ) ≥ 3 := by have hr := s4; omega
  have s6 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp2
    linarith [hw]
  have s7 : (Fintype.card V : ℤ) ≥ 6 := by linarith [s2, s6]
  have s8 : (Fintype.card V : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 12 := by linarith [s5, s7]
  linarith [s8]
