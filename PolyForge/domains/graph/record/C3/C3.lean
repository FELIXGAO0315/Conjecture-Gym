import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C3 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hp2 : G.IsTree) (hn1 : (G.diam : ℤ) ≥ 3) :
    (G.edgeFinset.card : ℤ) ≤ (Fintype.card V : ℤ) + 2 * (G.radius.toNat : ℤ) - 5 := by
  have s1 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G (isTree_connected G hp2)
    linarith [hw]
  have s2 : (G.diam : ℤ) ≥ 3 := by linarith [hn1]
  have s3 : 2 * (G.radius.toNat : ℤ) ≥ 3 := by linarith [s1, s2]
  have s4 : (G.radius.toNat : ℤ) ≥ 2 := by have hr := s3; omega
  have s5 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp2
    linarith [hw]
  have s6 : (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 5 := by linarith [s4, s5]
  linarith [s6]
