import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C76 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hp2 : G.IsBipartite) (hn1 : -2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≤ 0) (hn2 : (G.diam : ℤ) ≥ 5) :
    (G.edgeFinset.card : ℤ) ≤ (Fintype.card V : ℤ) + (G.radius.toNat : ℤ) - 4 := by
  have s1 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G (isTree_connected G hp1)
    linarith [hw]
  have s2 : (G.diam : ℤ) ≥ 5 := by linarith [hn2]
  have s3 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp1
    linarith [hw]
  have s4 : 2 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 7 := by linarith [s1, s2, s3]
  have s5 : (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + (G.radius.toNat : ℤ) ≥ 4 := by have hr := s4; omega
  linarith [s5]
