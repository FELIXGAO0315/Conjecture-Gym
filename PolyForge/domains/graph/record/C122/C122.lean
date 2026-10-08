import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C122 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hp2 : 2 ≤ Fintype.card V) (hn1 : (G.edgeFinset.card : ℤ) ≤ 3) (hn2 : (G.diam : ℤ) ≤ 1) :
    -(G.minDegree : ℤ) + 2 * (G.diam : ℤ) - (G.radius.toNat : ℤ) ≤ 0 := by
  have s1 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G (isTree_connected G hp1)
    linarith [hw]
  have s2 : (G.minDegree : ℤ) ≥ 1 := by
    have hw := connected_min_deg_int G (isTree_connected G hp1) hp2
    linarith [hw]
  have s3 : -(G.diam : ℤ) ≥ -1 := by linarith [hn2]
  have s4 : 2 * (G.minDegree : ℤ) - 4 * (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ -1 := by linarith [s1, s2, s3]
  have s5 : (G.minDegree : ℤ) - 2 * (G.diam : ℤ) + (G.radius.toNat : ℤ) ≥ 0 := by have hr := s4; omega
  linarith [s5]
