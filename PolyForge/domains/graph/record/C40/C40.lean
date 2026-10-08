import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C40 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hp2 : G.IsRegularOfDegree 0) (hn1 : (G.diam : ℤ) ≤ 1) (hn2 : -2 * (G.edgeFinset.card : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 0) :
    -(G.indepNum : ℤ) + 2 * (G.diam : ℤ) - 2 * (G.radius.toNat : ℤ) ≤ -1 := by
  have s1 : (G.edgeFinset.card : ℤ) ≥ 0 := by positivity
  have s2 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp1
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) ≥ 1 := by linarith [s1, s2]
  have s4 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int G (by omega)
    linarith [hw]
  have s5 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G (isTree_connected G hp1)
    linarith [hw]
  have s6 : -(G.diam : ℤ) ≥ -1 := by linarith [hn1]
  have s7 : -2 * (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ -1 := by linarith [s5, s6]
  have s8 : -(G.diam : ℤ) + (G.radius.toNat : ℤ) ≥ 0 := by have hr := s7; omega
  have s9 : (G.indepNum : ℤ) - 2 * (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s4, s8]
  linarith [s9]
