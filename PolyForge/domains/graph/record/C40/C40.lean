import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C40 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hn1 : -(G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≤ 0) (hn2 : (Fintype.card V : ℤ) ≥ 3) :
    (G.edgeFinset.card : ℤ) ≥ -2 * (G.indepNum : ℤ) + 6 := by
  have s1 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
    have hw := connected_edges_int G hp1
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) ≥ 3 := by linarith [hn2]
  have s3 : (G.edgeFinset.card : ℤ) ≥ 2 := by linarith [s1, s2]
  have s4 : (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s6 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s2, s4, s5]
  have s7 : (G.indepNum : ℤ) ≥ 2 := by have hr := s6; omega
  have s8 : (G.edgeFinset.card : ℤ) + 2 * (G.indepNum : ℤ) ≥ 6 := by linarith [s3, s7]
  linarith [s8]
