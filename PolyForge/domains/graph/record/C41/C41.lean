import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C41 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hp2 : G.IsTree) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ 2) (hn2 : (G.indepNum : ℤ) ≤ 6) :
    (G.edgeFinset.card : ℤ) ≤ (G.maxDegree : ℤ) + (G.indepNum : ℤ) - 1 := by
  have s1 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s3 : -(G.vertexCoverNum.toNat : ℤ) ≥ -2 := by linarith [hn1]
  have s4 : -(G.indepNum : ℤ) ≥ -6 := by linarith [hn2]
  have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s6 : -(Fintype.card V : ℤ) ≥ -8 := by linarith [s3, s4, s5]
  have s7 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s8 : (G.minDegree : ℤ) ≥ 1 := by
    have hw := connected_min_deg_int G (isTree_connected G hp2) hp1
    try push_cast at hw
    linarith [hw]
  have s9 : (G.maxDegree : ℤ) ≥ 1 := by linarith [s7, s8]
  have s10 : (Fintype.card V : ℤ) + 8 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 8 := by
    have hmul : (0 : ℤ) ≤ (8 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 1) :=
      mul_nonneg (by linarith [s6]) (by linarith [s9])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s11 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp2
    try push_cast at hw
    linarith [hw]
  have s12 : -8 * (G.edgeFinset.card : ℤ) + 8 * (G.maxDegree : ℤ) + 8 * (G.indepNum : ℤ) ≥ 1 := by linarith [s1, s2, s3, s10, s5, s11]
  have s13 : -(G.edgeFinset.card : ℤ) + (G.maxDegree : ℤ) + (G.indepNum : ℤ) ≥ 1 := by have hr := s12; omega
  linarith [s13]
