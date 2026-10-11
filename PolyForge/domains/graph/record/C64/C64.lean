import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C64 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsAcyclic) (hn1 : (G.edgeFinset.card : ℤ) ≤ 2) (hn2 : (Fintype.card V : ℤ) ≥ 2) :
    (G.maxDegree : ℤ) ≥ -2 * (G.indepNum : ℤ) + 3 := by
  have s1 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
    have hw := tau_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s3 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (Fintype.card V : ℤ) ≥ 2 := by linarith [hn2]
  have s5 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s6 : -(G.edgeFinset.card : ℤ) ≥ -2 := by linarith [hn1]
  have s7 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [s5, s6]
  have s8 : 2 * (Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 4 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 2) * (2 - (G.maxDegree : ℤ)) :=
      mul_nonneg (by linarith [s4]) (by linarith [s7])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s10 : (G.maxDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s1, s2, s3, s8, s9]
  linarith [s10]
