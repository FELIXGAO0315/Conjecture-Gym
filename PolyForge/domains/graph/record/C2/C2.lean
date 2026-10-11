import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C2 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) :
    (G.indepNum : ℤ) ≥ -2 * (G.edgeFinset.card : ℤ) + 2 * (G.minDegree : ℤ) + 3 := by
  have s1 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s4 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s2, s3]
  have s5 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
    have hw := tau_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s6 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s7 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s8 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s4]) (by linarith [s7])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s10 : 6 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 7 := by linarith [s1, s4, s5, s6, s8, s9]
  have s11 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + (G.indepNum : ℤ) ≥ 3 := by have hr := s10; omega
  linarith [s11]
