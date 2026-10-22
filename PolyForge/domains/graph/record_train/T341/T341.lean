import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T341 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) :
    (G.edgeFinset.card : ℤ) ≥ (G.minDegree : ℤ) - (G.indepNum : ℤ) + 2 := by
  have s1 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s5 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
    have hw := tau_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s7 : (G.edgeFinset.card : ℤ) + (G.indepNum : ℤ) ≥ 3 := by linarith [s3, s4, s5, s6]
  have s8 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s9 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s3, s4]
  have s10 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s9]) (by linarith [s8])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s11 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 5 := by linarith [s1, s2, s7, s10]
  have s12 : (G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) + (G.indepNum : ℤ) ≥ 2 := by have hr := s11; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s12, heq_gallai]
