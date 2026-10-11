import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C78 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.indepNum : ℤ) ≥ 4) :
    (G.cliqueNum : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 1 := by
  have s1 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
    have hw := omega_le_maxdeg_add_one_int G
    try push_cast at hw
    linarith [hw]
  have s3 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s5 : (G.indepNum : ℤ) ≥ 4 := by linarith [hn1]
  have s6 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
  have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s8 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s5, s6, s7]
  have s9 : -4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s8]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s10 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by linarith [s1, s2, s3, s9]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s10, heq_gallai]
