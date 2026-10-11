import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C40 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.vertexCoverNum.toNat : ℤ) ≥ 3) :
    (G.maxDegree : ℤ) ≥ -(G.edgeFinset.card : ℤ) + 3 * (G.minDegree : ℤ) := by
  have s1 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s2 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s4 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s5 : (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [hn1]
  have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s7 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s4, s5, s6]
  have s8 : -4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s7]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s9 : (G.edgeFinset.card : ℤ) + (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) ≥ 0 := by linarith [s1, s2, s8]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s9, heq_gallai]
