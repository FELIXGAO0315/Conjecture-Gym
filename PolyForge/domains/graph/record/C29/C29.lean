import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C29 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≥ 2 * (G.cliqueNum : ℤ)) (hn2 : (G.maxDegree : ℤ) ≥ 4) :
    (G.minDegree : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) - 3 * (G.cliqueNum : ℤ) - 1 := by
  have s1 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.maxDegree : ℤ) ≥ 4 := by linarith [hn2]
  have s3 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (G.maxDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
  have s5 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s6 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s7 : (Fintype.card V : ℤ) ≥ 5 := by linarith [s6, s2]
  have s8 : -5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s7]) (by linarith [s5])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s9 : 10 * (G.edgeFinset.card : ℤ) - 5 * (G.minDegree : ℤ) - 15 * (G.cliqueNum : ℤ) ≥ 2 := by linarith [s1, s2, s3, s4, s8]
  have s10 : 2 * (G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) - 3 * (G.cliqueNum : ℤ) ≥ 1 := by have hr := s9; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s10, heq_gallai]
