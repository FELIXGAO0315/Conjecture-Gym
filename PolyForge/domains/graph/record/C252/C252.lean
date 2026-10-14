import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C252 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≥ 6) (hn2 : (G.cliqueNum : ℤ) ≥ 5) :
    2 * (G.minDegree : ℤ) ≤ (G.edgeFinset.card : ℤ) - 2 := by
  have s1 : (G.edgeFinset.card : ℤ) ≥ 6 := by linarith [hn1]
  have s2 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s4 : (G.cliqueNum : ℤ) ≥ 5 := by linarith [hn2]
  have s5 : (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_card_int G
    try push_cast at hw
    linarith [hw]
  have s6 : (Fintype.card V : ℤ) ≥ 5 := by linarith [s4, s5]
  have s7 : -5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s6]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : 5 * (G.edgeFinset.card : ℤ) - 10 * (G.minDegree : ℤ) ≥ 6 := by linarith [s1, s2, s7]
  have s9 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ 2 := by have hr := s8; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s9, heq_gallai]
