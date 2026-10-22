import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C43 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≥ 3) (hn2 : (Fintype.card V : ℤ) ≥ 5) :
    2 * (G.minDegree : ℤ) ≤ (G.edgeFinset.card : ℤ) - 1 := by
  have s1 : (G.edgeFinset.card : ℤ) ≥ 3 := by linarith [hn1]
  have s2 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s4 : (Fintype.card V : ℤ) ≥ 5 := by linarith [hn2]
  have s5 : -5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s4]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s6 : 5 * (G.edgeFinset.card : ℤ) - 10 * (G.minDegree : ℤ) ≥ 3 := by linarith [s1, s2, s5]
  have s7 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ 1 := by have hr := s6; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s7, heq_gallai]
