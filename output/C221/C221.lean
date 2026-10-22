import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C221 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≤ 5) (hn2 : (G.maxDegree : ℤ) ≤ 3) :
    (G.edgeFinset.card : ℤ) ≤ 7 := by
  have s1 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s2 : -(G.maxDegree : ℤ) ≥ -3 := by linarith [hn2]
  have s3 : (G.maxDegree : ℤ) ≥ 0 := by positivity
  have s4 : -(Fintype.card V : ℤ) ≥ -5 := by linarith [hn1]
  have s5 : 5 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ (5 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s4]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s6 : -2 * (G.edgeFinset.card : ℤ) ≥ -15 := by linarith [s1, s2, s5]
  have s7 : -(G.edgeFinset.card : ℤ) ≥ -7 := by have hr := s6; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s7, heq_gallai]
