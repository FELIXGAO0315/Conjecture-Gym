import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C49 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hn1 : (Fintype.card V : ℤ) ≥ 6) (hn2 : (G.maxDegree : ℤ) ≤ 6) :
    2 * (G.minDegree : ℤ) ≤ (G.edgeFinset.card : ℤ) := by
  have s1 : (G.edgeFinset.card : ℤ) ≥ 0 := by positivity
  have s2 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s4 : (Fintype.card V : ℤ) ≥ 6 := by linarith [hn1]
  have s5 : -6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s4]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s6 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ 0 := by linarith [s1, s2, s5]
  linarith [s6]
