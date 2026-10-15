import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C298 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.cliqueNum : ℤ) ≤ 2) (hn2 : (G.maxDegree : ℤ) ≤ (G.cliqueNum : ℤ)) :
    2 * (G.cliqueNum : ℤ) ≥ -3 * (Fintype.card V : ℤ) + 3 * (G.edgeFinset.card : ℤ) + 4 := by
  have s1 : (G.cliqueNum : ℤ) ≥ 1 := by
    have hw := omega_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s3 : -(G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn2]
  have s4 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s5 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [hn1]
  have s6 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [s5, s3]
  have s7 : 2 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 2 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (2 - (G.maxDegree : ℤ)) :=
      mul_nonneg (by linarith [s4]) (by linarith [s6])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : 6 * (Fintype.card V : ℤ) - 6 * (G.edgeFinset.card : ℤ) + 4 * (G.cliqueNum : ℤ) ≥ 7 := by linarith [s1, s2, s3, s7]
  have s9 : 3 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) + 2 * (G.cliqueNum : ℤ) ≥ 4 := by have hr := s8; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s9, heq_gallai]
