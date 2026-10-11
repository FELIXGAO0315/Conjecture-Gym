import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C3 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (G.cliqueNum : ℤ) ≥ 2 * (G.indepNum : ℤ)) :
    2 * (G.minDegree : ℤ) ≤ (G.edgeFinset.card : ℤ) + (G.vertexCoverNum.toNat : ℤ) - 1 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s5 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s6 : (G.cliqueNum : ℤ) - 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
  have s7 : (Fintype.card V : ℤ) ≥ 3 := by
    have hw := three_le_card_of_cycle_int G hp1
    try push_cast at hw
    linarith [hw]
  have s8 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s9 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s7]) (by linarith [s8])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s11 : 2 * (G.edgeFinset.card : ℤ) - 4 * (G.minDegree : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by linarith [s1, s2, s3, s4, s5, s6, s9, s10]
  have s12 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by have hr := s11; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s12, heq_gallai]
