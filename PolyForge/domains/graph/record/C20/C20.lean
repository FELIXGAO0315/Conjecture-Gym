import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C20 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsEdgeConnected 3) (hp2 : ¬ G.IsAcyclic) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≥ 1) (hn2 : (G.minDegree : ℤ) ≥ 2 * (G.girth : ℤ)) :
    (G.cliqueNum : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) - 35 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.girth : ℤ) ≥ 3 := by
    have hw := girth_ge_three_int G hp2
    try push_cast at hw
    linarith [hw]
  have s4 : (G.minDegree : ℤ) - 2 * (G.girth : ℤ) ≥ 0 := by linarith [hn2]
  have s5 : (G.minDegree : ℤ) ≥ 6 := by linarith [s3, s4]
  have s6 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s7 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s8 : (Fintype.card V : ℤ) ≥ 7 := by linarith [s6, s7, s3, s4]
  have s9 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s10 : -6 * (Fintype.card V : ℤ) - 7 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -42 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 7) * ((G.minDegree : ℤ) - 6) :=
      mul_nonneg (by linarith [s8]) (by linarith [s5])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s11 : 2 * (G.edgeFinset.card : ℤ) - (G.cliqueNum : ℤ) ≥ 35 := by linarith [s1, s2, s5, s8, s9, s10]
  linarith [s11]
