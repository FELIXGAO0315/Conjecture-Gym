import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C6 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≤ 5) :
    (G.cliqueNum : ℤ) ≤ 3 * (G.maxDegree : ℤ) + 2 * (G.indepNum : ℤ) - 1 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s4 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
    have hw := tau_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s5 : (G.maxDegree : ℤ) ≥ 0 := by positivity
  have s6 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s7 : -(Fintype.card V : ℤ) ≥ -5 := by linarith [hn1]
  have s8 : 5 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ (5 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s7]) (by linarith [s5])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s10 : 3 * (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ 1 := by linarith [s1, s2, s3, s4, s5, s6, s8, s9]
  linarith [s10]
