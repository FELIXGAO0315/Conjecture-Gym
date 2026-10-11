import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C98 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.indepNum : ℤ) ≤ 2) (hn2 : (G.edgeFinset.card : ℤ) ≤ 2) :
    2 * (G.maxDegree : ℤ) ≥ 3 * (Fintype.card V : ℤ) - 3 * (G.chromaticNumber.toNat : ℤ) - 4 := by
  have s1 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
    have hw := tau_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s2 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s3 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s4 : -(G.indepNum : ℤ) ≥ -2 := by linarith [hn1]
  have s5 : -(G.edgeFinset.card : ℤ) ≥ -2 := by linarith [hn2]
  have s6 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s7 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
    have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
      mul_nonneg (by linarith [s4]) (by linarith [s6])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : (G.maxDegree : ℤ) ≥ 0 := by positivity
  have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s10 : -(Fintype.card V : ℤ) ≥ -4 := by linarith [s1, s4, s5, s9]
  have s11 : 4 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ (4 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s10]) (by linarith [s8])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s12 : -3 * (Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ -4 := by linarith [s1, s2, s3, s4, s5, s7, s11, s9]
  linarith [s12]
