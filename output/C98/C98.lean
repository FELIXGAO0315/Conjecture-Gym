import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C98 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsAcyclic) (hn1 : (Fintype.card V : ℤ) ≥ 5) :
    (G.indepNum : ℤ) ≥ -(G.edgeFinset.card : ℤ) + 2 * (G.minDegree : ℤ) + 4 := by
  have s1 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := acyclic_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) ≥ 5 := by linarith [hn1]
  have s3 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s5 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
    have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
      mul_nonneg (by linarith [s4]) (by linarith [s1])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s6 : 2 * (G.indepNum : ℤ) ≥ 5 := by linarith [s1, s2, s3, s5]
  have s7 : (G.indepNum : ℤ) ≥ 3 := by have hr := s6; omega
  have s8 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s9 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s10 : -5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s2]) (by linarith [s9])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s11 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
    have hw := tau_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s12 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s13 : (G.edgeFinset.card : ℤ) + (G.indepNum : ℤ) ≥ 5 := by linarith [s2, s11, s12]
  have s14 : 5 * (G.edgeFinset.card : ℤ) - 10 * (G.minDegree : ℤ) + 5 * (G.indepNum : ℤ) ≥ 17 := by linarith [s7, s8, s10, s13]
  have s15 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + (G.indepNum : ℤ) ≥ 4 := by have hr := s14; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s15, heq_gallai]
