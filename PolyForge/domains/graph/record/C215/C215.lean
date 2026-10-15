import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C215 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.indepNum : ℤ) ≥ 5) (hn2 : (G.chromaticNumber.toNat : ℤ) ≥ (G.maxDegree : ℤ)) :
    (G.chromaticNumber.toNat : ℤ) ≥ -(G.edgeFinset.card : ℤ) + 3 * (G.minDegree : ℤ) + 1 := by
  have s1 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s4 : -(G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
  have s5 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s6 : (G.indepNum : ℤ) ≥ 5 := by linarith [hn1]
  have s7 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
  have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s9 : (Fintype.card V : ℤ) ≥ 5 := by linarith [s6, s7, s8]
  have s10 : -5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s9]) (by linarith [s5])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s11 : 2 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by linarith [s1, s2, s3, s4, s10]
  have s12 : (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 1 := by have hr := s11; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s12, heq_gallai]
