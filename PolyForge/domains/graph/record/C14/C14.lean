import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C14 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsAcyclic) (hn1 : (G.maxDegree : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)) :
    (G.edgeFinset.card : ℤ) ≤ 2 * (Fintype.card V : ℤ) - 2 := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
  have s4 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s5 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s6 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := acyclic_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s7 : -(G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s8 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [s6, s7]
  have s9 : 2 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 2 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (2 - (G.maxDegree : ℤ)) :=
      mul_nonneg (by linarith [s5]) (by linarith [s8])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s11 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) ≥ 2 := by linarith [s1, s2, s3, s4, s9, s10]
  linarith [s11]
