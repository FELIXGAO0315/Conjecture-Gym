import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C157 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsAcyclic) (hn1 : (G.indepNum : ℤ) ≥ 4) :
    (G.cliqueNum : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 1 := by
  have s1 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
    have hw := omega_le_maxdeg_add_one_int G
    try push_cast at hw
    linarith [hw]
  have s3 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    try push_cast at hw
    linarith [hw]
  have s5 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := acyclic_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s6 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s4, s5]
  have s7 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s8 : (G.indepNum : ℤ) ≥ 4 := by linarith [hn1]
  have s9 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
  have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s11 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s8, s9, s10]
  have s12 : -4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s11]) (by linarith [s7])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s13 : 4 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -3 := by linarith [s1, s2, s3, s6, s12]
  have s14 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by have hr := s13; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s14, heq_gallai]
