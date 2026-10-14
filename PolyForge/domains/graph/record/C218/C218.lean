import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C218 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≥ 2 * (G.cliqueNum : ℤ)) (hn2 : (G.indepNum : ℤ) ≤ 4) :
    (G.chromaticNumber.toNat : ℤ) ≥ 2 * (G.cliqueNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) - 1 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
  have s4 : (G.maxDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
  have s5 : -(G.indepNum : ℤ) ≥ -4 := by linarith [hn2]
  have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s7 : 2 * (G.chromaticNumber.toNat : ℤ) - 4 * (G.cliqueNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ -3 := by linarith [s1, s2, s3, s4, s5, s6]
  have s8 : (G.chromaticNumber.toNat : ℤ) - 2 * (G.cliqueNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ -1 := by have hr := s7; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s8, heq_gallai]
