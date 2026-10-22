import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T388 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (G.cliqueNum : ℤ) ≥ 2 * (G.indepNum : ℤ)) :
    (G.maxDegree : ℤ) ≥ (G.cliqueNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) + 1 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) ≥ 3 := by
    have hw := three_le_card_of_cycle_int G hp1
    try push_cast at hw
    linarith [hw]
  have s4 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
    have hw := omega_le_maxdeg_add_one_int G
    try push_cast at hw
    linarith [hw]
  have s5 : (G.cliqueNum : ℤ) - 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
  have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s7 : 2 * (G.maxDegree : ℤ) - 2 * (G.cliqueNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by linarith [s1, s2, s3, s4, s5, s6]
  have s8 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by have hr := s7; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s8, heq_gallai]
