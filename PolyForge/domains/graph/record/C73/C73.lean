import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C73 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≥ (G.cliqueNum : ℤ)) (hn2 : (Fintype.card V : ℤ) ≤ 2 * (G.maxDegree : ℤ)) :
    (G.cliqueNum : ℤ) ≤ (G.maxDegree : ℤ) := by
  have s1 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := acyclic_chi_int G (isTree_acyclic G hp1)
    try push_cast at hw
    linarith [hw]
  have s4 : -(G.cliqueNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s5 : -(Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) ≥ 0 := by linarith [hn2]
  have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s7 : 2 * (G.maxDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -1 := by linarith [s1, s2, s3, s4, s5, s6]
  have s8 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by have hr := s7; omega
  linarith [s8]
