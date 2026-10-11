import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C65 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.minDegree : ℤ) ≤ 3) (hn2 : (G.chromaticNumber.toNat : ℤ) ≤ 2 * (G.vertexCoverNum.toNat : ℤ)) :
    (G.vertexCoverNum.toNat : ℤ) ≤ 3 * (Fintype.card V : ℤ) - 5 := by
  have s1 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : -(G.chromaticNumber.toNat : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn2]
  have s4 : 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by linarith [s2, s3]
  have s5 : (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by have hr := s4; omega
  have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s7 : 3 * (Fintype.card V : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 5 := by linarith [s1, s5, s6]
  linarith [s7]
