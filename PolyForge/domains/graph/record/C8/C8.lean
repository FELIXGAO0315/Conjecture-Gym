import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C8 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.cliqueNum : ℤ) ≤ 2 * (G.vertexCoverNum.toNat : ℤ)) :
    (G.indepNum : ℤ) ≤ 2 * (Fintype.card V : ℤ) - 3 := by
  have s1 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    linarith [hw]
  have s2 : (G.cliqueNum : ℤ) ≥ 1 := by
    have hw := omega_ge_one_int' G
    linarith [hw]
  have s3 : -(G.cliqueNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by linarith [s2, s3]
  have s5 : (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by have hr := s4; omega
  have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s7 : 2 * (Fintype.card V : ℤ) - (G.indepNum : ℤ) ≥ 3 := by linarith [s1, s5, s6]
  linarith [s7]
