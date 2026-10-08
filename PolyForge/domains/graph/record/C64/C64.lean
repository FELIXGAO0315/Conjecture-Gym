import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C64 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hn1 : (G.chromaticNumber.toNat : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0) (hn2 : (Fintype.card V : ℤ) ≥ 4) :
    2 * (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ 11 := by
  have s1 : (Fintype.card V : ℤ) ≥ 4 := by linarith [hn2]
  have s2 : (G.cliqueNum : ℤ) ≥ 1 := by
    have hw := omega_ge_one_int G (by omega)
    linarith [hw]
  have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int G (by omega)
    linarith [hw]
  have s4 : (G.chromaticNumber.toNat : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s6 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 9 := by linarith [s1, s3, s4, s5]
  have s7 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ 5 := by have hr := s6; omega
  have s8 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ 11 := by linarith [s2, s7]
  linarith [s8]
