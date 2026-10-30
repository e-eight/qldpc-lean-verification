import QldpcVerification.Input.Removal566RankZPart0
import QldpcVerification.Input.Removal566RankZPart1
import QldpcVerification.Input.Removal566RankZPart2
namespace QldpcVerification.Removal566.RankZ
open Input Input.Sparse QubitRemovalSequence
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem column_check : columnCheck Stage12.hz ps cols = true := by
  change allIdx columnPred ps 0 = true
  have hl0 : ((ps.drop 0).take 16).length = 16 := by rfl
  have hl1 : ((ps.drop 16).take 16).length = 16 := by rfl
  have hl2 : ((ps.drop 32).take 16).length = 16 := by rfl
  have hl3 : ((ps.drop 48).take 16).length = 16 := by rfl
  have hl4 : ((ps.drop 64).take 16).length = 16 := by rfl
  have hl5 : ((ps.drop 80).take 16).length = 16 := by rfl
  have hl6 : ((ps.drop 96).take 16).length = 16 := by rfl
  have hl7 : ((ps.drop 112).take 16).length = 16 := by rfl
  have hl8 : ((ps.drop 128).take 16).length = 16 := by rfl
  have hl9 : ((ps.drop 144).take 16).length = 16 := by rfl
  have hl10 : ((ps.drop 160).take 16).length = 16 := by rfl
  have hl11 : ((ps.drop 176).take 16).length = 16 := by rfl
  have hl12 : ((ps.drop 192).take 16).length = 16 := by rfl
  have hl13 : ((ps.drop 208).take 16).length = 16 := by rfl
  have hl14 : ((ps.drop 224).take 16).length = 16 := by rfl
  have hl15 : ((ps.drop 240).take 16).length = 16 := by rfl
  have hl16 : ((ps.drop 256).take 16).length = 16 := by rfl
  have hl17 : ((ps.drop 272).take 16).length = 2 := by rfl
  have hs : ps = ((ps.drop 0).take 16) ++ ((ps.drop 16).take 16) ++ ((ps.drop 32).take 16) ++ ((ps.drop 48).take 16) ++ ((ps.drop 64).take 16) ++ ((ps.drop 80).take 16) ++ ((ps.drop 96).take 16) ++ ((ps.drop 112).take 16) ++ ((ps.drop 128).take 16) ++ ((ps.drop 144).take 16) ++ ((ps.drop 160).take 16) ++ ((ps.drop 176).take 16) ++ ((ps.drop 192).take 16) ++ ((ps.drop 208).take 16) ++ ((ps.drop 224).take 16) ++ ((ps.drop 240).take 16) ++ ((ps.drop 256).take 16) ++ ((ps.drop 272).take 16) ++ [] := by rfl
  rw [hs]
  simp only [QubitRemovalSequence.allIdx_append, List.length_append, hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9, hl10, hl11, hl12, hl13, hl14, hl15, hl16, hl17]
  rw [column_block_0, column_block_1, column_block_2, column_block_3, column_block_4, column_block_5, column_block_6, column_block_7, column_block_8, column_block_9, column_block_10, column_block_11, column_block_12, column_block_13, column_block_14, column_block_15, column_block_16, column_block_17]
  rfl
theorem pivot_check : pivotCheck ts cols = true := by
  change allIdx pivotPred ts 0 = true
  have hl0 : ((ts.drop 0).take 16).length = 16 := by rfl
  have hl1 : ((ts.drop 16).take 16).length = 16 := by rfl
  have hl2 : ((ts.drop 32).take 16).length = 16 := by rfl
  have hl3 : ((ts.drop 48).take 16).length = 16 := by rfl
  have hl4 : ((ts.drop 64).take 16).length = 16 := by rfl
  have hl5 : ((ts.drop 80).take 16).length = 16 := by rfl
  have hl6 : ((ts.drop 96).take 16).length = 16 := by rfl
  have hl7 : ((ts.drop 112).take 16).length = 16 := by rfl
  have hl8 : ((ts.drop 128).take 16).length = 16 := by rfl
  have hl9 : ((ts.drop 144).take 16).length = 16 := by rfl
  have hl10 : ((ts.drop 160).take 16).length = 16 := by rfl
  have hl11 : ((ts.drop 176).take 16).length = 16 := by rfl
  have hl12 : ((ts.drop 192).take 16).length = 16 := by rfl
  have hl13 : ((ts.drop 208).take 16).length = 16 := by rfl
  have hl14 : ((ts.drop 224).take 16).length = 16 := by rfl
  have hl15 : ((ts.drop 240).take 16).length = 16 := by rfl
  have hl16 : ((ts.drop 256).take 16).length = 16 := by rfl
  have hl17 : ((ts.drop 272).take 16).length = 2 := by rfl
  have hs : ts = ((ts.drop 0).take 16) ++ ((ts.drop 16).take 16) ++ ((ts.drop 32).take 16) ++ ((ts.drop 48).take 16) ++ ((ts.drop 64).take 16) ++ ((ts.drop 80).take 16) ++ ((ts.drop 96).take 16) ++ ((ts.drop 112).take 16) ++ ((ts.drop 128).take 16) ++ ((ts.drop 144).take 16) ++ ((ts.drop 160).take 16) ++ ((ts.drop 176).take 16) ++ ((ts.drop 192).take 16) ++ ((ts.drop 208).take 16) ++ ((ts.drop 224).take 16) ++ ((ts.drop 240).take 16) ++ ((ts.drop 256).take 16) ++ ((ts.drop 272).take 16) ++ [] := by rfl
  rw [hs]
  simp only [QubitRemovalSequence.allIdx_append, List.length_append, hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9, hl10, hl11, hl12, hl13, hl14, hl15, hl16, hl17]
  rw [pivot_block_0, pivot_block_1, pivot_block_2, pivot_block_3, pivot_block_4, pivot_block_5, pivot_block_6, pivot_block_7, pivot_block_8, pivot_block_9, pivot_block_10, pivot_block_11, pivot_block_12, pivot_block_13, pivot_block_14, pivot_block_15, pivot_block_16, pivot_block_17]
  rfl
theorem rank_lower : 274 ≤ Module.finrank (ZMod 2)
    (Submodule.span (ZMod 2) (Set.range (matrix Stage12.hz))) :=
  rank_of_check Stage12.hz ts ps cols (by rfl) (by rfl) column_check pivot_check
end QldpcVerification.Removal566.RankZ
