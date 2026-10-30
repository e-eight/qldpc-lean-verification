import QldpcVerification.Input.Removal566RankZData
namespace QldpcVerification.Removal566.RankZ
open Input Input.Sparse QubitRemovalSequence
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem column_block_12 : allIdx columnPred ((ps.drop 192).take 16) 192 = true := by
  decide +kernel

theorem column_block_13 : allIdx columnPred ((ps.drop 208).take 16) 208 = true := by
  decide +kernel

theorem column_block_14 : allIdx columnPred ((ps.drop 224).take 16) 224 = true := by
  decide +kernel

theorem column_block_15 : allIdx columnPred ((ps.drop 240).take 16) 240 = true := by
  decide +kernel

theorem column_block_16 : allIdx columnPred ((ps.drop 256).take 16) 256 = true := by
  decide +kernel

theorem column_block_17 : allIdx columnPred ((ps.drop 272).take 16) 272 = true := by
  decide +kernel
theorem pivot_block_12 : allIdx pivotPred ((ts.drop 192).take 16) 192 = true := by
  decide +kernel

theorem pivot_block_13 : allIdx pivotPred ((ts.drop 208).take 16) 208 = true := by
  decide +kernel

theorem pivot_block_14 : allIdx pivotPred ((ts.drop 224).take 16) 224 = true := by
  decide +kernel

theorem pivot_block_15 : allIdx pivotPred ((ts.drop 240).take 16) 240 = true := by
  decide +kernel

theorem pivot_block_16 : allIdx pivotPred ((ts.drop 256).take 16) 256 = true := by
  decide +kernel

theorem pivot_block_17 : allIdx pivotPred ((ts.drop 272).take 16) 272 = true := by
  decide +kernel
end QldpcVerification.Removal566.RankZ
