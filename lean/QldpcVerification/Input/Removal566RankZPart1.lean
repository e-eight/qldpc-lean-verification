import QldpcVerification.Input.Removal566RankZData
namespace QldpcVerification.Removal566.RankZ
open Input Input.Sparse QubitRemovalSequence
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem column_block_6 : allIdx columnPred ((ps.drop 96).take 16) 96 = true := by
  decide +kernel

theorem column_block_7 : allIdx columnPred ((ps.drop 112).take 16) 112 = true := by
  decide +kernel

theorem column_block_8 : allIdx columnPred ((ps.drop 128).take 16) 128 = true := by
  decide +kernel

theorem column_block_9 : allIdx columnPred ((ps.drop 144).take 16) 144 = true := by
  decide +kernel

theorem column_block_10 : allIdx columnPred ((ps.drop 160).take 16) 160 = true := by
  decide +kernel

theorem column_block_11 : allIdx columnPred ((ps.drop 176).take 16) 176 = true := by
  decide +kernel
theorem pivot_block_6 : allIdx pivotPred ((ts.drop 96).take 16) 96 = true := by
  decide +kernel

theorem pivot_block_7 : allIdx pivotPred ((ts.drop 112).take 16) 112 = true := by
  decide +kernel

theorem pivot_block_8 : allIdx pivotPred ((ts.drop 128).take 16) 128 = true := by
  decide +kernel

theorem pivot_block_9 : allIdx pivotPred ((ts.drop 144).take 16) 144 = true := by
  decide +kernel

theorem pivot_block_10 : allIdx pivotPred ((ts.drop 160).take 16) 160 = true := by
  decide +kernel

theorem pivot_block_11 : allIdx pivotPred ((ts.drop 176).take 16) 176 = true := by
  decide +kernel
end QldpcVerification.Removal566.RankZ
