import QldpcVerification.Input.Removal566RankZData
namespace QldpcVerification.Removal566.RankZ
open Input Input.Sparse QubitRemovalSequence
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem column_block_0 : allIdx columnPred ((ps.drop 0).take 16) 0 = true := by
  decide +kernel

theorem column_block_1 : allIdx columnPred ((ps.drop 16).take 16) 16 = true := by
  decide +kernel

theorem column_block_2 : allIdx columnPred ((ps.drop 32).take 16) 32 = true := by
  decide +kernel

theorem column_block_3 : allIdx columnPred ((ps.drop 48).take 16) 48 = true := by
  decide +kernel

theorem column_block_4 : allIdx columnPred ((ps.drop 64).take 16) 64 = true := by
  decide +kernel

theorem column_block_5 : allIdx columnPred ((ps.drop 80).take 16) 80 = true := by
  decide +kernel
theorem pivot_block_0 : allIdx pivotPred ((ts.drop 0).take 16) 0 = true := by
  decide +kernel

theorem pivot_block_1 : allIdx pivotPred ((ts.drop 16).take 16) 16 = true := by
  decide +kernel

theorem pivot_block_2 : allIdx pivotPred ((ts.drop 32).take 16) 32 = true := by
  decide +kernel

theorem pivot_block_3 : allIdx pivotPred ((ts.drop 48).take 16) 48 = true := by
  decide +kernel

theorem pivot_block_4 : allIdx pivotPred ((ts.drop 64).take 16) 64 = true := by
  decide +kernel

theorem pivot_block_5 : allIdx pivotPred ((ts.drop 80).take 16) 80 = true := by
  decide +kernel
end QldpcVerification.Removal566.RankZ
