import QldpcVerification.Input.Removal566Data
namespace QldpcVerification.Removal566.Stage12
open Input Input.Sparse QubitRemovalSequence
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem comm_block_6 : commCheck ((hx.drop 96).take 16) hz = true := by decide +kernel

theorem comm_block_7 : commCheck ((hx.drop 112).take 16) hz = true := by decide +kernel

theorem comm_block_8 : commCheck ((hx.drop 128).take 16) hz = true := by decide +kernel

theorem comm_block_9 : commCheck ((hx.drop 144).take 16) hz = true := by decide +kernel

theorem comm_block_10 : commCheck ((hx.drop 160).take 16) hz = true := by decide +kernel

theorem comm_block_11 : commCheck ((hx.drop 176).take 16) hz = true := by decide +kernel
end QldpcVerification.Removal566.Stage12
