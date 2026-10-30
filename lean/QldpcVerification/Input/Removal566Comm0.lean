import QldpcVerification.Input.Removal566Data
namespace QldpcVerification.Removal566.Stage12
open Input Input.Sparse QubitRemovalSequence
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem comm_block_0 : commCheck ((hx.drop 0).take 16) hz = true := by decide +kernel

theorem comm_block_1 : commCheck ((hx.drop 16).take 16) hz = true := by decide +kernel

theorem comm_block_2 : commCheck ((hx.drop 32).take 16) hz = true := by decide +kernel

theorem comm_block_3 : commCheck ((hx.drop 48).take 16) hz = true := by decide +kernel

theorem comm_block_4 : commCheck ((hx.drop 64).take 16) hz = true := by decide +kernel

theorem comm_block_5 : commCheck ((hx.drop 80).take 16) hz = true := by decide +kernel
end QldpcVerification.Removal566.Stage12
