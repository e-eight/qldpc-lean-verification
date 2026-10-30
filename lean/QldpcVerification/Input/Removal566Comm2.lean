import QldpcVerification.Input.Removal566Data
namespace QldpcVerification.Removal566.Stage12
open Input Input.Sparse QubitRemovalSequence
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem comm_block_12 : commCheck ((hx.drop 192).take 16) hz = true := by decide +kernel

theorem comm_block_13 : commCheck ((hx.drop 208).take 16) hz = true := by decide +kernel

theorem comm_block_14 : commCheck ((hx.drop 224).take 16) hz = true := by decide +kernel

theorem comm_block_15 : commCheck ((hx.drop 240).take 16) hz = true := by decide +kernel

theorem comm_block_16 : commCheck ((hx.drop 256).take 16) hz = true := by decide +kernel

theorem comm_block_17 : commCheck ((hx.drop 272).take 16) hz = true := by decide +kernel
end QldpcVerification.Removal566.Stage12
