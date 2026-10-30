import QldpcVerification.Input.Removal566Comm0
import QldpcVerification.Input.Removal566Comm1
import QldpcVerification.Input.Removal566Comm2
namespace QldpcVerification.Removal566.Stage12
open Input Input.Sparse QubitRemovalSequence
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem comm_check : commCheck hx hz = true := by
  have hs : hx = ((hx.drop 0).take 16) ++ ((hx.drop 16).take 16) ++ ((hx.drop 32).take 16) ++ ((hx.drop 48).take 16) ++ ((hx.drop 64).take 16) ++ ((hx.drop 80).take 16) ++ ((hx.drop 96).take 16) ++ ((hx.drop 112).take 16) ++ ((hx.drop 128).take 16) ++ ((hx.drop 144).take 16) ++ ((hx.drop 160).take 16) ++ ((hx.drop 176).take 16) ++ ((hx.drop 192).take 16) ++ ((hx.drop 208).take 16) ++ ((hx.drop 224).take 16) ++ ((hx.drop 240).take 16) ++ ((hx.drop 256).take 16) ++ ((hx.drop 272).take 16) ++ [] := by rfl
  rw [hs]
  simp only [commCheck_append]
  rw [comm_block_0, comm_block_1, comm_block_2, comm_block_3, comm_block_4, comm_block_5, comm_block_6, comm_block_7, comm_block_8, comm_block_9, comm_block_10, comm_block_11, comm_block_12, comm_block_13, comm_block_14, comm_block_15, comm_block_16, comm_block_17]
  rfl
def code : CSSCode 566 274 274 := ⟨matrix hx, matrix hz, comm_of_check hx hz comm_check⟩
end QldpcVerification.Removal566.Stage12
