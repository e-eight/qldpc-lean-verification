import QldpcCert.Bits
import QldpcCert.Surface225Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 100
open Bits Surface225
example : commCheck nq 8 (hx.take 64) hz = true := by decide +kernel
