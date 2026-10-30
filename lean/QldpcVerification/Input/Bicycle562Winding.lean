import QldpcVerification.Input.Bicycle562Geometry
import QldpcVerification.Lattice.Winding

/-! Period-aware winding lifts of the submitted 562-qubit incidence graphs. -/

namespace QldpcVerification.Bicycle562Geometry

open Lattice

def xLift : WindingData xSource xTarget horizontal :=
  cyclicWindingData xSource xTarget horizontal 7 145 x_step

def zLift : WindingData zSource zTarget horizontal :=
  cyclicWindingData zSource zTarget horizontal 145 7 z_step

end QldpcVerification.Bicycle562Geometry
