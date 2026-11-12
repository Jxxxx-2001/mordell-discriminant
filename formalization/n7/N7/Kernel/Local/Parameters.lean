import N7.Kernel.Local.ContactData
import N7.Kernel.LocalGeometry
set_option autoImplicit false
namespace N7.Kernel.Local
namespace C0
def center : Fin 3 → ℚ := ![0,1,0]
def radius : ℚ := (1/4096:ℚ)
theorem distance_pos : 0<LocalGeometry.centerDistance center-4*radius := by norm_num [LocalGeometry.centerDistance,center,radius,Matrix.cons_val_two]
end C0
namespace C1
def center : Fin 3 → ℚ := ![1,1,(1/2:ℚ)]
def radius : ℚ := (1/16384:ℚ)
theorem distance_pos : 0<LocalGeometry.centerDistance center-4*radius := by norm_num [LocalGeometry.centerDistance,center,radius,Matrix.cons_val_two]
end C1
namespace C2
def center : Fin 3 → ℚ := ![1,1,(-1/2:ℚ)]
def radius : ℚ := (1/256:ℚ)
theorem distance_pos : 0<LocalGeometry.centerDistance center-4*radius := by norm_num [LocalGeometry.centerDistance,center,radius,Matrix.cons_val_two]
end C2
namespace C3
def center : Fin 3 → ℚ := ![1,1,-1]
def radius : ℚ := (1/4096:ℚ)
theorem distance_pos : 0<LocalGeometry.centerDistance center-4*radius := by norm_num [LocalGeometry.centerDistance,center,radius,Matrix.cons_val_two]
end C3
end N7.Kernel.Local
