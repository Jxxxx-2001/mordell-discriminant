import N7.Kernel.CoverProofs.P0000
namespace N7.Kernel.Cover
theorem root_majorant : BoxMajorant RootTensor.box := bound0
theorem domain_majorant : DomainMajorant matrix := domainMajorant_of_root root_majorant
#print axioms domain_majorant
end N7.Kernel.Cover
