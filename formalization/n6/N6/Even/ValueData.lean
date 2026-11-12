import N6.Univariate.IntegerCore
namespace N6.Even.ValueCover
open N6.IntegerCover
def p : List Int := [-27, 378, -1821, 3324, -1605, 650, 125]
def v : List Int := [-54217579843964399638960334682497485872562176, 518404997007633475346979149913903171140321280, -1349682106430269325291105001999212728578736128, 627227208715985549448906731198284178820956160, -296820281236716747008826173836284255849676800, -54658869202062559901334974258930729877504000]
def vden : Nat := 88817841970012523233890533447265625
def tree : Cover := (.split (.split (.split .leaf (.split (.split (.split (.split (.split (.split .leaf (.split (.split .leaf (.split .leaf (.split .leaf (.split .leaf (.split .leaf .leaf))))) .leaf)) .leaf) .leaf) .leaf) .leaf) .leaf)) .leaf) (.split (.split (.split (.split (.split .leaf (.split .leaf .leaf)) (.split (.split .leaf .leaf) .leaf)) .leaf) .leaf) .leaf))
theorem vden_pos : 0 < vden := by decide +kernel
end N6.Even.ValueCover
