"""Public Magma calculator; only the explicit mathematical input below is sent."""
from pathlib import Path
import urllib.request,urllib.parse,xml.etree.ElementTree as ET,json,time
ROOT=Path(__file__).resolve().parent
raw=json.loads((ROOT/'quotient_system.json').read_text())
program='SetColumns(0);\nSetGBGlobalModular(false);\nP<t,e,k,c,B>:=PolynomialRing(Rationals(),5,"grevlex");\n'
program+='D:='+raw['D'].replace('**','^')+';\n'
for j,v in enumerate(raw['equations']):program+=f'E{j}:='+v.replace('**','^')+';\n'
program+='I:=ideal<P|E0,E1,E2,E3,t*B*D-1>;\nprint "GLOBAL_MODULAR",GetGBGlobalModular();\ntime G:=GroebnerBasis(I:GlobalModular:=false);\nprint "DIMENSION",Dimension(I);\nprint "QUOTIENT_DIMENSION",QuotientDimension(I);\nprint "GB_SIZE",#G;\n'
assert len(program.encode())<50000
(ROOT/'magma_input.txt').write_text(program)
request=urllib.request.Request('https://magma.maths.usyd.edu.au/xml/calculator.xml',
 data=urllib.parse.urlencode({'input':program}).encode(),
 headers={'Content-Type':'application/x-www-form-urlencoded','Referer':'https://magma.maths.usyd.edu.au/calc/',
          'Accept':'text/html, application/xml, application/xhtml+xml','User-Agent':'Mozilla/5.0'})
start=time.time()
try:
    response=urllib.request.urlopen(request,timeout=90).read()
    (ROOT/'magma_response.xml').write_bytes(response)
    parsed=ET.fromstring(response)
    answer='\n'.join(''.join(e.itertext())for e in parsed.findall('.//results/line'))
    (ROOT/'magma_response.txt').write_text(answer)
    print(answer)
except Exception as ex:
    print(type(ex).__name__,str(ex))
print('Elapsed',time.time()-start)
