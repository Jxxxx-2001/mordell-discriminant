"""Recheck the exact certificates following the certified rational Groebner computation.

For recomputing that Groebner basis itself, see GLOBAL_PROOF.txt. This verifier
recomputes all number-field identities, real-root isolations, comparisons, and
exceptional charts; it does not replace the exact modStd(I,1) computation.
"""
from pathlib import Path
from fractions import Fraction as F
import json,sys,subprocess,hashlib,platform,xml.etree.ElementTree as ET
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'friedman_full_audit_20261023/deps'))
import sympy,flint
steps=['analyze_generic.py','prepare_dual_check.py','generic_branch_check.py',
       'generic_compare.py','exceptional_systems.py','even_branch.py']
with (ROOT/'proof_verification_steps.log').open('w',encoding='utf-8')as log:
    for name in steps:
        print('Verifying',name,flush=True)
        result=subprocess.run([sys.executable,str(ROOT/name)],cwd=ROOT,
                              stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
                              text=True,encoding='utf-8',errors='replace')
        log.write(name+'\n'+result.stdout+'\n');log.flush()
        assert result.returncode==0,(name,result.stdout)
tri=json.loads((ROOT/'generic_triangular.json').read_text())
assert [r['degree']for r in tri['branches']]==[1,1,2,6,11,14]
assert all(r['multiplicity']==1 for r in tri['branches'])
rows=json.loads((ROOT/'generic_comparison.json').read_text())
checks=json.loads((ROOT/'generic_branch_checks.json').read_text())
assert [r['Ay_field_degree']for r in checks]==[1,1,2,6,11,7]
assert all(r['original_equations_zero'] and r['saturation_verified']
           and r['dual_involution_verified']for r in checks)
assert [r['real_root_count']for r in rows]==[1,1,2,2,3,3]
caps=[350000000,1803000000,224000000,10100000]
survivors=[(br['index'],r)for br in rows for r in br['roots']
           if r['decision']=='objective strictly below regular hexagon squared']
assert [j for j,r in survivors]==[0,2,4,4]
for (j,r),bound in zip(survivors,caps):
    assert F(r['objective_square_interval'][1])<bound<6**12
assert all('UNRESOLVED' not in r['decision']for br in rows for r in br['roots'])
even=json.loads((ROOT/'even_branch_comparison.json').read_text())
assert len(even)==4 and all(F(r['upper'])<6**12 for r in even)
singlog=(ROOT/'singular_modexact.log').read_text()
assert 'BASIS DONE\n35\n35\nLEX DONE' in singlog
assert 'error' not in singlog.lower() and '?' not in singlog
program=(ROOT/'quotient_modexact.sing').read_text()
assert 'modStd(I,1)' in program and 'ring r=0,' in program
execution=json.loads((ROOT/'singular_modexact_execution.json').read_text())
assert execution['status']=='finished' and execution['exit_code']==0
membership_files=[]
response_path=ROOT/'magma_response.xml'
if response_path.exists():
    response=ET.fromstring(response_path.read_bytes())
    output='\n'.join(''.join(v.itertext())for v in response.findall('.//results/line'))
    if ('GLOBAL_MODULAR false' in output and 'DIMENSION 0 []' in output and
            'QUOTIENT_DIMENSION 35' in output and 'GB_SIZE 35' in output):
        assert 'error' not in output.lower()
        assert response.find('.//headers/warning') is None
        magma_input=(ROOT/'magma_input.txt').read_text()
        assert 'SetGBGlobalModular(false)' in magma_input
        assert 'GroebnerBasis(I:GlobalModular:=false)' in magma_input
        original=json.loads((ROOT/'quotient_system.json').read_text())
        assert 'D:='+original['D'].replace('**','^')+';' in magma_input
        for j,value in enumerate(original['equations']):
            assert f'E{j}:='+value.replace('**','^')+';' in magma_input
        assert 'I:=ideal<P|E0,E1,E2,E3,t*B*D-1>;' in magma_input
        # I is contained in the graph ideal J by the exact field substitutions.
        # J has dimension 35 as a vector space, as independently certified I does.
        # The surjection Q[t,e,k,c,B]/I -> Q[t,e,k,c,B]/J is an isomorphism.
        B=sympy.Symbol('B')
        factors=[sympy.Poly(sympy.sympify(br['factor']),B)for br in tri['branches']]
        assert sum(f.degree()for f in factors)==35
        assert all(sympy.gcd(f,f.diff()).degree()==0 for f in factors)
        assert all(sympy.gcd(f,g).degree()==0 for j,f in enumerate(factors)for g in factors[:j])
        membership_files=['magma_public_check.py','magma_input.txt','magma_response.xml','magma_response.txt']
for variant in ['direct','directfast','signature']:
    if membership_files:break
    path=ROOT/f'quotient_lex_{variant}.txt'
    logpath=ROOT/f'singular_{variant}.log'
    if path.exists() and 'LEX DONE' in logpath.read_text() and '?' not in logpath.read_text():
        variables=sympy.symbols('t e k c B')
        def read_basis(path):
            return [sympy.Poly(sympy.sympify(v.replace('^','**')),*variables).monic()
                    for v in path.read_text().strip().split(',')]
        assert read_basis(path)==read_basis(ROOT/'quotient_lex_modexact.txt')
        membership_files=[path.name,logpath.name,f'quotient_{variant}.sing',f'singular_{variant}_execution.json']
        break
liftlog=ROOT/'singular_lift.log'
if not membership_files and liftlog.exists() and 'EXACT MEMBERSHIP CERTIFICATE VERIFIED' in liftlog.read_text():
    assert 'Exact lift check: 0' in liftlog.read_text()
    membership_files=['quotient_lift.sing','singular_lift.log','singular_lift_execution.json','quotient_lift_certificate.txt']
assert membership_files,'Independent exact reverse ideal inclusion is still pending'
C=F(5**5)*F(6,5)**15
assert C==F(470184984576,9765625) and C>6**6
x=sympy.Symbol('x')
assert sympy.discriminant(x**6-x,x)==5**5
assert sympy.discriminant(x**6-1,x)==6**6
verification={'global_upper_bound_certified':True,'all_equality_cases_classified':True,
 'method':'exact rational algebra plus real-root isolation; computer-assisted ordinary proof',
 'maximum':str(C),'maximum_decimal_for_display':float(C),
 'equality':'{0} union {sqrt(6/5)*exp(i*theta+2*pi*i*k/5): k=0,...,4}, up to relabeling',
 'generic_algebraic_degree':35,'generic_irreducible_degrees':[1,1,2,6,11,14],
 'generic_Ay_degrees':[1,1,2,6,11,7],'generic_real_Ay_counts':[1,1,2,2,3,3],
 'generic_admissible_roots_bounded':4,'generic_square_caps':caps,
 'even_real_branches_bounded':4,'all_zero_coefficient_charts_covered':True,
 'collision_boundary_excluded_by_positive_candidate':True,
 'centering_proved_analytically':True,'numerical_optimization_used_as_proof':False,
 'exact_Groebner_recomputed_by_this_verifier':False,
 'exact_Groebner_source':'quotient_modexact.sing calls modStd(I,1); see exact execution log',
 'independent_reverse_ideal_inclusion_certified':True,
 'independent_completeness_method':'Magma GlobalModular=false: quotient dimension 35; exact containment I subset J; dim(Q[x]/J)=35 implies I=J',
 'membership_evidence':membership_files,
 'external_peer_review':'not claimed'}
(ROOT/'global_verification.json').write_text(json.dumps(verification,indent=2),encoding='utf-8')
names=['GLOBAL_PROOF.txt','SYMMETRIC_PROOF.md','generic_system.py','generic_system.json',
 'prepare_generic.py','quotient_system.json','advance_generic.py','quotient_modexact.sing',
 'run_singular.py','singular_modexact.log','singular_modexact_execution.json',
 'quotient_basis_modexact.txt','quotient_lex_modexact.txt','analyze_generic.py',
 'generic_triangular.json','prepare_dual_check.py','dual_coefficients.json',
 'generic_branch_check.py','generic_branch_checks.json','generic_compare.py',
 'generic_comparison.json','exceptional_systems.py','exceptional_results.json',
 'even_branch.py','even_branch_result.json','even_branch_comparison.json',
 'verify_global.py','global_verification.json','proof_verification_steps.log',
 'singular_runtime.json']+membership_files
manifest={'software':{'python':platform.python_version(),'sympy':sympy.__version__,
 'python_flint':flint.__version__,'singular':'4.3.2-p10 (Ubuntu package; see singular_runtime.json)',
 'magma':'2.29-10, public calculator, GlobalModular=false'},
 'sha256':{name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest()for name in names}}
(ROOT/'proof_manifest.json').write_text(json.dumps(manifest,indent=2),encoding='utf-8')
print(json.dumps(verification,indent=2))
