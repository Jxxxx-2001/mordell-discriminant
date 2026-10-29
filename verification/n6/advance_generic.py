from pathlib import Path
ROOT=Path(__file__).resolve().parent
base=(ROOT/'quotient_0.sing').read_text()
base=base.replace('ideal G=std(I);','LIB "modstd.lib";\nideal G=modStd(I,1);')
base=base.replace('quotient_basis_0.txt','quotient_basis_modexact.txt')
base=base.replace('quit;', 'ring lexr=0,(t,e,k,c,B),lp;\nideal H=fglm(r,G);\nshort=0;\nwrite("quotient_lex_modexact.txt",H);\nprint("LEX DONE");\nquit;')
(ROOT/'quotient_modexact.sing').write_text(base)
ff=(ROOT/'quotient_32003.sing').read_text().replace('quit;', 'ring lexr=32003,(t,e,k,c,B),lp;\nideal H=fglm(r,G);\nshort=0;\nwrite("quotient_lex_32003.txt",H);\nprint("LEX DONE");\nquit;')
(ROOT/'quotient_fflex.sing').write_text(ff)
