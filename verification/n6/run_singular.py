from pathlib import Path
import subprocess,os,sys,json,time
ROOT=Path(__file__).resolve().parent
char=sys.argv[1];base=Path.home()/'.local/share/mordell-singular/root'
env=os.environ.copy();env['LD_LIBRARY_PATH']=str(base/'usr/lib/x86_64-linux-gnu');env['SINGULARPATH']=str(base/'usr/share/singular/LIB')
env['SINGULAR_PROCS_DIR']=str(base/'usr/libexec/x86_64-linux-gnu/singular/MOD')
start=time.time();meta={'characteristic':char,'started_unix':start,'status':'running'}
path=ROOT/f'singular_{char}_execution.json'
with (ROOT/f'singular_{char}.log').open('w') as out:
    p=subprocess.Popen([str(base/'usr/bin/Singular'),'--no-rc','--cpus=4','-q',f'quotient_{char}.sing'],cwd=ROOT,env=env,stdout=out,stderr=subprocess.STDOUT)
    meta['pid']=p.pid;path.write_text(json.dumps(meta,indent=2));ret=p.wait()
meta.update(status='finished',exit_code=ret,elapsed_seconds=time.time()-start)
path.write_text(json.dumps(meta,indent=2));print(json.dumps(meta))
