from pathlib import Path
import sys
import json
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from capitulo_02 import analise_geral as analysis
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'capitulo_02'))
from capitulo_02 import ponte_analise

def logarithm_basic_certificates():
 a=analysis.assumption('|- A e. RR+')
 b=analysis.assumption('|- B e. RR+')
 quotient=analysis.mp(analysis.mm('relogdiv'),analysis.both(a,b))
 product=analysis.mp(analysis.mm('relogmul'),analysis.both(a,b))
 positive_iff=analysis.mp(analysis.mm('loggt0b',{'A':'2'}),analysis.mm('2rp'))
 positive=('iff_mp',positive_iff,analysis.mm('1lt2'),1)
 positive=analysis.rewrite(analysis.eqsym(analysis.mm('1p1e2')),positive)
 zero=analysis.mm('log1')
 mean_value=ponte_analise.logarithm_mean_value()
 results={
 'log_positive_quotient':{'proof':quotient,'formula':'|- ( log ` ( A / B ) ) = ( ( log ` A ) - ( log ` B ) )','hypotheses':frozenset({'|- A e. RR+','|- B e. RR+'})},
 'log_positive_product':{'proof':product,'formula':'|- ( log ` ( A x. B ) ) = ( ( log ` A ) + ( log ` B ) )','hypotheses':frozenset({'|- A e. RR+','|- B e. RR+'})},
 'log_two_positive':{'proof':positive,'formula':'|- 0 < ( log ` ( 1 + 1 ) )','hypotheses':frozenset()},
 'log_one_zero':{'proof':zero,'formula':'|- ( log ` 1 ) = 0','hypotheses':frozenset()},
 'log_mean_value':{'proof':mean_value,'formula':'|- E. x e. ( A (,) B ) ( 1 / x ) = ( ( ( log ` B ) - ( log ` A ) ) / ( B - A ) )','hypotheses':frozenset({'|- A e. RR+','|- B e. RR','|- A < B'})}
 }
 for name,entry in results.items():
  result=analysis.infer(entry['proof'])
  if result!=(entry['formula'],entry['hypotheses']):raise ValueError(('logarithm foundation',name))
 def check(name,condition):
  if not condition:raise ValueError(('foundation interface',name))
 check('log_mean_value',analysis.infer(results['log_mean_value']['proof'])==(results['log_mean_value']['formula'],results['log_mean_value']['hypotheses']))
 return results

if __name__=='__main__':
 results=logarithm_basic_certificates()
 report=[{'id':name,'passed':True,'formula':entry['formula'],'hypotheses':sorted(entry['hypotheses'])} for name,entry in results.items()]
 print(json.dumps({'backend':'Python/independent-Metamath-kernel','checks':len(report),'results':report,'proved':list(results),'passed':True}))
