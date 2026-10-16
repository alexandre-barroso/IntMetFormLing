import json
import sympy as sp

results=[]
def check(identifier,condition):
    results.append({'id':identifier,'passed':bool(condition)})
m,n=sp.symbols('m n',integer=True,positive=True)
i,j=sp.symbols('i j',integer=True)
total=sp.symbols('total',positive=True)
rows=sp.IndexedBase('rows',nonnegative=True)
columns=sp.IndexedBase('columns',nonnegative=True)
row_total=sp.Sum(rows[i],(i,1,m))
column_total=sp.Sum(columns[j],(j,1,n))
expected_entry=rows[i]*columns[j]/total
check('expected_nonnegative',expected_entry.is_nonnegative is True)
expected_row=sp.Sum(expected_entry,(j,1,n))
expected_column=sp.Sum(expected_entry,(i,1,m))
factored_row=expected_row.factor()
factored_column=expected_column.factor()
check('expected_row_general',sp.simplify(expected_row-rows[i]*column_total/total)==0 and factored_row.subs(column_total,total)==rows[i])
check('expected_column_general',sp.simplify(expected_column-columns[j]*row_total/total)==0 and factored_column.subs(row_total,total)==columns[j])
factored_total=sp.Sum(factored_row,(i,1,m)).factor()
check('expected_total_general',sp.simplify(factored_total-row_total*column_total/total)==0 and factored_total.subs({row_total:total,column_total:total})==total)
report={'backend':'Python/SymPy','checks':len(results),'passed':all(r['passed'] for r in results),'results':results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
