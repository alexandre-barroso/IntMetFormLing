import json
from fractions import Fraction


def main():
    results=[]
    def check(name,condition):
        if not bool(condition):
            raise AssertionError(name)
        results.append(name)
    rows=[[(int(p[0]),int(p[1])) for p in s.split()] for s in
          ('11 10 11 01 10 01 10 11 00 10','10 11 10 01 01 10 01 11 00 11','10 11 00 01 01 11 01 10 11 11')]
    check('F08_all_sixty_binary_entries',sum(len(pair) for row in rows for pair in row)==60 and all(value in (0,1) for row in rows for pair in row for value in pair))
    check('F08_all_sample_lengths',all(len(row)==10 for row in rows))
    check('F08_pair_frequencies',tuple(tuple(row.count(pair) for pair in ((0,0),(0,1),(1,0),(1,1))) for row in rows)==((1,2,4,3),(1,3,3,3),(1,3,2,4)))
    check('F08_three_differences',tuple(sum(Fraction(a-b,10) for a,b in row) for row in rows)==(Fraction(1,5),Fraction(0),Fraction(-1,10)))
    check('F08_paired_bootstrap_admissible',all(p in rows[0] for row in rows for p in row))
    check('F08_source_pair_not_identified',rows[0][1]==rows[0][4] and 1!=4)
    print(json.dumps({'passed':True,'checks':len(results),'results':results,'scope':'Sixty internally specified binary entries, pair frequencies, paired differences, equal sample lengths, admissible resampled pairs and nonidentifiability of repeated source pairs.'}))


if __name__=='__main__':
    main()
