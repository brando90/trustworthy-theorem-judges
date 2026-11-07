"""TLDR: Independent scoring, pairing, tie, split and probability controls."""
import unittest
import numpy as np
from metrics import histogram, smooth, per_item, summarize, choose, correlations

class Controls(unittest.TestCase):
    def test_individual_rating_formulas(self):
        p = histogram([0,2,5]); q = smooth(histogram([1,2,2]),1e-6)
        m = per_item(p[None,:],q[None,:])
        direct_brier = np.mean([sum((q-np.eye(6)[r])**2) for r in [0,2,5]])
        direct_rps = np.mean([np.mean((np.cumsum(q)[:5]-(r<=np.arange(5)))**2) for r in [0,2,5]])
        self.assertAlmostEqual(m['brier'][0],direct_brier)
        self.assertAlmostEqual(m['rps'][0],direct_rps)
        self.assertAlmostEqual(m['ce'][0],-np.log(q[[0,2,5]]).mean())
        self.assertAlmostEqual(m['ce'][0]-m['kl'][0],m['entropy'][0])

    def test_oracle_permutation_and_constant(self):
        p=np.eye(6); q=smooth(p,1e-6); m=per_item(p,q)
        self.assertLess(m['brier'].max(),1e-9)
        self.assertAlmostEqual(summarize(m,np.arange(6))['spearman'],1)
        self.assertAlmostEqual(summarize(per_item(p,q[::-1]),np.arange(6))['spearman'],-1)
        self.assertTrue(np.isnan(correlations(np.ones(6),np.arange(6))['pearson']))
        self.assertTrue(np.isnan(correlations(np.ones(6),np.arange(6))['spearman']))

    def test_ties(self):
        self.assertAlmostEqual(correlations([1,1,3],[1,1,3])['kendall'],1)
        self.assertEqual(choose([{'ce':1},{'ce':1}], 'ce',['a','b']), (0,False))
        self.assertEqual(choose([{'spearman':float('nan')},{'spearman':.1}], 'spearman',['a','b']), (1,False))

    def test_sparse_and_missing(self):
        with self.assertRaises(AssertionError):histogram([])
        with self.assertRaises(AssertionError):histogram([2.1])
        with self.assertRaises(AssertionError):histogram([float('nan')])
        for e in [1e-8,1e-6,1e-4]:
            q=smooth(histogram([0,0,0]),e)
            self.assertAlmostEqual(q.sum(),1)
            self.assertAlmostEqual(-np.log(q[5]),-np.log(e))

    def test_proper_loss_minima(self):
        p=np.array([[.6,.3,.1,0,0,0]])
        q=smooth(p,1e-10); alternative=smooth(np.array([[2/3,1/3,0,0,0,0]]),1e-10)
        for k in ['ce','brier','rps','weighted_pmf','tvd']:
            self.assertLess(per_item(p,q)[k][0],per_item(p,alternative)[k][0])
        self.assertLess((p*(1-alternative)**2).sum(), (p*(1-q)**2).sum())

    def test_family_split_and_duplicate_assignment(self):
        from run_cached import partitions
        rows=[{'family':str(i//6)} for i in range(60)]
        for outer,inner in partitions(rows,[1,2]):
            for fold in range(5):
                tr={r['family'] for i,r in enumerate(rows) if outer[i]!=fold}
                te={r['family'] for i,r in enumerate(rows) if outer[i]==fold}
                self.assertFalse(tr&te)
                self.assertEqual(tr,set(inner[fold]))
            idx=np.array([0,1,0,1,7,7])
            self.assertEqual(outer[idx][0],outer[idx][2])

    def test_mathematical_expected_rating_ties(self):
        p=np.array([histogram([1,2,3]),histogram([2,2,2])])
        m=per_item(p,smooth(p,1e-6))
        self.assertEqual(m['judge_mean'][0],m['judge_mean'][1])

if __name__=='__main__':unittest.main()
