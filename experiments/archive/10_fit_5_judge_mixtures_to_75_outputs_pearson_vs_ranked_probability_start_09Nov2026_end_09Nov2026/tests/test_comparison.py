"""Synthetic arithmetic, optimization and data-separation controls."""
import importlib.util
import json
from pathlib import Path
import sys
import unittest

import numpy as np
from scipy.optimize import minimize

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from models import histogram, smooth, rps, fit_rps, train_select, predict
from metrics import summarize
from vendor.mixture_models import fit_mixture, predict_mixture

CFG=json.loads((ROOT/'protocol.json').read_text())


class Controls(unittest.TestCase):
    def test_empirical_oracle_and_individual_score_identity(self):
        p=np.array([histogram([0,5]),histogram([2,2,2])])
        q=smooth(p,1e-12)
        out=summarize(p,q)
        individual=[]
        for i,ratings in enumerate([[0,5],[2,2,2]]):
            individual.append(np.mean([np.mean((np.cumsum(q[i])[:5]-(r<=np.arange(5)))**2) for r in ratings]))
        self.assertAlmostEqual(out['rps'],np.mean(individual),places=14)
        self.assertAlmostEqual(out['rps'],.125,places=10)
        self.assertLess(out['tvd'],5e-12)
        self.assertAlmostEqual(out['ce'],np.log(2)/2,places=10)
        self.assertAlmostEqual(out['brier'],.25,places=10)
        self.assertAlmostEqual(out['rps'],out['empirical_cdf_squared_distance']+out['empirical_disagreement'],places=14)

    def test_extremes_and_artifact_weighting(self):
        p=np.array([histogram([0]),histogram([5,5,5])])
        q=smooth(np.array([[1,0,0,0,0,0]]*2),1e-12)
        out=summarize(p,q)
        self.assertAlmostEqual(out['rps'],.5,places=10)
        self.assertAlmostEqual(out['tvd'],.5,places=10)
        self.assertAlmostEqual(out['brier'],1,places=10)
        self.assertIsNone(out['pearson'])
        self.assertAlmostEqual(out['bias'],-.5,places=10)
        with self.assertRaises(ValueError): histogram([1.5])
        with self.assertRaises(ValueError): histogram([])

    def test_rps_recovers_representable_distribution(self):
        rng=np.random.default_rng(17)
        q=rng.dirichlet(np.ones(6),size=(20,5))
        truth=np.array([.2,0,.3,.5,0])
        p=np.einsum('njr,j->nr',q,truth)
        w,rec=fit_rps(q,p,CFG)
        self.assertTrue(rec['success'])
        np.testing.assert_allclose(p,predict_mixture(q,w),atol=1e-9)
        self.assertEqual(rec['linear_solves'],31)

    def test_rps_matches_independent_constrained_optimizer(self):
        rng=np.random.default_rng(2026)
        for _ in range(12):
            q=rng.dirichlet(np.full(6,.4),size=(15,5))
            p=rng.dirichlet(np.ones(6),size=15)
            w,rec=fit_rps(q,p,CFG)
            sol=minimize(lambda z:rps(p,np.einsum('njr,j->nr',q,z)),np.ones(5)/5,
                         method='SLSQP',bounds=[(0,1)]*5,
                         constraints={'type':'eq','fun':lambda z:z.sum()-1},
                         options={'ftol':1e-13,'maxiter':1000})
            self.assertTrue(sol.success and rec['success'])
            self.assertAlmostEqual(sol.fun,rps(p,predict_mixture(q,w)),places=9)

    def test_duplicate_constant_and_negative_pearson_cases(self):
        p=np.eye(6)[[0,1,2,3,4,5]]
        constant=np.tile(np.ones(6)/6,(6,1))
        q=np.stack([smooth(p,1e-6),smooth(p,1e-6),constant,constant,constant],axis=1)
        for method in ['rps','pearson']:
            w,rec=fit_rps(q,p,CFG) if method=='rps' else fit_mixture(q,p,'pearson')
            self.assertTrue(rec['success'])
            self.assertGreater(w[0],.999)
        neg=np.stack([smooth(p[::-1],1e-6)]*5,axis=1)
        _,rec=fit_mixture(neg,p,'pearson')
        self.assertTrue(rec['success'])
        self.assertAlmostEqual(rec['training_pearson'],-1)

    def test_selection_never_accepts_test_and_controls_common_budget(self):
        rng=np.random.default_rng(19)
        q=rng.dirichlet(np.ones(6),size=(24,5))
        p=np.array([histogram([r]) for r in rng.integers(0,6,size=24)])
        models,fits,selection=train_select(q[:18],p[:18],q[18:],p[18:],CFG)
        self.assertIsNotNone(models)
        self.assertEqual(len(fits),12)
        self.assertEqual(sum(r['objective']=='shared_constant' for r in fits),2)
        self.assertTrue(all(r['linear_solves']<=31 for r in fits))
        for model in models.values():
            self.assertTrue(np.all(predict(q,model)>0))
            np.testing.assert_allclose(predict(q,model).sum(1),1,atol=1e-13)
        # A different held-out evaluation cannot change the saved model parameters.
        before=json.dumps(models,sort_keys=True)
        summarize(p[:6],predict(q[:6],models['method4_rps']))
        summarize(p[:6,::-1],predict(q[:6],models['method4_rps']))
        self.assertEqual(before,json.dumps(models,sort_keys=True))
        # Pearson is invariant under common shrinkage for every nonconstant candidate.
        rec=[r for r in fits if r['method']=='method2_pearson' and r['objective']=='pearson']
        self.assertLess(np.ptp([r['training_pearson'] for r in rec]),1e-10)


if __name__=='__main__': unittest.main()
