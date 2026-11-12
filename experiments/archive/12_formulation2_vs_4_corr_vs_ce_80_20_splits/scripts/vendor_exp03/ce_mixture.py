"""Matched simplex family: convex log loss and the historical cone Pearson solver."""
import time
from pathlib import Path
import sys

import numpy as np
from scipy.optimize import minimize

sys.path.insert(0, str(Path(__file__).resolve().parent/'historical'))
from mixture_models import _inputs, _base_receipt, _pearson, predict_mixture

MAX_EVALUATIONS = 2000
MAX_ITERATIONS = 1000
CERTIFICATE_TOL = 1e-8


def fit(q, p, loss):
    q, p = _inputs(q, p)
    assert np.min(q) > 0, 'Smooth each candidate once before fitting either loss.'
    start = time.monotonic()
    m = q.shape[1]
    if loss == 'pearson':
        w, rec = _pearson(q, p)
        rec.update(iterations=0, function_evaluations=0,
                   linear_solves=rec['faces_total'] if rec['status'] in
                   ['optimal_cone_projection','certificate_failed'] else 0,
                   initialization='finite faces; no random starts')
    elif loss == 'ce':
        calls = 0
        best_w = np.full(m, 1/m)
        best_value = float('inf')

        def fg(w):
            nonlocal calls, best_w, best_value
            if calls >= MAX_EVALUATIONS:
                raise RuntimeError('evaluation_budget_exhausted')
            calls += 1
            prediction = np.einsum('njr,j->nr', q, w)
            value = -float(np.sum(p*np.log(prediction))/len(p))
            gradient = -np.einsum('nr,njr->j', p/prediction, q)/len(p)
            if value < best_value and min(w) >= 0 and abs(sum(w)-1) < 1e-10:
                best_value, best_w = value, w.copy()
            return value, gradient

        try:
            opt = minimize(fg, best_w.copy(), method='SLSQP', jac=True,
                           bounds=[(0.,1.)]*m,
                           constraints={'type':'eq','fun':lambda w:w.sum()-1,
                                        'jac':lambda w:np.ones(m)},
                           options={'maxiter':MAX_ITERATIONS,'ftol':1e-15})
            w = np.maximum(opt.x, 0)
            w /= w.sum()
            optimizer = {'optimizer_success':bool(opt.success),'optimizer_message':str(opt.message),
                         'iterations':int(opt.nit)}
        except RuntimeError as err:
            if str(err) != 'evaluation_budget_exhausted': raise
            w = best_w
            optimizer = {'optimizer_success':False,'optimizer_message':str(err),'iterations':None}
        # Refine on the selected face: SLSQP can stop on objective rounding
        # before its gradient meets the independently checked gap tolerance.
        # This is a fixed bounded continuation of the same start, not a retry.
        polishing_steps = 0
        linear_solves = 0
        available = min(10, MAX_ITERATIONS-(optimizer['iterations'] or MAX_ITERATIONS))
        for _ in range(available):
            if calls >= MAX_EVALUATIONS-25: break
            value, gradient = fg(w)
            if gradient@w-gradient.min() <= CERTIFICATE_TOL/10: break
            active = np.flatnonzero(w>1e-10)
            if len(active)<2: break
            pred = predict_mixture(q,w)
            hessian = np.einsum('nr,njr,nkr->jk',p/(pred*pred),q[:,active],q[:,active])/len(p)
            basis=np.vstack([np.eye(len(active)-1),-np.ones(len(active)-1)])
            tangent_gradient=basis.T@gradient[active]
            reduced=np.linalg.lstsq(basis.T@hessian@basis,-tangent_gradient,rcond=None)[0]
            direction = np.zeros(m)
            direction[active] = basis@reduced
            linear_solves += 1
            slope = float(tangent_gradient@reduced)
            if slope >= 0 or np.max(abs(direction)) < 1e-15: break
            negative=direction<0
            step=min(1.,float(np.min(-w[negative]/direction[negative])))
            accepted=False
            for _ in range(20):
                trial=np.maximum(w+step*direction,0);trial/=trial.sum()
                trial_value,_=fg(trial)
                if trial_value <= value+1e-4*step*slope+1e-15:
                    w=trial;accepted=True;polishing_steps+=1;break
                step*=.5
            if not accepted: break
        pred = predict_mixture(q,w)
        gradient = -np.einsum('nr,njr->j',p/pred,q)/len(p)
        # Convex differentiable simplex loss: F(w)-F* <= g.w-min_j g_j.
        gap = float(gradient@w-gradient.min())
        rec = _base_receipt('ce',w,q,p)
        rec.update(algorithm='SLSQP_convex_log_loss',success=bool(gap<=CERTIFICATE_TOL),
                   status='optimal' if gap<=CERTIFICATE_TOL else 'certificate_failed',
                   objective_value=-float(np.sum(p*np.log(pred))/len(p)),
                   simplex_frank_wolfe_gap=gap,certificate_tolerance=CERTIFICATE_TOL,
                   function_evaluations=calls,linear_solves=linear_solves,
                   polishing_steps=polishing_steps,
                   initialization='one uniform start',
                   identification='deterministic SLSQP from uniform weights; no secondary test loss',**optimizer)
    else:
        raise ValueError(loss)
    rec.update(elapsed_seconds=time.monotonic()-start,common_evaluation_ceiling=MAX_EVALUATIONS,
               common_iteration_ceiling=MAX_ITERATIONS,hyperparameter_candidates=1,
               new_inference_calls=0)
    return w, rec
