"""Batched, residual-certified NLHF solves for exhaustive partition audits.

Continuation is a numerical aid only. Every returned lottery is checked at the
requested temperature; unresolved members use the independent SciPy solver.
"""
import numpy as np
from scipy.special import logsumexp
from scripts.theory.nlhf_tie_normalization import _solve_centered_nlhf


def solve_batch(tau, margins, log_rho, tolerance=1e-9):
    margins=np.asarray(margins,dtype=float);b,n,_=margins.shape
    log_rho=np.broadcast_to(np.asarray(log_rho,dtype=float),(b,n)).copy()
    log_rho-=logsumexp(log_rho,axis=1,keepdims=True)
    q=margins[:,:-1,:]-margins[:,-1:,:]
    eye=np.broadcast_to(np.eye(n-1),(b,n-1,n-1))
    def state(y,coefficient,indices):
        z=np.concatenate([y,np.zeros((len(y),1))],axis=1)
        lp=log_rho[indices]+z;lp-=logsumexp(lp,axis=1,keepdims=True)
        pi=np.exp(lp)
        residual=y-coefficient*np.einsum('bij,bj->bi',q[indices],pi)
        return pi,residual,lp
    y=np.zeros((b,n-1));target=1/(2*tau);coef=min(1.,target)
    while True:
        active=np.arange(b)
        for iteration in range(60):
            if not len(active):break
            pi,res,_=state(y[active],coef,active);err=np.max(np.abs(res),axis=1)
            unfinished=err>tolerance
            active=active[unfinished];pi=pi[unfinished];res=res[unfinished];err=err[unfinished]
            if not len(active):break
            covariance=pi[:,:,None]*np.eye(n)[None,:,:]-pi[:,:,None]*pi[:,None,:]
            jac=eye[active]-coef*np.einsum('bij,bjk->bik',q[active],covariance[:,:,:-1])
            step=np.linalg.solve(jac,-res[:,:,None])[:,:,0]
            alpha=np.ones(len(active));base=y[active].copy();accepted=np.zeros(len(active),dtype=bool)
            for _ in range(18):
                candidates=base+alpha[:,None]*step
                _,new_res,_=state(candidates,coef,active);newerr=np.max(np.abs(new_res),axis=1)
                good=(newerr<=err*(1-1e-4*alpha))|(newerr<=tolerance)
                update=good&~accepted;y[active[update]]=candidates[update];accepted|=good
                if np.all(accepted):break
                alpha[~accepted]*=.5
            if not np.any(accepted):break
        if coef>=target:break
        nxt=min(target,coef*2)
        y*=nxt/coef;coef=nxt
    pi,res,lp=state(y,target,np.arange(b));errors=np.max(np.abs(res),axis=1)
    failures=[];fallbacks=np.flatnonzero(~np.isfinite(errors)|(errors>tolerance))
    for i in fallbacks:
        answer=_solve_centered_nlhf(2*tau,margins[i],np.exp(log_rho[i]),log_rho=log_rho[i],return_log=True)
        if answer is None:failures.append(int(i));lp[i]=np.nan
        else:lp[i]=answer
    return lp,failures,len(fallbacks)
