import sys, math
from math import gcd
def run(m, z, lam):
    spf=list(range(m+1))
    for i in range(2,int(m**.5)+1):
        if spf[i]==i:
            for j in range(i*i,m+1,i):
                if spf[j]==j: spf[j]=i
    isp=[False]*(m+1)
    for n in range(2,m+1): isp[n]=(spf[n]==n)
    units=[n for n in range(1,m) if gcd(n,m)==1]
    phi=len(units)
    P=[p for p in units if isp[p]]
    inP=[False]*m
    for p in P: inP[p]=True
    rho=len(P)/phi
    inv=[0]*m
    for n in units: inv[n]=pow(n,-1,m)
    rt=math.isqrt(m)
    # blocks
    blocks=[]; M=z
    while M<math.sqrt(m):
        hi=M*(1+lam)
        I=[p for p in P if M<=p<hi and p*p<m]   # half-open [M,hi)
        K=[k for k in units if k<=m/M and (k==1 or spf[k]>=M)]
        blocks.append((I,K)); M=hi
    # a-independent fourth moments
    Y=[]
    for I,K in blocks:
        s4=0
        for c in units:
            d=sum(1 for p1 in I if inP[c*inv[p1]%m])-rho*len(I)
            s4+=d**4
        Y.append(s4)
    bad_id=0; bad_ineq=0; ncert=0; nrep=0; worst=1e9
    for a in units:
        A=[a*inv[p]%m for p in P]
        N=sum(1 for n in A if isp[n])
        S=sum(1 for n in A if n==1 or spf[n]>=z)
        B=0
        for n in A:
            if n>1:
                p1=spf[n]
                if z<=p1 and p1*p1<m and not isp[n]: B+=1   # n=p1*k, P^-(k)>=p1 automatically, k>1
                # prime n=p1 (k=1) with p1<sqrt m:
                if isp[n] and z<=n and n*n<m: B+=1
        one=1 if 1 in A else 0
        if N!=S-B-one+sum(1 for n in A if isp[n] and n*n<m): bad_id+=1
        bound=sum(rho*len(I)*len(K)+len(K)**.75*y**.25 for (I,K),y in zip(blocks,Y))
        if B>bound+1e-9: bad_ineq+=1
        cert=S-1-bound
        worst=min(worst,cert)
        if cert>0:
            ncert+=1
            if N==0: print("FALSE CERT",a)
        if N>0:nrep+=1
    print(f"m={m} z={z} lam={lam} phi={phi} blocks={len(blocks)} identity_fail={bad_id} ineq_fail={bad_ineq} certified={ncert}/{phi} represented={nrep} min_cert={worst:.1f} (mu={len(P)*rho:.1f})")
for m,z,lam in [(2003,5,0.5),(2310+1,7,1.0),(3003,5,0.5),(2401,3,0.5),(10007,7,0.25)]:
    run(m,z,lam)
