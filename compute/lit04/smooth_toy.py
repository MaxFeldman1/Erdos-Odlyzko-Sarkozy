import numpy as np, math, sys
def primroot(p):
    fs=[];n=p-1;d=2
    while d*d<=n:
        if n%d==0:
            fs.append(d)
            while n%d==0:n//=d
        d+=1
    if n>1:fs.append(n)
    g=2
    while any(pow(g,(p-1)//f,p)==1 for f in fs):g+=1
    return g
for m in [10007,100003,1000003]:
    B=math.isqrt(m); g=primroot(m)
    ind=np.zeros(m,dtype=np.int64); x=1
    pw=np.empty(m-1,dtype=np.int64)
    for k in range(m-1):
        pw[k]=x; x=x*g%m
    ind[pw]=np.arange(m-1)
    n=np.arange(1,B+1)
    i=ind[n]
    # r on index side: products n1*n2 -> index sum
    r=np.zeros(m-1); 
    for a in i: r+=np.bincount((a+i)%(m-1),minlength=m-1)
    M=(r>0).sum()
    F=np.fft.rfft(r)
    D4=np.fft.irfft(F*F,m-1)           # n1n2n3n4 = a
    Dq=np.fft.irfft(F*np.conj(F),m-1)  # n1n2 = a n3n4
    mean=B**4/(m-1)
    # indicator version
    I=(r>0).astype(float); FI=np.fft.rfft(I)
    MM=np.fft.irfft(FI*FI,m-1)
    # U = h/n
    u=np.zeros(m-1)
    for a in i: u+=np.bincount((a-i)%(m-1),minlength=m-1)
    U=(u>0).sum()
    L=math.log(m)
    print(m,"B",B,"|M|/m %.4f"%(M/m),"(logm)^-0.086=%.4f"%(L**-0.08607),
      "sum r^2/(m log m)=%.3f"%((r*r).sum()/(m*L)),
      "D4 min/mean %.3f max/mean %.3f"%(D4.min()/mean,D4.max()/mean),
      "std/mean %.4f"%(D4.std()/mean),
      "quot min/mean %.3f"%(Dq.min()/mean),
      "MM min/exp %.3f"%(MM.min()/(M*M/(m-1))),
      "|U|/(m-1) %.4f"%(U/(m-1)))

    am=int(np.argmin(Dq)); res=int(pw[am]); 
    print("   quotient argmin residue",res,"(m-res=%d)"%(m-res),"Dq(-1)/mean %.3f"%(Dq[ind[m-1]]/mean),"D4(-1)/mean %.3f D4(1)/mean %.3f"%(D4[ind[m-1]]/mean,D4[0]/mean),"6/pi^2=%.4f"%(6/math.pi**2), "second-smallest quot/mean %.3f"%(np.sort(Dq)[1]/mean), "frac of a with Dq<0.5mean %.4f"%((Dq<0.5*mean).mean()))
