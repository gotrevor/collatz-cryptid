// generic lifted residue game. args: p q g(json) w(json) k d iters
const [p,q]=[+process.argv[2],+process.argv[3]];
const g=JSON.parse(process.argv[4]), w=JSON.parse(process.argv[5]);
const k=+process.argv[6], d=+process.argv[7], iters=+process.argv[8];
let M=1; for(let i=0;i<k;i++) M*=q;
// state x mod M (M = q^k); next mod M depends on x mod qM: adversary picks digit a in [0,q)
let V=new Float64Array(M), NV=new Float64Array(M);
const nxt=new Int32Array(M*q*(d+1));
for(let s=0;s<M;s++) for(let a=0;a<q;a++){ const u=s+a*M; const base=p*Math.floor(u/q)+g[u%q];
  for(let c=0;c<=d;c++){ nxt[(s*q+a)*(d+1)+c]=(((base+c)%M)+M)%M; } }
for(let it=0;it<iters;it++){
  for(let s=0;s<M;s++){ let worst=-Infinity;
    for(let a=0;a<q;a++){ let best=Infinity; const o=(s*q+a)*(d+1);
      for(let c=0;c<=d;c++){ const v=V[nxt[o+c]]; if(v<best)best=v; }
      if(best>worst)worst=best; }
    NV[s]=w[s%q]+worst; }
  const t=V; V=NV; NV=t; }
let mx=-Infinity,mn=Infinity; for(let s=0;s<M;s++){ if(V[s]>mx)mx=V[s]; if(V[s]<mn)mn=V[s]; }
console.log(`k=${k} d=${d} value max ${(mx/iters).toFixed(4)} min ${(mn/iters).toFixed(4)}`);
