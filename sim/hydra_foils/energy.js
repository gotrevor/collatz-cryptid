// energy game: states s mod M; adversary digit a in [0,A); next(s,a,c) = (p*floor(u/q)+g[u%q]+c) mod M, u=s+a*M.
// find R, phi: for s in R, all a, exists c: next in R and m*w[s%q]+1+phi[next] <= phi[s]
const [p,q]=[+process.argv[2],+process.argv[3]];
const g=JSON.parse(process.argv[4]), w=JSON.parse(process.argv[5]);
const M=+process.argv[6], A=+process.argv[7], d=+process.argv[8], m=+process.argv[9];
const cap=M*(m*Math.max(...w.map(Math.abs))+1)+1;
const nxt=new Int32Array(M*A*(d+1));
for(let s=0;s<M;s++) for(let a=0;a<A;a++){ const u=s+a*M; const base=p*Math.floor(u/q)+g[u%q];
  for(let c=0;c<=d;c++) nxt[(s*A+a)*(d+1)+c]=(((base+c)%M)+M)%M; }
let inR=new Uint8Array(M).fill(1);
let phi=new Float64Array(M);
while(true){
  phi.fill(0);
  let changed=true, it=0;
  while(changed){ changed=false; it++;
    for(let s=0;s<M;s++){ if(!inR[s]) continue; if(phi[s]>=cap) continue;
      let worst=-Infinity;
      for(let a=0;a<A;a++){ let best=Infinity; const o=(s*A+a)*(d+1);
        for(let c=0;c<=d;c++){ const n=nxt[o+c]; if(inR[n]){ const v=phi[n]; if(v<best)best=v; } }
        if(best>worst)worst=best; }
      let nv=Math.max(0, m*w[s%q]+1+worst); if(nv>cap) nv=cap;
      if(nv>phi[s]){ phi[s]=nv; changed=true; } }
  }
  let bad=0; for(let s=0;s<M;s++) if(inR[s]&&phi[s]>=cap){ inR[s]=0; bad++; }
  if(!bad) break;
}
let size=0,mx=0; for(let s=0;s<M;s++) if(inR[s]){size++; if(phi[s]>mx)mx=phi[s];}
console.log(`M=${M} d=${d} m=${m} |R|=${size} maxphi=${mx}`);
if(process.argv[10]){ require('fs').writeFileSync(process.argv[10], JSON.stringify({R:Array.from(inR),phi:Array.from(phi)})); }
