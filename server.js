const http=require('http'),fs=require('fs'),path=require('path'),crypto=require('crypto');
const rooms={},PORT=process.env.PORT||3000;
const shuffle=a=>{for(let i=a.length-1;i>0;i--){const j=crypto.randomInt(i+1);[a[i],a[j]]=[a[j],a[i]]}return a};
const mk=()=>{const t=[];let id=0;for(let r=0;r<2;r++)for(let c=0;c<4;c++)for(let n=1;n<=13;n++)t.push({id:id++,c,n});t.push({id:id++,c:0,n:0,f:1},{id:id++,c:0,n:0,f:1});return t};
const eff=(t,o)=>t.f?{c:o.c,n:o.n,w:0}:{c:t.c,n:t.n,w:+(t.c==o.c&&t.n==o.n)};
// Seri/per puanı; geçersizse 0
function pts(ts,o){const e=ts.map(t=>eff(t,o)),r=e.filter(x=>!x.w),L=e.length;if(L<3||!r.length)return 0;
 if(L<=4&&r.every(x=>x.n==r[0].n)&&new Set(r.map(x=>x.c)).size==r.length)return r[0].n*L;
 if(L<=13&&r.every(x=>x.c==r[0].c)&&new Set(r.map(x=>x.n)).size==r.length)
  for(let s=1;s+L-1<=13;s++)if(r.every(x=>x.n>=s&&x.n<=s+L-1)){let p=0;for(let k=s;k<s+L;k++)p+=(k-1)%13+1;return p}
 return 0}
const pairOk=(ts,o)=>{if(ts.length!=2)return 0;const e=ts.map(t=>eff(t,o));return e.some(x=>x.w)||(e[0].c==e[1].c&&e[0].n==e[1].n)};
const setDl=R=>{const g=R.g,s=R.seats[g.turn];g.off=0;g.dl=Date.now()+(s.bot||s.auto?1500:R.opts.sure?R.opts.sure*1000+(g.tc<4?20000:0):1e15)};
function build(h,o,ord){let p=h.filter(t=>!eff(t,o).w),G=[];const E=t=>eff(t,o),
 runs=()=>{for(let c=0;c<4;c++){const a=p.filter(t=>E(t).c==c),ns=[...new Set(a.map(t=>E(t).n))].sort((x,y)=>x-y);let i=0;while(i<ns.length){let j=i;while(j+1<ns.length&&ns[j+1]==ns[j]+1)j++;if(j-i>=2){const q=[];for(let k=i;k<=j;k++)q.push(a.find(x=>E(x).n==ns[k]&&p.includes(x)));G.push(q);p=p.filter(t=>!q.includes(t))}i=j+1}}},
 sets=()=>{for(let n=1;n<=13;n++){const a=[];for(let c=0;c<4;c++){const t=p.find(x=>E(x).n==n&&E(x).c==c);t&&a.push(t)}if(a.length>=3){G.push(a);p=p.filter(t=>!a.includes(t))}}};
 ord?(sets(),runs()):(runs(),sets());return{G,p}}
const best=(h,o)=>{const a=build(h,o,0),b=build(h,o,1);return a.G.flat().length>=b.G.flat().length?a:b};
const worst=(R,h)=>{const o=R.g.o,E=t=>eff(t,o),B=best(h,o);let c=B.p.length?B.p:h.filter(t=>!E(t).w);if(!c.length)c=h;
 if(R.opts.ceza){const ok=c.filter(t=>!R.g.table.some(x=>!x.pair&&pts([...x.t,t],o)));if(ok.length)c=ok}
 const f=t=>h.filter(u=>u!=t&&(E(u).c==E(t).c&&Math.abs(E(u).n-E(t).n)<=2||E(u).n==E(t).n)).length;
 return c.reduce((m,t)=>f(t)<f(m)||(f(t)==f(m)&&E(t).n>E(m).n)?t:m)};
// Bot oynar; süresi dolan insan için sadece çek+at yapar
function auto(R,bot){const g=R.g,s=g.turn,p=R.seats[s].pid,o=g.o,h=()=>g.hands[s],call=x=>act({r:R.id,p,auto:1,...x}),cov=x=>best(x,o).G.flat().length;
 if(g.side!=null)call({t:'undo'});
 if(g.phase=='draw'){const d=g.disc[(s+3)%4].slice(-1)[0],need=R.opts.katla?Math.max(101,g.lastOpen+1):101,B2=d&&best([...h(),d],o),
  ok=bot&&d&&!g.noSide&&(g.opened[s]?g.table.some(x=>!x.pair&&pts([...x.t,d],o)):B2.G.some(x=>x.includes(d))&&B2.G.reduce((a,x)=>a+pts(x,o),0)>=need);
  call({t:ok?'drawDisc':'drawDeck'});if(g.over||g.turn!=s)return}
 if(bot){const B=best(h(),o),need=R.opts.katla?Math.max(101,g.lastOpen+1):101;let gr=B.G.map(x=>x.map(t=>t.id));
  if(gr.flat().length>=h().length){const l=gr[gr.length-1];l&&(l.length>3?l.pop():gr.pop())}
  if(gr.length&&(g.opened[s]==1||B.G.reduce((a,x)=>a+pts(x,o),0)>=need))call({t:'open',gr});
  if(g.opened[s]==1)for(const t of h().filter(t=>!eff(t,o).w))for(let i=0;i<g.table.length;i++)if(!call({t:'add',tile:t.id,gi:i}).err)break}
 if(g.side!=null){call({t:'undo'});call({t:'drawDeck'});if(g.over)return}
 call({t:'discard',tile:worst(R,h()).id})}
function deal(R){const d=shuffle(mk()),gos=d.splice(d.findIndex(t=>!t.f),1)[0],st=R.dealer;
 const hands=[0,1,2,3].map(i=>d.splice(0,i==st?22:21));
 R.g={rk:++R.rn,gos,o:{c:gos.c,n:gos.n%13+1},deck:d,hands,disc:[[],[],[],[]],table:[],opened:[0,0,0,0],pen:[0,0,0,0],turn:st,phase:'play',lastOpen:0,lastPairs:0,over:null,dl:0,off:0,side:null,noSide:0,sideFrom:0,ot:[-1,-1,-1,-1],tc:0};setDl(R);
 R.log.push('Yeni el başladı.')}
function endRound(R,w,dbl,elden){const g=R.g,M=(dbl?2:1)*(elden?2:1)*(w!=null&&g.opened[w]==2?2:1),
 base=i=>{if(!g.opened[i])return 202;const h=g.hands[i];return(h.reduce((a,t)=>a+eff(t,g.o).n,0)+101*h.filter(t=>eff(t,g.o).w).length)*(g.opened[i]==2?2:1)},
 d=[0,1,2,3].map(i=>g.pen[i]+(i==w?-101*M:R.opts.pair&&w!=null&&i==(w+2)%4?0:M*base(i)));
 d.forEach((x,i)=>R.scores[i]+=x);g.over={w,d,M};R.dealer=(R.dealer+1)%4;R.hn++;if(R.hn>=R.opts.hands)R.final=1;g.overAt=Date.now();
 R.log.push(w==null?'Taşlar bitti, el berabere.':R.seats[w].name+' eli bitirdi'+(M>1?` (x${M}${dbl?', okeyle':''}${elden?', elden':''})`:'')+'!')}
function next(R){const g=R.g;g.turn=(g.turn+1)%4;g.phase='draw';g.side=null;g.noSide=0;g.tc++;if(!g.deck.length)endRound(R,null);else setDl(R)}
function swap(g,gr,t,h){const o=g.o,wi=gr.t.findIndex(x=>eff(x,o).w);if(wi<0)return'Bu taş buraya işlemiyor';
 const rest=gr.t.filter((x,i)=>i!=wi),c=[];for(let k=0;k<4;k++)for(let n=1;n<=13;n++){const f=k==o.c&&n==o.n?{id:-1,f:1,c:0,n:0}:{id:-1,c:k,n};if(pts([...rest,f],o))c.push([k,n])}
 const e=eff(t,o);if(c.length!=1)return'Okey yerine gelecek taş belli değil, alınamaz';if(e.w||e.c!=c[0][0]||e.n!=c[0][1])return'Bu taş okeyin yerine uymuyor';
 const w=gr.t[wi];gr.t[wi]=t;g.hands[g.turn]=h.filter(x=>x!=t).concat(w);return''}
function act(b){
 if(b.t=='new'){const id=crypto.randomBytes(4).toString('hex');rooms[id]={id,host:b.p,seats:[null,null,null,null],opts:{pair:0,katla:0,ceza:1,bots:0,sure:60,help:1,hands:3},scores:[0,0,0,0],dealer:0,rn:0,hn:0,final:0,g:null,log:[],chat:[],cl:[],t:Date.now()};return{id}}
 const R=rooms[b.r];if(!R)return{err:'Masa bulunamadı'};R.t=Date.now();
 let s=R.seats.findIndex(x=>x&&x.pid==b.p);const g=R.g,live=g&&!g.over,say=m=>R.log.push(m);
 if(b.t=='join'){if(s>=0)return{};s=R.seats.findIndex(x=>!x);if(s<0)return{err:'Masa dolu'};R.seats[s]={pid:b.p,name:String(b.name||'Oyuncu').replace(/[<>&"'`]/g,'').slice(0,14)||'Oyuncu'};say(R.seats[s].name+' masaya oturdu.');return{}}
 if(s<0)return{err:'Masada değilsin'};if(!b.auto&&b.t!='chat'){R.seats[s].miss=0;R.seats[s].auto=0}
 if(b.t=='chat'){const m=String(b.m||'').trim().slice(0,200);if(m)R.chat.push({n:R.seats[s].name,s,m});return{}}
 if(b.t=='opts'){if(b.p!=R.host||live)return{err:'Sadece kurucu, el dışında değiştirebilir'};
 const nb=Math.max(0,Math.min(3,+b.o.bots||0)),hs=R.seats.map(x=>x&&x.bot?null:x),fr=[3,2,1,0].filter(i=>!hs[i]);if(fr.length<nb)return{err:'Botlar için masada boş yer yok'};
 for(const k of['pair','katla','ceza','help'])R.opts[k]=+!!b.o[k];R.opts.sure=[0,30,45,60].includes(+b.o.sure)?+b.o.sure:60;R.opts.bots=nb;R.opts.hands=[1,3,5,7].includes(+b.o.hands)?+b.o.hands:3;
 R.seats=hs;fr.slice(0,nb).forEach((i,k)=>R.seats[i]={pid:'bot'+i,name:'Bot '+(k+1),bot:1});return{}}
 if(b.t=='newgame'){if(b.p!=R.host)return{err:'Sadece kurucu başlatabilir'};if(live)return{err:'El sürüyor'};R.scores=[0,0,0,0];R.hn=0;R.final=0;R.dealer=0;R.g=null;R.log.push('Yeni oyun için hazırlık.');return{}}
 if(b.t=='start'){if(R.final)return{err:'Maç bitti, "Yeni Oyun" başlat'};if(b.p!=R.host)return{err:'Sadece kurucu başlatabilir'};if(live)return{err:'El sürüyor'};if(R.seats.some(x=>!x))return{err:'4 oyuncu gerekli'};deal(R);return{}}
 if(!live)return{err:'El başlamadı'};if(g.turn!=s)return{err:'Sıra sende değil'};
 const h=g.hands[s],nm=R.seats[s].name;
 if(b.t=='drawDeck'||b.t=='drawDisc'){if(g.phase!='draw')return{err:'Zaten taş çektin'};
  if(b.t=='drawDeck'){if(!g.deck.length){endRound(R,null);return{}}h.push(g.deck.pop())}
  else{if(g.noSide)return{err:'Taşı geri bıraktın, bu turda desteden çekmelisin'};const f=(s+3)%4,p=g.disc[f];if(!p.length)return{err:'Alınacak taş yok'};const t=p.pop();h.push(t);say(nm+' yandan taş çekti.');g.side=t.id;g.sideFrom=f}
  g.phase='play';return{}}
 if(g.phase!='play')return{err:'Önce taş çek'};
 if(b.t=='undo'){if(g.side==null)return{err:'Geri bırakılacak taş yok'};const i=h.findIndex(t=>t.id==g.side);g.disc[g.sideFrom].push(h.splice(i,1)[0]);g.side=null;g.phase='draw';g.noSide=1;say(nm+' açamadı, taşı geri bıraktı.');return{}}
 if(b.t=='open'){if(b.k&&b.gr)b.gr=b.gr.map(a=>a.map(i=>h.find(t=>t.id==i))).filter(G=>G.every(Boolean)&&(b.k=='seri'?pts(G,g.o):G.length==2&&pairOk(G,g.o))).map(G=>G.map(t=>t.id));
  if(b.k&&(!b.gr||!b.gr.length))return{err:b.k=='seri'?'Istakanda geçerli seri/per yok (12-13-1 geçerli değil)':'Istakanda geçerli çift yok'};const ids=(b.gr||[]).flat();if(!b.gr||!b.gr.length||new Set(ids).size!=ids.length||!ids.every(i=>h.some(t=>t.id==i)))return{err:'Geçersiz seçim'};
  if(ids.length>=h.length)return{err:'Atmak için en az 1 taş elde kalmalı'};
  if(g.side!=null&&!g.opened[s]&&!ids.includes(g.side))return{err:'Soldan çektiğin taşı da açılışa katmalısın (ya da geri bırak)'};
  const G=b.gr.map(a=>a.map(i=>h.find(t=>t.id==i))),isP=G.every(x=>x.length==2);let tot=0;
  if(g.opened[s]==2){if(!isP)return{err:'Çift açtığın için yeni seri açamazsın, işleyebilirsin'};if(!G.every(x=>pairOk(x,g.o)))return{err:'Geçersiz çift var'}}
  else if(!g.opened[s]&&isP){const need=R.opts.katla?Math.max(5,g.lastPairs+1):5;if(G.length<need)return{err:`Çift sayısı ${G.length}, gerekli ${need}`};if(!G.every(x=>pairOk(x,g.o)))return{err:'Geçersiz çift var'};g.lastPairs=G.length;g.opened[s]=2;g.ot[s]=g.tc}
  else{const ps=G.map(x=>pts(x,g.o));if(ps.some(p=>!p))return{err:'Geçersiz seri/per var (12-13-1 geçerli değil)'};tot=ps.reduce((a,b)=>a+b);
   if(!g.opened[s]){const need=R.opts.katla?Math.max(101,g.lastOpen+1):101;if(tot<need)return{err:`Açılış puanı ${tot}, gerekli ${need}`};g.lastOpen=tot;g.opened[s]=1;g.ot[s]=g.tc}}
  if(ids.includes(g.side))g.side=null;g.hands[s]=h.filter(t=>!ids.includes(t.id));G.forEach(x=>g.table.push({o:s,t:x,pair:+(isP&&g.opened[s]==2)}));say(nm+' açtı'+(tot?` (${tot})`:' (çift)')+'.');return{}}
 if(b.t=='add'){const t=h.find(x=>x.id==b.tile);if(!g.opened[s])return{err:'Önce elini açmalısın'};if(!t)return{err:'Taş yok'};if(h.length<2)return{err:'Atmak için en az 1 taş elde kalmalı'};
  const g0=g.table[b.gi];if(b.gi>=0&&g0&&!g0.pair&&g0.t.some(x=>eff(x,g.o).w)&&!swap(g,g0,t,h)){if(g.side==t.id)g.side=null;say(nm+' yerden okey aldı.');return{}}
  for(const i of b.gi>=0?[b.gi]:g.table.map((_,i)=>i)){const gr=g.table[i];if(gr&&!gr.pair&&pts([...gr.t,t],g.o)){gr.t.push(t);g.hands[s]=h.filter(x=>x!=t);if(g.side==t.id)g.side=null;say(nm+' taş işledi.');return{}}}
  return{err:'Bu taş hiçbir yere işlemiyor'}}
 if(b.t=='addPair'){const ts=(b.tiles||[]).map(i=>h.find(t=>t.id==i));if(!g.opened[s])return{err:'Önce elini açmalısın'};if(!g.table.some(x=>x.pair))return{err:'Yerde açılmış çift yok'};
  if(ts.length!=2||ts.some(x=>!x)||ts[0]==ts[1]||!pairOk(ts,g.o))return{err:'Geçersiz çift'};if(h.length<3)return{err:'Atmak için en az 1 taş elde kalmalı'};
  g.table.push({o:s,t:ts,pair:1});g.hands[s]=h.filter(t=>!ts.includes(t));if(ts.some(t=>t.id==g.side))g.side=null;say(nm+' çift işledi.');return{}}
 if(b.t=='discard'){if(g.side!=null)return{err:'Soldan çektiğin taşı kullanmalısın (aç / işle); olmuyorsa taşı geri bırak'};const i=h.findIndex(t=>t.id==b.tile);if(i<0)return{err:'Taş yok'};
  const t=h.splice(i,1)[0],fin=!h.length,ow=eff(t,g.o).w;
  if(!fin&&R.opts.ceza&&(ow||g.table.some(x=>!x.pair&&pts([...x.t,t],g.o)))){g.pen[s]+=101;say(nm+(ow?' okey attı':' işlek taş attı')+': +101 ceza!')}
  g.disc[s].push(t);if(fin)endRound(R,s,ow,g.opened.every((o,j)=>j==s||!o)&&g.ot[s]===g.tc);else next(R);return{}}
 return{err:'Bilinmeyen işlem'}}
function view(R,s){const g=R.g,v={id:R.id,seat:s,opts:R.opts,names:R.seats.map(x=>x&&x.name),hostSeat:R.seats.findIndex(x=>x&&x.pid==R.host),scores:R.scores,hn:R.hn,final:R.final,log:R.log.slice(-40),on:R.seats.map(x=>x&&(x.bot||R.cl.some(c=>c.p==x.pid))),chat:R.chat.slice(-30)};
 if(g)v.g={rk:g.rk,gos:g.gos,o:g.o,deck:g.deck.length,n:g.hands.map(h=>h.length),hand:s>=0?g.hands[s]:[],disc:g.disc.map(d=>d[d.length-1]||null),table:g.table,opened:g.opened,turn:g.turn,phase:g.phase,over:g.over,isl:R.opts.help&&s>=0?g.hands[s].filter(t=>g.table.some(x=>!x.pair&&pts([...x.t,t],g.o))).map(t=>t.id):[],side:g.side,noSide:g.noSide,tl:g.dl>1e14||R.seats[g.turn].bot||R.seats[g.turn].auto?null:Math.max(0,g.dl-Date.now()),last:g.lastOpen,lastP:g.lastPairs};return v}
const send=(R,c)=>c.res.write('data: '+JSON.stringify(view(R,R.seats.findIndex(x=>x&&x.pid==c.p)))+'\n\n');
http.createServer((req,res)=>{const u=new URL(req.url,'http://x'),q=Object.fromEntries(u.searchParams);
 if(u.pathname=='/ev'){res.writeHead(200,{'Content-Type':'text/event-stream','Cache-Control':'no-cache','X-Accel-Buffering':'no'});const R=rooms[q.r];
  if(!R){res.write('data: {"err":"Masa bulunamadı (sunucu yeniden başlamış olabilir)"}\n\n');return res.end()}
  const c={res,p:q.p};R.cl.push(c);R.cl.forEach(x=>send(R,x));const hb=setInterval(()=>res.write(': hb\n\n'),20000);req.on('close',()=>{clearInterval(hb);R.cl=R.cl.filter(x=>x!=c);R.cl.forEach(x=>send(R,x))});return}
 if(req.method=='POST'&&u.pathname=='/api'){let d='';req.on('data',x=>{d+=x;if(d.length>1e5)req.destroy()});req.on('end',()=>{let r;try{r=act(JSON.parse(d))}catch(e){r={err:'Hata: '+e.message}}
  res.writeHead(200,{'Content-Type':'application/json'});res.end(JSON.stringify(r));const R=rooms[JSON.parse(d||'{}').r];if(R&&!r.err)R.cl.forEach(c=>send(R,c))});return}
 fs.readFile(path.join(__dirname,'public','index.html'),(e,b)=>{res.writeHead(e?404:200,{'Content-Type':'text/html; charset=utf-8'});res.end(b||'yok')})
}).listen(PORT,()=>console.log('101 Okey çalışıyor: http://localhost:'+PORT));
setInterval(()=>{for(const k in rooms)if(!rooms[k].cl.length&&Date.now()-rooms[k].t>6*36e5)delete rooms[k]},6e5);
// Süre/bot/bağlantısı kopan oyuncu zamanlayıcısı
setInterval(()=>{const now=Date.now();for(const k in rooms){const R=rooms[k],g=R.g;if(g&&g.over&&!R.final&&now-g.overAt>15000){try{deal(R)}catch(e){console.log(e)}R.cl.forEach(c=>send(R,c));continue}
 if(!g||g.over)continue;const x=R.seats[g.turn],off=!x.bot&&!R.cl.some(c=>c.p==x.pid);g.off=off?g.off||now+15000:0;
 if(now>=g.dl||(off&&now>=g.off)){const bt=!!(x.bot||x.auto);if(!x.bot){x.miss=(x.miss||0)+1;if(x.miss>=2)x.auto=1}try{auto(R,bt)}catch(e){console.log(e)}R.cl.forEach(c=>send(R,c))}}},1000);
