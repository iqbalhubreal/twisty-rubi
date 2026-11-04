import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';

const $ = id => document.getElementById(id);
const V3 = THREE.Vector3;
const V = (x,y,z) => new V3(x,y,z);
const wait = ms => new Promise(r => setTimeout(r, ms));

/* ---------------- Renderer / scene ---------------- */
const stage = $('stage');
const renderer = new THREE.WebGLRenderer({ antialias:true });
renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
stage.appendChild(renderer.domElement);
const scene = new THREE.Scene();
scene.background = new THREE.Color(0x14161b);
const camera = new THREE.PerspectiveCamera(40, 1, 0.01, 1000);
scene.add(camera);
const controls = new OrbitControls(camera, renderer.domElement);
controls.enableDamping = true;
scene.add(new THREE.HemisphereLight(0xffffff, 0x303848, 1.15));
const key = new THREE.DirectionalLight(0xffffff, 1.7); key.position.set(1, 1.6, 1.2); camera.add(key);
const fill = new THREE.DirectionalLight(0xffffff, 0.5); fill.position.set(-1.5, -0.6, 0.6); camera.add(fill);
const root = new THREE.Group(); scene.add(root);

function resize(){
  const w = stage.clientWidth, h = stage.clientHeight;
  renderer.setSize(w, h); camera.aspect = w / Math.max(1,h); camera.updateProjectionMatrix();
}
window.addEventListener('resize', resize);

/* ---------------- Colours ---------------- */
const CUBE_COLS = ['#e0262f','#ff8a1a','#ffffff','#ffd60a','#19a94b','#1f5fd6']; // +x -x +y -y +z -z
const TETRA_COLS = ['#e0262f','#19a94b','#1f5fd6','#ffd60a'];
const OCTA_COLS = ['#ffffff','#e0262f','#19a94b','#8a3fd1','#ffd60a','#ff8a1a','#1f5fd6','#9aa0a6'];
const DODE_COLS = ['#ffffff','#e0262f','#19a94b','#8a3fd1','#ffd60a','#1f5fd6','#fff2a8','#ff7ab6','#8fe36a','#ff8a1a','#6fc8ff','#9aa0a6'];

/* ---------------- Global state ---------------- */
let P = null;                 // current puzzle
let history = [];             // all applied moves {g,r,k}
let queue = [], qi = 0, anim = null, accum = 0, queueActive = false, onDone = null;
let seqToken = 0, phase = '', runTotal = 0;
let dirtyFlag = new Uint8Array(0), dirtyList = [], needInst = false;
let liveTps=6, recTps=5;
let recorder=null, recStart=0;

/* ---------------- ASMR nature audio ---------------- */
let audio=null, natureBed=null, lastNatureCue=0;
function ensureAudio(){
  try{
    if(!audio){
      const Ctx=window.AudioContext||window.webkitAudioContext; audio=new Ctx();
      audio.master=audio.createGain(); audio.master.gain.value=+$('natureVol').value/100; audio.master.connect(audio.destination);
    }
    if(audio.state==='suspended') audio.resume();
    if($('nature').checked) startNature();
  }catch(e){ /* audio is optional */ }
}
function startNature(){
  if(!audio||natureBed) return;
  const src=audio.createBufferSource(), buf=audio.createBuffer(1,audio.sampleRate*2,audio.sampleRate), data=buf.getChannelData(0);
  for(let i=0;i<data.length;i++) data[i]=Math.random()*2-1;
  src.buffer=buf; src.loop=true;
  const filter=audio.createBiquadFilter(), gain=audio.createGain(); filter.type='lowpass'; filter.frequency.value=620; filter.Q.value=0.5;
  gain.gain.value=0.016; src.connect(filter); filter.connect(gain); gain.connect(audio.master); src.start(); natureBed={src};
}
function stopNature(){ if(natureBed){ natureBed.src.stop(); natureBed=null; } }
function playNatureCue(){
  if(!$('nature').checked||!audio||audio.state!=='running') return;
  const now=audio.currentTime; if(now-lastNatureCue<0.08) return; lastNatureCue=now;
  const o=audio.createOscillator(), g=audio.createGain(); o.type='sine'; o.frequency.setValueAtTime(360+Math.random()*160,now);
  o.frequency.exponentialRampToValueAtTime(180,now+0.2); g.gain.setValueAtTime(0.0001,now); g.gain.exponentialRampToValueAtTime(0.03,now+0.01);
  g.gain.exponentialRampToValueAtTime(0.0001,now+0.24); o.connect(g); g.connect(audio.master); o.start(now); o.stop(now+0.26);
}

const LAT = new Int32Array(129*129*129);
const S1 = 129*129, S2 = 129, BASE = 64*S1 + 64*S2 + 64, STR = [S1, S2, 1];

/* ================================================================
   CUBE FAMILY (instanced – handles up to 50×50×50 and cuboids)
   ================================================================ */
function roundedSquare(s, r){
  const h = s/2, sh = new THREE.Shape();
  sh.moveTo(-h+r,-h); sh.lineTo(h-r,-h); sh.quadraticCurveTo(h,-h,h,-h+r);
  sh.lineTo(h,h-r); sh.quadraticCurveTo(h,h,h-r,h); sh.lineTo(-h+r,h);
  sh.quadraticCurveTo(-h,h,-h,h-r); sh.lineTo(-h,-h+r); sh.quadraticCurveTo(-h,-h,-h+r,-h);
  return new THREE.ShapeGeometry(sh, 3);
}

function buildLattice(A, B, C, name, slug){
  const dims = [A, B, C];
  const coords = [];
  for (let x=0;x<A;x++) for (let y=0;y<B;y++) for (let z=0;z<C;z++)
    if (x===0||x===A-1||y===0||y===B-1||z===0||z===C-1) coords.push(2*x-(A-1), 2*y-(B-1), 2*z-(C-1));
  const n = coords.length / 3;
  const pos2 = Int16Array.from(coords);
  LAT.fill(-1);
  for (let i=0;i<n;i++) LAT[BASE + pos2[3*i]*S1 + pos2[3*i+1]*S2 + pos2[3*i+2]] = i;

  const dirs = [V(1,0,0),V(-1,0,0),V(0,1,0),V(0,-1,0),V(0,0,1),V(0,0,-1)];
  const pieces = [], stickers = [], Lb = [], Ls = [], pst = [];
  const zAxis = V(0,0,1);
  for (let i=0;i<n;i++){
    const x=pos2[3*i], y=pos2[3*i+1], z=pos2[3*i+2];
    const c = V(x/2, y/2, z/2);
    pieces.push({ q: new THREE.Quaternion() });
    Lb.push(new THREE.Matrix4().makeTranslation(c.x, c.y, c.z));
    const list = [];
    const ext = [x===A-1, x===-(A-1), y===B-1, y===-(B-1), z===C-1, z===-(C-1)];
    for (let d=0; d<6; d++){
      if (!ext[d]) continue;
      const q = new THREE.Quaternion().setFromUnitVectors(zAxis, dirs[d]);
      const p = c.clone().addScaledVector(dirs[d], 0.483);
      Ls.push(new THREE.Matrix4().compose(p, q, new V3(1,1,1)));
      list.push(stickers.length);
      stickers.push({ p:i, n:dirs[d], c:d });
    }
    pst.push(list);
  }
  const bodyMesh = new THREE.InstancedMesh(new THREE.BoxGeometry(0.96,0.96,0.96),
    new THREE.MeshStandardMaterial({ color:0x0b0b0d, roughness:0.55, metalness:0.1 }), n);
  const stkMesh = new THREE.InstancedMesh(roundedSquare(0.84, 0.13),
    new THREE.MeshStandardMaterial({ color:0xffffff, roughness:0.33, metalness:0.0 }), stickers.length);
  bodyMesh.frustumCulled = false; stkMesh.frustumCulled = false;
  const col = new THREE.Color();
  for (let s=0; s<stickers.length; s++){ col.set(CUBE_COLS[stickers[s].c]); stkMesh.setColorAt(s, col); }
  for (let i=0;i<n;i++) bodyMesh.setMatrixAt(i, Lb[i]);
  for (let s=0;s<stickers.length;s++) stkMesh.setMatrixAt(s, Ls[s]);
  root.add(bodyMesh, stkMesh);

  const axes = [], choices = [];
  for (let a=0;a<3;a++){
    const b=(a+1)%3, e=(a+2)%3, square = dims[b]===dims[e];
    axes.push({ v: dirs[2*a], order:4, amounts: square ? [1,2,3] : [2], layers: dims[a] });
    if (dims[a] > 1) for (let r=0;r<dims[a];r++) choices.push({ g:a, r });
  }
  return { kind:'lattice', name, slug, dims, pos2, pieces, stickers, Lb, Ls, pst, bodyMesh, stkMesh,
           axes, choices, faceNormals: dirs, radius: 0.5*Math.hypot(A,B,C),
           info: `${n.toLocaleString()} pieces · ${stickers.length.toLocaleString()} stickers` };
}

/* ================================================================
   GENERIC CUT-POLYHEDRON ENGINE (Pyraminx, Skewb, Megaminx, ...)
   ================================================================ */
function centroid(pts){ const c=new V3(); for(const p of pts) c.add(p); return c.divideScalar(pts.length); }
function newell(pts){
  const n=new V3(), m=pts.length;
  for (let i=0;i<m;i++){ const a=pts[i], b=pts[(i+1)%m];
    n.x+=(a.y-b.y)*(a.z+b.z); n.y+=(a.z-b.z)*(a.x+b.x); n.z+=(a.x-b.x)*(a.y+b.y); }
  return n.normalize();
}
function cleanRing(r){
  const o=[];
  for (const p of r) if (!o.length || o[o.length-1].distanceToSquared(p) > 1e-16) o.push(p);
  while (o.length>1 && o[0].distanceToSquared(o[o.length-1]) <= 1e-16) o.pop();
  return o;
}
function basis(n){
  const t = Math.abs(n.x) < 0.9 ? V(1,0,0) : V(0,1,0);
  const u = new V3().crossVectors(n, t).normalize();
  const w = new V3().crossVectors(n, u);
  return [u, w];
}
// keep side n·x <= d ; new cap face gets capTag
function clipPoly(faces, n, d, capTag){
  const out=[], cap=[];
  for (const f of faces){
    const P0=f.pts, m=P0.length, res=[];
    for (let i=0;i<m;i++){
      const a=P0[i], b=P0[(i+1)%m];
      const da=n.dot(a)-d, db=n.dot(b)-d;
      if (da <= 1e-9) res.push(a);
      if (Math.abs(da) <= 1e-9) cap.push(a);
      if ((da < -1e-9 && db > 1e-9) || (da > 1e-9 && db < -1e-9)){
        const p = a.clone().lerp(b, da/(da-db)); res.push(p); cap.push(p);
      }
    }
    const cl = cleanRing(res);
    if (cl.length >= 3) out.push({ pts: cl, tag: f.tag });
  }
  const cp=[];
  for (const p of cap) if (!cp.some(q => q.distanceToSquared(p) < 1e-12)) cp.push(p);
  if (cp.length >= 3){
    const c = centroid(cp), [u,w] = basis(n);
    cp.sort((A,B)=>{ const a=A.clone().sub(c), b=B.clone().sub(c);
      return Math.atan2(a.dot(w),a.dot(u)) - Math.atan2(b.dot(w),b.dot(u)); });
    out.push({ pts: cp, tag: capTag });
  }
  return out;
}
function splitCells(cells, n, h){
  const out=[], nn=n.clone().negate();
  for (const c of cells){
    let mn=Infinity, mx=-Infinity;
    for (const f of c) for (const p of f.pts){ const d=n.dot(p)-h; if(d<mn)mn=d; if(d>mx)mx=d; }
    if (mn < -1e-7 && mx > 1e-7){
      const a=clipPoly(c,n,h,-1), b=clipPoly(c,nn,-h,-1);
      if (a.length>=4) out.push(a); if (b.length>=4) out.push(b);
    } else out.push(c);
  }
  return out;
}
function boxFaces(s){
  const v=(x,y,z)=>V(x*s,y*s,z*s);
  return [
    [v(1,-1,-1),v(1,1,-1),v(1,1,1),v(1,-1,1)], [v(-1,-1,-1),v(-1,-1,1),v(-1,1,1),v(-1,1,-1)],
    [v(-1,1,-1),v(-1,1,1),v(1,1,1),v(1,1,-1)], [v(-1,-1,-1),v(1,-1,-1),v(1,-1,1),v(-1,-1,1)],
    [v(-1,-1,1),v(1,-1,1),v(1,1,1),v(-1,1,1)], [v(-1,-1,-1),v(-1,1,-1),v(1,1,-1),v(1,-1,-1)]
  ].map(pts=>({ pts, tag:-2 }));
}
// shrink a convex polygon inward by a fixed border (sticker look)
function insetPolygon(pts, N, base){
  const c=centroid(pts), [U,W]=basis(N);
  let p2 = pts.map(p=>{ const d=p.clone().sub(c); return [d.dot(U), d.dot(W)]; });
  let A=0; for (let i=0;i<p2.length;i++){ const a=p2[i], b=p2[(i+1)%p2.length]; A+=a[0]*b[1]-b[0]*a[1]; }
  if (A < 0) p2.reverse();
  const ed=[]; let inr=Infinity;
  for (let i=0;i<p2.length;i++){
    const a=p2[i], b=p2[(i+1)%p2.length], dx=b[0]-a[0], dy=b[1]-a[1], L=Math.hypot(dx,dy);
    if (L < 1e-9) continue;
    const nx=-dy/L, ny=dx/L;
    inr = Math.min(inr, -(a[0]*nx + a[1]*ny));
    ed.push({ a, dx:dx/L, dy:dy/L, nx, ny });
  }
  const delta = Math.min(base, 0.28*inr);
  let out=[]; const k=ed.length;
  for (let i=0;i<k;i++){
    const pe=ed[(i-1+k)%k], ce=ed[i];
    const px=pe.a[0]+pe.nx*delta, py=pe.a[1]+pe.ny*delta;
    const qx=ce.a[0]+ce.nx*delta, qy=ce.a[1]+ce.ny*delta;
    const den = pe.dx*ce.dy - pe.dy*ce.dx;
    if (Math.abs(den) < 1e-6) out.push([qx,qy]);
    else { const t=((qx-px)*ce.dy - (qy-py)*ce.dx)/den; out.push([px+pe.dx*t, py+pe.dy*t]); }
  }
  const ok = out.every(p => ed.every(e => (p[0]-e.a[0])*e.nx + (p[1]-e.a[1])*e.ny >= delta*0.97 - 1e-9));
  if (!ok){ const s=Math.max(0.5, 1-delta/inr); out = p2.map(p=>[p[0]*s,p[1]*s]); }
  return out.map(p => c.clone().addScaledVector(U,p[0]).addScaledVector(W,p[1]));
}
function fan(pts, n, P0, N0, C0, col){
  for (let i=1;i<pts.length-1;i++) for (const p of [pts[0],pts[i],pts[i+1]]){
    P0.push(p.x,p.y,p.z); N0.push(n.x,n.y,n.z); if (C0) C0.push(col.r,col.g,col.b);
  }
}

function buildGeneric(def){
  let cell = boxFaces(4);
  def.faces.forEach((f,i)=>{ cell = clipPoly(cell, f.n, f.d, i); });
  let R=0; for (const f of cell) for (const p of f.pts) R=Math.max(R,p.length());
  let cells=[cell];
  for (const ax of def.axes) for (const h of ax.cuts) cells = splitCells(cells, ax.v, h);

  const bodyMat = new THREE.MeshStandardMaterial({ color:0x0b0b0d, roughness:0.55, metalness:0.1 });
  const stkMat = new THREE.MeshStandardMaterial({ vertexColors:true, roughness:0.33, metalness:0.0 });
  const pieces=[], stickers=[], base=0.035*R, colObj=new THREE.Color();
  let visible=0;
  cells.forEach((c, idx)=>{
    const cc=new V3(); let cnt=0;
    for (const f of c) for (const p of f.pts){ cc.add(p); cnt++; }
    cc.divideScalar(cnt);
    const bp=[], bn=[], sp=[], sn=[], sc=[];
    let hasSt=false;
    for (const f of c){
      let pts=f.pts.slice(); const fc=centroid(pts); const nrm=newell(pts);
      if (nrm.dot(fc.clone().sub(cc)) < 0){ pts.reverse(); nrm.negate(); }
      fan(pts.map(p=>p.clone().sub(cc).multiplyScalar(0.985).add(cc)), nrm, bp, bn);
      if (f.tag >= 0){
        const fn = def.faces[f.tag].n;
        const ins = insetPolygon(pts, fn, base).map(p=>p.addScaledVector(fn, 0.0025*R));
        colObj.set(def.colors[f.tag]);
        fan(ins, fn, sp, sn, sc, colObj);
        stickers.push({ p:idx, n:fn.clone(), c:f.tag });
        hasSt=true;
      }
    }
    if (hasSt) visible++;
    const group=new THREE.Group();
    const bg=new THREE.BufferGeometry();
    bg.setAttribute('position', new THREE.Float32BufferAttribute(bp,3));
    bg.setAttribute('normal', new THREE.Float32BufferAttribute(bn,3));
    group.add(new THREE.Mesh(bg, bodyMat));
    if (sp.length){
      const sg=new THREE.BufferGeometry();
      sg.setAttribute('position', new THREE.Float32BufferAttribute(sp,3));
      sg.setAttribute('normal', new THREE.Float32BufferAttribute(sn,3));
      sg.setAttribute('color', new THREE.Float32BufferAttribute(sc,3));
      group.add(new THREE.Mesh(sg, stkMat));
    }
    root.add(group);
    pieces.push({ q:new THREE.Quaternion(), pos:cc.clone(), group });
  });

  const axes=[], choices=[];
  def.axes.forEach((ax,g)=>{
    const ranges=[];
    for (let j=0;j<=ax.cuts.length;j++) ranges.push([ j===0?-Infinity:ax.cuts[j-1], j===ax.cuts.length?Infinity:ax.cuts[j] ]);
    const amounts=[]; for (let k=1;k<ax.order;k++) amounts.push(k);
    axes.push({ v:ax.v, order:ax.order, amounts, ranges });
    for (const r of ax.allowed) choices.push({ g, r });
  });
  return { kind:'mesh', name:def.name, slug:def.slug, pieces, stickers, axes, choices,
           faceNormals: def.faces.map(f=>f.n), radius:R,
           info:`${visible} pieces · ${stickers.length} stickers` };
}

/* ---------------- Puzzle definitions ---------------- */
function puzzleDef(type, layers){
  const s3=Math.sqrt(3);
  const corners=[V(1,1,1),V(1,-1,-1),V(-1,1,-1),V(-1,-1,1)].map(v=>v.normalize());
  const cubeFaces=[V(1,0,0),V(-1,0,0),V(0,1,0),V(0,-1,0),V(0,0,1),V(0,0,-1)].map(n=>({n,d:1}));
  const octaFaces=[]; for (const x of [1,-1]) for (const y of [1,-1]) for (const z of [1,-1]) octaFaces.push({ n:V(x,y,z).normalize(), d:1/s3 });
  const phi=(1+Math.sqrt(5))/2, dn=[];
  for (const a of [1,-1]) for (const b of [1,-1]) dn.push(V(0,a,b*phi), V(a,b*phi,0), V(b*phi,0,a));
  const dodeFaces = dn.map(v=>({ n:v.normalize(), d:1 }));
  const dodeAxes=[]; for (const f of dodeFaces) if (!dodeAxes.some(a=>Math.abs(a.dot(f.n))>0.99)) dodeAxes.push(f.n.clone());
  const ax=(list,order,cuts,allowed)=>list.map(v=>({ v, order, cuts, allowed }));
  switch(type){
    case 'pyraminx': {
      const H=4/s3, cuts=[], allowed=[];
      for (let k=1;k<layers;k++){ cuts.push(-1/s3 + k*H/layers); allowed.push(k); }
      return { name:`Pyraminx (${layers} layers)`, slug:`pyraminx-${layers}`, colors:TETRA_COLS,
               faces:corners.map(v=>({ n:v.clone().negate(), d:1/s3 })), axes:ax(corners,3,cuts,allowed) };
    }
    case 'skewb':   return { name:'Skewb', slug:'skewb', colors:CUBE_COLS, faces:cubeFaces, axes:ax(corners,3,[0],[0,1]) };
    case 'dino':    return { name:'Dino Cube', slug:'dino-cube', colors:CUBE_COLS, faces:cubeFaces, axes:ax(corners,3,[-1/s3,1/s3],[0,2]) };
    case 'diamond': return { name:'Skewb Diamond', slug:'skewb-diamond', colors:OCTA_COLS, faces:octaFaces, axes:ax(corners,3,[0],[0,1]) };
    case 'fto':     { const c=1/(3*s3); return { name:'Face-Turning Octahedron', slug:'fto', colors:OCTA_COLS, faces:octaFaces, axes:ax(corners,3,[-c,c],[0,2]) }; }
    case 'megaminx':return { name:'Megaminx', slug:'megaminx', colors:DODE_COLS, faces:dodeFaces, axes:ax(dodeAxes,5,[-0.7,0.7],[0,2]) };
    case 'gigaminx':return { name:'Gigaminx', slug:'gigaminx', colors:DODE_COLS, faces:dodeFaces, axes:ax(dodeAxes,5,[-0.82,-0.62,0.62,0.82],[0,1,3,4]) };
  }
}

/* ---------------- Spec / build ---------------- */
const clampInt=(v,a,b)=>Math.max(a,Math.min(b,Math.round(+v||a)));
function readSpec(){
  const type=$('ptype').value;
  if (type==='cube'){ const n=clampInt($('nNum').value,2,50); return { type, n }; }
  if (type==='cuboid'){
    let A=clampInt($('dimA').value,1,30), B=clampInt($('dimB').value,1,30), C=clampInt($('dimC').value,1,30);
    if (A===1&&B===1&&C===1) C=2;
    return { type, A, B, C };
  }
  if (type==='pyraminx') return { type, n: clampInt($('pyRange').value,2,6) };
  return { type };
}
function defaultScramble(s){
  switch(s.type){
    case 'cube': return 10+6*s.n;
    case 'cuboid': return 10+3*(s.A+s.B+s.C);
    case 'pyraminx': return 8+6*s.n;
    case 'skewb': case 'diamond': return 15;
    case 'dino': return 30;
    case 'fto': return 40;
    case 'megaminx': return 70;
    case 'gigaminx': return 140;
  }
  return 30;
}
function disposeRoot(){
  root.traverse(o=>{ if (o.geometry) o.geometry.dispose(); if (o.material) o.material.dispose?.(); });
  while (root.children.length) root.remove(root.children[0]);
}
let lastSpecKey='';
function build(spec){
  disposeRoot();
  if (spec.type==='cube') P = buildLattice(spec.n,spec.n,spec.n, `${spec.n}×${spec.n}×${spec.n} Cube`, `cube-${spec.n}x${spec.n}`);
  else if (spec.type==='cuboid') P = buildLattice(spec.A,spec.B,spec.C, `${spec.A}×${spec.B}×${spec.C} Cuboid`, `cuboid-${spec.A}x${spec.B}x${spec.C}`);
  else P = buildGeneric(puzzleDef(spec.type, spec.n));
  history=[]; dirtyFlag=new Uint8Array(P.pieces.length); dirtyList=[]; needInst=false;
  const k=JSON.stringify(spec);
  if (k!==lastSpecKey){ lastSpecKey=k; frameCamera(); }
  $('pinfo').textContent = P.info;
}
function frameCamera(){
  const R=P.radius, d=R*3.3;
  camera.position.copy(V(1,0.8,1.3).normalize().multiplyScalar(d));
  controls.target.set(0,0,0);
  controls.minDistance=R*1.3; controls.maxDistance=R*15;
  camera.near=R*0.02; camera.far=R*100; camera.updateProjectionMatrix();
  controls.update();
}

/* ---------------- Moves ---------------- */
const _m=new THREE.Matrix4(), _t=new THREE.Matrix4(), _q=new THREE.Quaternion(), _q2=new THREE.Quaternion(), _v=new V3();

function showPiece(i,q){
  if (P.kind==='lattice'){
    _m.makeRotationFromQuaternion(q);
    _t.multiplyMatrices(_m,P.Lb[i]); P.bodyMesh.setMatrixAt(i,_t);
    for (const s of P.pst[i]){ _t.multiplyMatrices(_m,P.Ls[s]); P.stkMesh.setMatrixAt(s,_t); }
    needInst=true;
  } else P.pieces[i].group.quaternion.copy(q);
}
function markDirty(i){ if (!dirtyFlag[i]){ dirtyFlag[i]=1; dirtyList.push(i); } }
function flushDirty(){
  for (const i of dirtyList){ dirtyFlag[i]=0; showPiece(i,P.pieces[i].q); }
  dirtyList.length=0;
}
function members(m){
  const res=[];
  if (P.kind==='lattice'){
    const a=m.g, b=(a+1)%3, e=(a+2)%3, d=P.dims;
    const k0=BASE+(2*m.r-(d[a]-1))*STR[a];
    for (let u=-(d[b]-1); u<=d[b]-1; u+=2){
      const k1=k0+u*STR[b];
      for (let w=-(d[e]-1); w<=d[e]-1; w+=2){ const id=LAT[k1+w*STR[e]]; if (id>=0) res.push(id); }
    }
    return res;
  }
  const ax=P.axes[m.g], [lo,hi]=ax.ranges[m.r];
  for (let i=0;i<P.pieces.length;i++){ const d=ax.v.dot(P.pieces[i].pos); if (d>lo && d<hi) res.push(i); }
  return res;
}
function applyState(m, mem){
  mem = mem || members(m);
  const ax=P.axes[m.g];
  _q.setFromAxisAngle(ax.v, m.k*2*Math.PI/ax.order);
  if (P.kind==='lattice'){
    const a=m.g, b=(a+1)%3, e=(a+2)%3, pos=P.pos2;
    for (const id of mem){
      let u=pos[3*id+b], w=pos[3*id+e];
      for (let t=0;t<m.k;t++){ const nu=-w; w=u; u=nu; }
      pos[3*id+b]=u; pos[3*id+e]=w;
    }
    for (const id of mem) LAT[BASE+pos[3*id]*S1+pos[3*id+1]*S2+pos[3*id+2]]=id;
  }
  for (const id of mem){
    const p=P.pieces[id]; p.q.premultiply(_q).normalize();
    if (p.pos) p.pos.applyQuaternion(_q);
    markDirty(id);
  }
  history.push({ g:m.g, r:m.r, k:m.k });
}
function genScramble(n){
  const ch=P.choices, out=[]; if (!ch.length) return out;
  let prev=-1;
  for (let i=0;i<n;i++){
    let j; do { j=Math.floor(Math.random()*ch.length); } while (ch.length>1 && j===prev);
    prev=j; const c=ch[j], am=P.axes[c.g].amounts;
    out.push({ g:c.g, r:c.r, k:am[Math.floor(Math.random()*am.length)] });
  }
  return out;
}
function simplify(moves){
  const out=[];
  for (const m of moves){
    const ord=P.axes[m.g].order; let merged=false;
    for (let j=out.length-1;j>=0;j--){
      const o=out[j]; if (o.g!==m.g) break;
      if (o.r===m.r){ o.k=(o.k+m.k)%ord; if (o.k===0) out.splice(j,1); merged=true; break; }
    }
    if (!merged) out.push({ g:m.g, r:m.r, k:m.k });
  }
  return out;
}
function solveMoves(){
  return simplify(history).reverse().map(m=>({ g:m.g, r:m.r, k:(P.axes[m.g].order-m.k)%P.axes[m.g].order }));
}
function isSolved(){
  const fn=P.faceNormals, seen=new Int16Array(fn.length).fill(-1);
  for (const s of P.stickers){
    _v.copy(s.n).applyQuaternion(P.pieces[s.p].q);
    let best=0, bd=-2; for (let j=0;j<fn.length;j++){ const d=_v.dot(fn[j]); if (d>bd){ bd=d; best=j; } }
    if (seen[best]<0) seen[best]=s.c; else if (seen[best]!==s.c) return false;
  }
  return true;
}

/* ---------------- Animation engine ---------------- */
const ease = t => t<0.5 ? 4*t*t*t : 1-Math.pow(-2*t+2,3)/2;
const recNatural = () => !!recorder && $('natural').checked;

function startAnim(){
  const first=queue[qi++], grp=[first];
  if ($('groupAxis').checked)
    while (qi<queue.length && queue[qi].g===first.g && !grp.some(x=>x.r===queue[qi].r)) grp.push(queue[qi++]);
  const ax=P.axes[first.g];
  let maxAbs=1;
  const items=grp.map(m=>{
    let s=m.k; if (s>ax.order/2) s-=ax.order;
    maxAbs=Math.max(maxAbs,Math.abs(s));
    return { m, mem:members(m), ang:s*2*Math.PI/ax.order };
  });
  const base = 1/(recNatural() ? recTps : liveTps);
  anim = { items, ax, el:0, dur: base*(1+0.45*(maxAbs-1)) };
}
function animFrame(t){
  flushDirty();
  const e=ease(t);
  for (const it of anim.items){
    _q.setFromAxisAngle(anim.ax.v, it.ang*e);
    for (const id of it.mem){ _q2.multiplyQuaternions(_q, P.pieces[id].q); showPiece(id,_q2); }
  }
}
function finishAnim(){ for (const it of anim.items) applyState(it.m, it.mem); anim=null; playNatureCue(); }

function step(dt){
  const animated = recNatural() || liveTps<=40;
  if (anim && !animated) finishAnim();
  if (animated){
    let budget=dt, guard=0;
    while (guard++ < 5000){
      if (!anim){ if (qi<queue.length) startAnim(); else break; }
      const need=anim.dur-anim.el;
      if (budget>=need){ budget-=need; finishAnim(); continue; }
      anim.el+=budget; animFrame(anim.el/anim.dur); break;
    }
  } else if (qi<queue.length){
    accum += dt*liveTps;
    let n=Math.min(Math.floor(accum), queue.length-qi); accum-=Math.floor(accum);
    while (n-- > 0) applyState(queue[qi++]);
  }
  if (queueActive && qi>=queue.length && !anim){
    queueActive=false; queue=[]; qi=0; accum=0;
    const cb=onDone; onDone=null; cb && cb(true);
  }
}
function runMoves(list){
  return new Promise(res=>{
    queue=list; qi=0; accum=0; runTotal=list.length;
    if (!list.length){ res(true); return; }
    queueActive=true; onDone=res;
  });
}
function stopAll(){
  if (anim) finishAnim();
  queue=[]; qi=0; accum=0; phase='';
  if (queueActive){ queueActive=false; const cb=onDone; onDone=null; cb && cb(false); }
  seqToken++;
}

/* ---------------- High-level actions ---------------- */
function newPuzzle(){
  stopAll();
  const spec=readSpec();
  build(spec);
  for (const m of genScramble(clampInt($('scrN').value,1,50000))) applyState(m);
  flushDirty();
  if ($('autoSolve').checked){ const tok=seqToken; setTimeout(()=>{ if (tok===seqToken) solve(); }, 1000); }
}
function resetSolved(){ stopAll(); build(readSpecCurrent()); }
function readSpecCurrent(){ return JSON.parse(lastSpecKey); }

async function scramble(){
  stopAll(); phase='Scrambling';
  await runMoves(genScramble(clampInt($('scrN').value,1,50000)));
  phase='';
}
async function solve(){
  stopAll(); const tok=seqToken;
  const moves=solveMoves();
  if (!moves.length){ history=[]; toast('Already solved'); return; }
  let auto=false;
  if ($('autoRec').checked && !recorder){ startRec(); auto=true; await wait(600); }
  if (tok!==seqToken){ if (auto) stopRec(); return; }
  phase='Solving';
  const ok=await runMoves(moves);
  if (ok){ history=[]; phase=''; }
  if (auto){ if (ok) await wait(1500); stopRec(); }
}
async function recordAll(){
  stopAll(); if (recorder) stopRec();
  build(readSpecCurrent());
  const tok=seqToken;
  startRec();
  const abort=()=>{ phase=''; stopRec(); };
  await wait(800); if (tok!==seqToken) return abort();
  phase='Scrambling';
  if (!await runMoves(genScramble(clampInt($('scrN').value,1,50000)))) return abort();
  phase=''; await wait(600); if (tok!==seqToken) return abort();
  phase='Solving';
  if (!await runMoves(solveMoves())) return abort();
  history=[]; phase='';
  await wait(1500);
  stopRec();
}

/* ---------------- Recording ---------------- */
function pickMime(){
  for (const t of ['video/webm;codecs=vp9','video/webm;codecs=vp8','video/webm','video/mp4;codecs=avc1','video/mp4'])
    if (window.MediaRecorder && MediaRecorder.isTypeSupported(t)) return t;
  return '';
}
function startRec(){
  if (recorder) return;
  if (!window.MediaRecorder || !renderer.domElement.captureStream){ toast('Recording is not supported in this browser'); return; }
  const stream=renderer.domElement.captureStream(60), mime=pickMime(), chunks=[];
  const r=new MediaRecorder(stream, mime ? { mimeType:mime, videoBitsPerSecond:12e6 } : { videoBitsPerSecond:12e6 });
  r.ondataavailable=e=>{ if (e.data && e.data.size) chunks.push(e.data); };
  const slug=P.slug;
  r.onstop=()=>{
    const type=r.mimeType||mime||'video/webm', ext=type.includes('mp4')?'mp4':'webm';
    const blob=new Blob(chunks,{ type }), url=URL.createObjectURL(blob), a=document.createElement('a');
    a.href=url; a.download=`${slug}-${new Date().toISOString().replace(/[:.]/g,'-')}.${ext}`;
    document.body.appendChild(a); a.click(); a.remove();
    setTimeout(()=>URL.revokeObjectURL(url),15000);
    stream.getTracks().forEach(t=>t.stop());
    toast('Video saved: '+a.download);
  };
  r.start(250); recorder=r; recStart=performance.now();
  $('rec').style.display='block'; $('btnRec').textContent='⏹ Stop & Save Video'; $('btnRec').classList.add('rec');
}
function stopRec(){
  if (!recorder) return;
  const r=recorder; recorder=null; r.stop();
  $('rec').style.display='none'; $('btnRec').textContent='⏺ Start Recording'; $('btnRec').classList.remove('rec');
}

/* ---------------- UI wiring ---------------- */
let toastT=0;
function toast(msg){ const t=$('toast'); t.textContent=msg; t.style.display='block'; clearTimeout(toastT); toastT=setTimeout(()=>t.style.display='none',3000); }

function showSizeRows(){
  const t=$('ptype').value;
  $('sizeCube').style.display = t==='cube'?'flex':'none';
  $('sizeCuboid').style.display = t==='cuboid'?'flex':'none';
  $('sizePyra').style.display = t==='pyraminx'?'flex':'none';
}
function specChanged(){ $('scrN').value=defaultScramble(readSpec()); newPuzzle(); }
$('ptype').addEventListener('change',()=>{ showSizeRows(); specChanged(); });
$('nRange').addEventListener('input',()=>{ $('nNum').value=$('nRange').value; });
$('nRange').addEventListener('change',specChanged);
$('nNum').addEventListener('change',()=>{ $('nNum').value=clampInt($('nNum').value,2,50); $('nRange').value=$('nNum').value; specChanged(); });
['dimA','dimB','dimC'].forEach(id=>$(id).addEventListener('change',()=>{ $(id).value=clampInt($(id).value,1,30); specChanged(); }));
$('pyRange').addEventListener('input',()=>{ $('pyVal').textContent=$('pyRange').value; });
$('pyRange').addEventListener('change',specChanged);

const s2t=s=>Math.max(1,Math.min(10000,Math.round(Math.pow(10,s/250))));
const t2s=t=>Math.round(Math.log10(t)*250);
function setSpeed(t){ liveTps=clampInt(t,1,10000); $('spdNum').value=liveTps; $('spdRange').value=t2s(liveTps); $('spdLbl').textContent=liveTps.toLocaleString(); }
$('spdRange').addEventListener('input',()=>setSpeed(s2t(+$('spdRange').value)));
$('spdNum').addEventListener('change',()=>setSpeed($('spdNum').value));
for (const q of [2,10,30,100,1000,10000]){ const b=document.createElement('button'); b.textContent=q.toLocaleString(); b.onclick=()=>setSpeed(q); $('quick').appendChild(b); }
$('recSpd').addEventListener('input',()=>{ recTps=+$('recSpd').value; $('recSpdLbl').textContent=recTps; });
$('nature').addEventListener('change', e => e.target.checked ? (ensureAudio(), startNature()) : stopNature());
$('natureVol').addEventListener('input', e => { if(audio) audio.master.gain.value=+e.target.value/100; });
document.addEventListener('pointerdown', ensureAudio);

$('btnNew').onclick=newPuzzle;
$('btnScramble').onclick=scramble;
$('btnSolve').onclick=solve;
$('btnReset').onclick=resetSolved;
$('btnStop').onclick=()=>{ stopAll(); toast('Stopped'); };
$('btnRec').onclick=()=>{ recorder ? stopRec() : startRec(); };
$('btnRecAll').onclick=recordAll;

/* ---------------- Main loop ---------------- */
let last=performance.now(), statT=0, solvedCache=true;
function updateStatus(){
  solvedCache=isSolved();
  const rn=recNatural();
  const mode = rn ? `natural motion · ${recTps}/s (recording)` : liveTps<=40 ? `smooth · ${liveTps}/s` : `fast jumps · ${liveTps.toLocaleString()}/s`;
  const prog = queueActive ? ` ${Math.min(qi,runTotal).toLocaleString()}/${runTotal.toLocaleString()}` : '';
  $('status').innerHTML =
    `<h2>Status</h2><div><b>${P.name}</b></div>
     <div>State: ${solvedCache?'<b style="color:#5be37d">Solved ✓</b>':'<b style="color:#ffb347">Scrambled</b>'}</div>
     <div>Activity: ${phase?phase+prog:'Idle'}</div>
     <div>Mode: ${mode}</div>
     <div class="small">Moves in history: ${history.length.toLocaleString()}</div>`;
  $('hud').textContent = `${P.name} — ${phase ? phase+prog : (solvedCache?'Solved ✓':'Scrambled')}`;
}
function loop(now){
  requestAnimationFrame(loop);
  let dt=(now-last)/1000; last=now;
  dt = recNatural() ? Math.min(dt,1/30) : Math.min(dt,0.25);
  if (P){
    step(dt);
    flushDirty();
    if (needInst && P.kind==='lattice'){ P.bodyMesh.instanceMatrix.needsUpdate=true; P.stkMesh.instanceMatrix.needsUpdate=true; }
    needInst=false;
    const cine = !!recorder && $('cine').checked;
    controls.autoRotate = cine || $('autoRot').checked;
    controls.autoRotateSpeed = cine ? 0.7 : 1.0;
    controls.update(dt);
    if (now-statT>250){ statT=now; updateStatus(); }
    if (recorder){ const s=Math.floor((now-recStart)/1000); $('recTime').textContent=String(Math.floor(s/60)).padStart(2,'0')+':'+String(s%60).padStart(2,'0'); }
  }
  renderer.render(scene,camera);
}

resize();
showSizeRows();
setSpeed(6);
$('scrN').value=defaultScramble(readSpec());
newPuzzle();
requestAnimationFrame(loop);
