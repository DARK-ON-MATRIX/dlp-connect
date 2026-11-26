JavaScript

/* ---------- Generatore di codici QR (byte mode, correzione L/M, versioni 1-10), solo ES5 ---------- */
var QR=(function(){
  var ECC_PB={L:[0,7,10,15,20,26,18,20,24,30,18],M:[0,10,16,26,18,24,16,18,22,22,26]};
  var NBLK={L:[0,1,1,1,1,1,2,2,2,2,4],M:[0,1,1,1,2,2,4,4,4,5,5]};
  var FMT={L:1,M:0};
  function rawModules(v){var r=(16*v+128)*v+64;if(v>=2){var n=Math.floor(v/7)+2;r-=(25*n-10)*n-55;if(v>=7)r-=36}return r}
  function dataCw(v,e){return Math.floor(rawModules(v)/8)-ECC_PB[e][v]*NBLK[e][v]}
  function alignPos(v){
    if(v===1)return[];
    var n=Math.floor(v/7)+2,size=v*4+17,step=Math.ceil((v*4+4)/(n*2-2))*2,r=[6],p;
    for(p=size-7;r.length<n;p-=step)r.splice(1,0,p);
    return r;
  }
  function rsMul(x,y){var z=0,i;for(i=7;i>=0;i--){z=(z<<1)^((z>>>7)*0x11D);z^=((y>>>i)&1)*x}return z}
  function rsDiv(deg){
    var r=[],i,j,root=1;
    for(i=0;i<deg-1;i++)r.push(0);r.push(1);
    for(i=0;i<deg;i++){
      for(j=0;j<r.length;j++){r[j]=rsMul(r[j],root);if(j+1<r.length)r[j]^=r[j+1]}
      root=rsMul(root,2);
    }
    return r;
  }
  function rsRem(data,div){
    var r=[],i,k;
    for(i=0;i<div.length;i++)r.push(0);
    for(k=0;k<data.length;k++){
      var f=data[k]^r.shift();r.push(0);
      for(i=0;i<div.length;i++)r[i]^=rsMul(div[i],f);
    }
    return r;
  }
  function addEcc(data,v,e){
    var nb=NBLK[e][v],el=ECC_PB[e][v],raw=Math.floor(rawModules(v)/8),ns=nb-raw%nb,sl=Math.floor(raw/nb),
        blocks=[],div=rsDiv(el),i,k=0,j,res=[];
    for(i=0;i<nb;i++){
      var dat=data.slice(k,k+sl-el+(i<ns?0:1));k+=dat.length;
      var ecc=rsRem(dat,div);
      if(i<ns)dat.push(0);
      blocks.push(dat.concat(ecc));
    }
    for(i=0;i<blocks[0].length;i++){
      for(j=0;j<nb;j++){if(i!==sl-el||j>=ns)res.push(blocks[j][i])}
    }
    return res;
  }
  function utf8(s){var u=unescape(encodeURIComponent(s)),a=[],i;for(i=0;i<u.length;i++)a.push(u.charCodeAt(i));return a}
  function bit(x,i){return((x>>>i)&1)!==0}
  function encode(text,ecl){
    ecl=ecl==='L'?'L':'M';
    var bytes=utf8(text),v,ccb;
    for(v=1;v<=10;v++){ccb=v<10?8:16;if(4+ccb+bytes.length*8<=dataCw(v,ecl)*8)break}
    if(v>10)throw new Error('testo troppo lungo per il QR');
    var bits=[],i;
    function put(val,len){for(var b=len-1;b>=0;b--)bits.push((val>>>b)&1)}
    put(4,4);put(bytes.length,ccb);for(i=0;i<bytes.length;i++)put(bytes[i],8);
    var cap=dataCw(v,ecl)*8;
    put(0,Math.min(4,cap-bits.length));
    while(bits.length%8)bits.push(0);
    for(var pad=0xEC;bits.length<cap;pad^=0xEC^0x11)put(pad,8);
    var data=[];
    for(i=0;i<bits.length;i+=8){var by=0;for(var b=0;b<8;b++)by=(by<<1)|bits[i+b];data.push(by)}
    var cw=addEcc(data,v,ecl),size=v*4+17,m=[],fn=[],x,y;
    for(y=0;y<size;y++){m.push([]);fn.push([]);for(x=0;x<size;x++){m[y].push(false);fn[y].push(false)}}
    function setF(x,y,d){m[y][x]=d;fn[y][x]=true}
    for(i=0;i<size;i++){setF(6,i,i%2===0);setF(i,6,i%2===0)}
    function finder(cx,cy){
      for(var dy=-4;dy<=4;dy++)for(var dx=-4;dx<=4;dx++){
        var dist=Math.max(Math.abs(dx),Math.abs(dy)),xx=cx+dx,yy=cy+dy;
        if(xx>=0&&xx<size&&yy>=0&&yy<size)setF(xx,yy,dist!==2&&dist!==4);
      }
    }
    finder(3,3);finder(size-4,3);finder(3,size-4);
    var ap=alignPos(v),n=ap.length,a,b;
    for(a=0;a<n;a++)for(b=0;b<n;b++){
      if((a===0&&b===0)||(a===0&&b===n-1)||(a===n-1&&b===0))continue;
      for(var dy=-2;dy<=2;dy++)for(var dx=-2;dx<=2;dx++)setF(ap[a]+dx,ap[b]+dy,Math.max(Math.abs(dx),Math.abs(dy))!==1);
    }
    function formatBits(mask){
      var d=(FMT[ecl]<<3)|mask,r=d,k;
      for(k=0;k<10;k++)r=(r<<1)^((r>>>9)*0x537);
      var bt=((d<<10)|r)^0x5412;
      for(k=0;k<=5;k++)setF(8,k,bit(bt,k));
      setF(8,7,bit(bt,6));setF(8,8,bit(bt,7));setF(7,8,bit(bt,8));
      for(k=9;k<15;k++)setF(14-k,8,bit(bt,k));
      for(k=0;k<8;k++)setF(size-1-k,8,bit(bt,k));
      for(k=8;k<15;k++)setF(8,size-15+k,bit(bt,k));
      setF(8,size-8,true);
    }
    formatBits(0);
    if(v>=7){
      var rem=v,k;
      for(k=0;k<12;k++)rem=(rem<<1)^((rem>>>11)*0x1F25);
      var vb=(v<<12)|rem;
      for(k=0;k<18;k++){var q=bit(vb,k),aa=size-11+k%3,bb=Math.floor(k/3);setF(aa,bb,q);setF(bb,aa,q)}
    }
    var idx=0;
    for(var right=size-1;right>=1;right-=2){
      if(right===6)right=5;
      for(var vert=0;vert<size;vert++){
        for(var j=0;j<2;j++){
          var xx=right-j,up=((right+1)&2)===0,yy=up?size-1-vert:vert;
          if(!fn[yy][xx]&&idx<cw.length*8){m[yy][xx]=bit(cw[idx>>>3],7-(idx&7));idx++}
        }
      }
    }
    function maskFn(mk,x,y){
      switch(mk){
        case 0:return(x+y)%2===0;case 1:return y%2===0;case 2:return x%3===0;case 3:return(x+y)%3===0;
        case 4:return(Math.floor(x/3)+Math.floor(y/2))%2===0;case 5:return x*y%2+x*y%3===0;
        case 6:return(x*y%2+x*y%3)%2===0;default:return((x+y)%2+x*y%3)%2===0;
      }
    }
    function applyMask(mk){for(var yy=0;yy<size;yy++)for(var xx=0;xx<size;xx++)if(!fn[yy][xx]&&maskFn(mk,xx,yy))m[yy][xx]=!m[yy][xx]}
    function penalty(){
      var p=0,yy,xx,run,col,dark=0;
      for(yy=0;yy<size;yy++){
        for(var dir=0;dir<2;dir++){
          run=1;col=dir?m[0][yy]:m[yy][0];
          for(xx=1;xx<size;xx++){
            var c=dir?m[xx][yy]:m[yy][xx];
            if(c===col){run++;if(run===5)p+=3;else if(run>5)p++}else{col=c;run=1}
          }
        }
      }
      for(yy=0;yy<size-1;yy++)for(xx=0;xx<size-1;xx++){
        var c0=m[yy][xx];if(c0===m[yy][xx+1]&&c0===m[yy+1][xx]&&c0===m[yy+1][xx+1])p+=3;
      }
      var pa=[1,0,1,1,1,0,1,0,0,0,0],pb=[0,0,0,0,1,0,1,1,1,0,1];
      function same(arr,pat,s){for(var t=0;t<11;t++)if((arr[s+t]?1:0)!==pat[t])return false;return true}
      for(yy=0;yy<size;yy++){
        var row=m[yy],colA=[];for(xx=0;xx<size;xx++)colA.push(m[xx][yy]);
        for(xx=0;xx+11<=size;xx++){
          if(same(row,pa,xx)||same(row,pb,xx))p+=40;
          if(same(colA,pa,xx)||same(colA,pb,xx))p+=40;
        }
      }
      for(yy=0;yy<size;yy++)for(xx=0;xx<size;xx++)if(m[yy][xx])dark++;
      p+=Math.floor(Math.abs(dark*20-size*size*10)/(size*size))*10;
      return p;
    }
    var best=0,bestP=1e9,mk;
    for(mk=0;mk<8;mk++){
      applyMask(mk);formatBits(mk);
      var pp=penalty();if(pp<bestP){bestP=pp;best=mk}
      applyMask(mk);
    }
    applyMask(best);formatBits(best);
    return{size:size,modules:m,version:v};
  }
  function draw(canvas,text,maxPx){
    var q=encode(text,'M'),quiet=4,total=q.size+quiet*2,sc=Math.max(2,Math.floor(maxPx/total)),px=sc*total,
        ctx=canvas.getContext('2d'),x,y;
    canvas.width=px;canvas.height=px;
    ctx.fillStyle='#fff';ctx.fillRect(0,0,px,px);
    ctx.fillStyle='#000';
    for(y=0;y<q.size;y++)for(x=0;x<q.size;x++)if(q.modules[y][x])ctx.fillRect((x+quiet)*sc,(y+quiet)*sc,sc,sc);
    return q;
  }
  return{encode:encode,draw:draw};
})();
