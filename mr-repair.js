/*****************************************
	MR-RePair 2019.9.8
******************************************
A variation of RePair algorithm using maximal repeats.
This program is based on Satoshi Yoshida's RePair implementation.
Yoshida's implementation is originaly come from Shirou Maruyama's RePair implementation.
This is used for the experiments appered in the paper of DCC2019, entitled
"MR-RePair: Grammar Compression based on Maximal Repeats".
Please refer the paper for the datail, and main.c for the copyright and usage.
******************************************/
var primes=function(a,b){for(;b;)a[--b]+=8<<b;return a}([3,3,5,3,3,27,9,9,5,3,27,43,3,45,29,3,21,7,17,15,9,43,35,15,29,3,11,85],28),log2=function(A,a){for(;a<255;)A[++a]=A[a>>1]+1;return A}([0],0);
function l2b(x,l){l=-1;
	if(x>255){l+=8,x>>=8;
	if(x>255){l+=8,x>>=8;
	if(x>255){l+=8,x>>=8}}}
	return l+log2[x]
}
function buildHash(H,Q){
 var h,i=H.length=0,p,n=H.length=primes[++H.hN];
 do for(p=Q[++i<Q.max?i:i=0];p;p=p.next)
	 p.link=H[h=(1+p.left)*(1+p.right)%n],H[h]=p;
 while(i)}

function locatePair(H,l,r){
 for(var p=H[(1+l)*(1+r)%H.length];p;p=p.link)
	if(p.left===l&&p.right===r)return p}

function insertPairPQ(Q,w,n,t){
 t=Q[n<Q.max?n:n=0];Q[n]=w;w.prev=0;
 if(w.next=t)t.prev=w}

function removePairPQ(Q,w,n){
 if(w.prev){
	if(w.prev.next=w.next)w.next.prev=w.prev;w.prev=0}
 else if(Q[n<Q.max?n:0]=w.next)w.next.prev=0;
 w.next=0}

function destructPair(H,Q,w){
 for(var h=(1+w.left)*(1+w.right)%H.length,p=H[h],q;p.left-w.left||p.right-w.right;p=p.link)q=p;
 q?q.link=p.link:H[h]=p.link;
 Q.pairs--}

function destructAllUniquePairs(H,Q,u,n){
	for(n=Q[1],Q[1]=0;u=n;destructPair(H,Q,u))
		n=u.next,removePairPQ(Q,u,u.freq)}

function leftPosSQ(C,N,p){return p?~C[--p]?p:N[p]:1/0}

function rightPosSQ(C,P,p){return++p<C.length?~C[p]?p:P[p]:1/0}

function incrementPair(Q,w){
 if(w.freq>=Q.max)return++w.freq;
 removePairPQ(Q,w,w.freq);
 insertPairPQ(Q,w,++w.freq)}

function decrementPairAtThePosition(H,Q,C,P,N,p,w){
	if(w=locatePair(H,C[p],C[~C[w=p+1]?w:P[w]])){
		if(w.top===p)w.top=N[p];
		if(w.pos===p)w.pos=P[p];
		p=--w.freq;
		if(p<Q.max)removePairPQ(Q,w,p+1),p?insertPairPQ(Q,w,p):destructPair(H,Q,w)
	}
}
function createPair(H,Q,l,r,p){
 var w={left:l,right:r,freq:1,top:p,pos:p};
 ++Q.pairs<H.length||buildHash(H,Q);
 insertPairPQ(Q,w,1);
 w.link=H[p=++l*++r%H.length];
 return H[p]=w}

function initRDS(H,Q,C,P,N,cut){
 for(var i=0,j,l=C.length-1,a,b,c=-1,w;i<l;i++,c=a)
	if(w=locatePair(H,a=C[i],b=C[i+1]))
	 N[P[i]=w.pos]=w.pos=i,
	 cut===1&&a===b&&a===c&&i-1===j||incrementPair(Q,w,j=i),
	 cut<2||a^b||a^c||i++;
	else createPair(H,Q,a,b,j=i);
 destructAllUniquePairs(H,Q)}

function getMaxPair(Q){
 var p=Q[0],mp,m=0;
 if(p){do if(m<p.freq)m=p.freq,mp=p;while(p=p.next)}
 else{for(p=Q.i||Q.max-1;p>1&&!(mp=Q[p]);)p--;Q.i=p}
 return mp}

function removeLinkSQ(P,N,p,u,n){
	n=N[p];p=P[p];p<u?n<u?P[N[p]=n]=p:N[p]=u:n<u&&(P[n]=u)}

function findMaximalRepeat(Q,C,P,N,mp){
	lm:for(var f=mp.top,e=mp.pos+1,p0=f,p1=rightPosSQ(C,P,f),ln=0,rn=0,i,p,d=0,c,u=1e99,v=C.length;p0;ln++){
		c=C[p=~C[p=p0-1]?p:N[p]];
		for(i=N[f];i<e;i=N[i])
			if(p=leftPosSQ(C,N,i-d),p>u||C[p]^c)break lm;
		~C[--p0]||(p0=N[p0]);d=f-p0
	}
	rm:for(d=p1-f;p1<v;rn++){
		c=C[p=~C[p=p1+1]?p:P[p]];
		for(i=N[f];i<e&&i+d<=v;i=N[i])
			if(p=rightPosSQ(C,P,i+d),p>u||C[p]^c)break rm;
		~C[++p1]||(p1=P[p1]);d=p1-f
	}
	if(ln+rn&&C[p0]===C[p1])
		if(rn)p1=leftPosSQ(C,N,p1),rn--;
		else p0=rightPosSQ(C,P,p0),ln--;
	mp.p0=p0,mp.p1=p1,mp.len=2+ln+rn}

function addMaximalRepeatAsNewRule(S,C,P,w,n){
	for(var i=0,p=w.p0,l=w.len,R=S[n]=[];i<l;p=~C[++p]?p:P[p])
		R[i++]=C[p];
}
function replaceMaximalRepeat(H,Q,C,P,N,mr,n){
	for(var a=mr.top,b,c,e=mr.pos,i,j,p,r=0,ld=a-mr.p0,rd=mr.p1-a,lp,rp,u=1/0,w;a<=e;a=p){
		i=b=a-ld;c=a+rd;p=N[a];
		if(p-ld<=c)p=N[p];
		lp=leftPosSQ(C,N,b);
		rp=rightPosSQ(C,P,c);
		if(lp<u)
			decrementPairAtThePosition(H,Q,C,P,N,lp),
			removeLinkSQ(P,N,lp,u);
		for(;i<c;i=j)
			j=rightPosSQ(C,P,i),
			decrementPairAtThePosition(H,Q,C,P,N,i),
			removeLinkSQ(P,N,i,u),
			C[i]=-1;
		if(rp<u)
			decrementPairAtThePosition(H,Q,C,P,N,c),
			removeLinkSQ(P,N,c,u);
		C[c]=-1;C[b]=n;
		if(rp<u)
			if(b+2^rp)P[b+1]=rp,N[b+1]=P[rp-1]=u,N[rp-1]=b;
			else P[c]=rp,N[c]=b;
		else if(a=C.length,b+2^a)
			P[b+1]=N[b+1]=P[a-1]=u,N[a-1]=b;
		else P[c]=u,N[c]=b;
		if(lp<u)
			if(w=locatePair(H,c=C[lp],n))
				incrementPair(Q,w),
				N[N[P[lp]=w.pos]=w.pos=lp]=u;
			else createPair(H,Q,c,n,lp),P[lp]=N[lp]=u;
		if(rp<u)
			if(w=locatePair(H,n,c=C[rp]))
				incrementPair(Q,w),
				N[N[P[b]=w.pos]=w.pos=b]=u;
			else createPair(H,Q,n,c,b),P[b]=N[b]=u;
		r+=mr.len-1
	}
	destructAllUniquePairs(H,Q);
	return r
}