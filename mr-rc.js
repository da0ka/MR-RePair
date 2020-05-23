/*****************************************
	MR-RePair(range coder) 2019.9.10
******************************************
Re-Pair is the name of the algorithm and the software which implements the recursive pairing algorithm. Its corresponding decompressor is Des-Pair.

 usage:
	rcEnc(A,cut)
	@A	:圧縮元配列	{n|0..255}
	@cut:初走査の時3連長をどうするか
		0:無視, 1:2文字目省略, 2:1文字目省略
	返値	:圧縮配列	{n|0..255}

	rcDec(A)
	@A	:圧縮配列	{n|0..255}
	返値	:復号配列	{n|0..255}
******************************************/
function rcEnc(A,cut){
	function eb(i,b,P){
		var p=(P[i]||(P[i]=0x80000000))>>>9,r=(x>>>12)*(p>>11||1);
		b?x=r:(x-=r,y+=r);
		for(P[i]+=((b<<23)-p)*Y[r=P[i]&127]&-128|r<127;x<16777216;x*=256){
			if((y^0xff000000)>>>0>0xffffff){
				O[o++]=B+(r=y/0x100000000)&255;
				for(r+=255;N;N--)O[o++]=r&255;
				B=y>>>24}
			else++N;
			y=y<<8>>>0}
	}
	function eb2(i,s,P){
		for(;i;)eb(--i,s>>i&1,P)
	}
	function eb3(i,s,P){
		for(var b,c=1;i;c+=c+b)eb(c,b=s>>--i&1,P)
	}
	function eB(i,s,r){
		for(;i;){r=x>>>=1;
			if(s>>>--i&1)y+=r;
			for(;x<16777216;x*=256){
				if((y^0xff000000)>>>0>0xffffff){
					O[o++]=B+(r=y/0x100000000)&255;
					for(r+=255;N;N--)O[o++]=r&255;
					B=y>>>24}
				else++N;
				y=y<<8>>>0}
		}
	}
	function rw(c,r,s,n){
		if(T[c]>=0){d++;
			for(e++;nc>>nl;)nl++;
			if(c>=cs)c=T[c];eb(f,f=1,F);
			if(c<(n=(1<<nl)-nc))eb3(nl-1,c,E);
			else c+=n,eb3(nl-1,c>>1,E),eB(1,c&1)
		}else{e--;s=S[c];r=0;
			for(n=s.length-1;rw(s[r]),r++<n;);
			eb(f,0,F);
			if(d<3)f=4;
			else if(d<4)eb(f+6,n>1,F),f=5;
			else{f=r=0;
				for(s=n;s>>=1;)eb(r++,0,G);
				r<l2b(d-1)&&eb(r,1,G);
				n>1&&eb2(r,n,L[r])
			}d-=n;T[c]=nc++
		}
	}
	for(var d,e=A.length,f=32,m=1/0,n=e,x=-1>>>0,y=128,B=0,o=e,cs=0,nc,nl=0,C=Array(n),P=Array(n),N=Array(n),O=[],H=[],Q=[],S=[],T=[],E=[],F=[],G=[],L=[],Y=[];y;)Y[--y]=4096/(y+96)|0;
	if(!n)return O;
	for(;f;)L[--f]=[];
	for(Q.max=Math.sqrt(n)+.5|0;n--;N[n]=P[n]=m)E[A[n]]=1;
	for(Q.pairs=H[primes[H.hN=15]-1]=0;++n<256;)if(E[n])E[n]=cs++;
	for(m=n=nc=cs;o--;)C[o]=E[A[o]];
	for(;T[--m]=m;);
	for(initRDS(H,Q,C,P,N,cut&3);m=getMaxPair(Q);f?++n:--S.length)
		findMR(Q,C,P,N,m),
		addMRrule(S,C,P,m,n),
		e-=f=replaceMR(H,Q,C,P,N,m,n);
	f=Q=H=N=0;
	eB(5,d=l2b(e)+1);eB(--d,e^1<<d);eB(1,E[d=0]>-1);
	for(m=e;n=d<256;eB(e*2-1,n)){
		for(e=E[d]>-1;e==E[++d]>-1&&d<256;n++);
		if(n<256)e=l2b(+n)+1;else e=5,n=0}
	for(n=E.length=0;m;)if(~C[n])d=e=0,rw(C[n++]),eb(f,0,F),f=e<2?2:3,m--;else n=P[n];
	for(n=5;n--;y=y<<8>>>0)
		if((y^0xff000000)>>>0>0xffffff){
			O[o++]=B+(m=y/0x100000000)&255;
			for(m+=255;N;N--)O[o++]=m&255;
			B=y>>>24}
		else++N;
	return O}

function rcDec(A){
 function dB(i,c,b){
	for(c=0;i--;c+=c-b){
		x>>>=1;b=y-x>>>31;
		for(y-=x&--b;x<16777216;x*=256)y=(y<<8|A[a++])>>>0}
	return c}

 function db(P,c){
	var p=(P[c]||(P[c]=0x80000000))>>>9,r=(x>>>12)*(p>>11||1),b=1;
	y<r?x=r:(x-=r,y-=r,b=0);
	for(P[c]+=((b<<23)-p)*Y[r=P[c]&127]&-128|r<127;x<16777216;x*=256)y=(y<<8|A[a++])>>>0;
	return b}

 function db2(P,i,c){
	for(;i--;)c|=db(P,i)<<i;return c}

 function db3(P,i,c,d){
	for(c=1,d=i;i--;)c+=c+db(P,c);return c^1<<d}

 for(var a=0,c,d,e=128,f=32,l,m,n=0,o,r,s,x=-1>>>0,y,z,O=[],E=[],F=[],G=[],L=[],R=[],S=[],T=[],Y=[];a<4;)y=(y<<8|A[a++])>>>0;
 for(c=dB(5)-1;e;)Y[--e]=4096/(e+96)|0;
 if(c<0)return O;
 for(z=dB(c)|1<<c,l=dB(1);e<256;l^=1){
	for(o=0;o<9&&!dB(1);)o++;
	for(o=o<9?1<<o|dB(o):256;o--;e++)if(l)T[n++]=e}
 if(!n){for(;++o<z;)O[o]=dB(8);return O}
 for(;f;)L[--f]=[];

 O.e=function(R,s,r){
	if(s<m)return this[++o]=T[s];
	for(r=R[s],s=r.length;s;)this.e(R,r[--s])};

 for(m=n;z--;)
	for(e=s=0;;)
	 if(db(F,f)){f=1;
		for(e++;n>>l;)l++;
		if((c=db3(E,l-1))>=(d=(1<<l)-n))c+=c+dB(1)-d;
		O.e(R,S[s++]=c)}
	 else{
		if(!--e){f=2;break}
		if(s<2){f=3;break}r=R[n]=[];
		if(s<3)c=1,f=4;
		else if(s<4)c=1+db(F,f+6),f=5;
		else{for(c=f=0,d=l2b(s-1);c<d&&!db(G,c);)c++;c=1<<c|db2(L[c],c)}
		for(d=0;r[d++]=S[--s],c--;);S[s++]=n++}
 delete O.e;return O}