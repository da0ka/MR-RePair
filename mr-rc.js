/*****************************************
	MR-RePair(range coder) 2022.5.21
******************************************
 usage:
	rcEnc(A,cut,done,rate)
	@A	:圧縮元配列	{n|0..255}
	@cut:初走査の時3連長をどうするか
		0:無視, 1:初走査のみ2文字目省略, 2:置換回数が合わないなら再計算
	@done:call back for last process
	返値	:圧縮配列	{n|0..255}

	rcDec(A,done,rate)
	@A	:圧縮配列	{n|0..255}
	@done:call back for last process
	返値	:復号配列	{n|0..255}
******************************************/
function rcEnc(A,cut,done,rate){
	function eb(i,b,P){
		var p=(P[i]||(P[i]=0x80000000))>>>9,r=(x>>>12)*(p>>11||1);
		b?x=r:(x-=r,y+=r);
		for(P[i]+=((b<<23)-p)*Y[r=P[i]&127]&-128|r<127;x<16777216;x*=256,y=y<<8>>>0)
			if(255>y>>>24)
				for(r=0xffffffff<y,O[o++]=255&r+B,B=y>>>24,r+=255;N;N--)O[o++]=255&r;
			else++N
	}
	function eb2(i,s,P){
		for(;i;)eb(--i,s>>i&1,P)
	}
	function eb3(i,s,P){
		for(var b,c=1;i;c+=c+b)eb(c,b=s>>--i&1,P)
	}
	function eB(i,s,r){
		for(;i;)for(y+=(x>>>=1)*(s>>>--i&1);x<16777216;x*=256,y=y<<8>>>0)
			if(255>y>>>24)
				for(r=0xffffffff<y,O[o++]=255&r+B,B=y>>>24,r+=255;N;N--)O[o++]=255&r;
			else++N
	}
	function rw(c,r,s,n){
		if(T[c]>=0){
			for(d++;nc>>nl;)nl++;
			if(c>=cs)c=T[c];
			e++&&Q&&eb(f+4*(e<65?e-2:63),1,F);f=Q=1;
			if(c<(n=(1<<nl)-nc))eb3(nl-1,c,E);
			else c+=n,eb3(nl-1,c>>1,E),eB(1,c&1)
		}else{s=S[c];r=0;
			for(n=s.length-1;rw(s[r]),r++<n;);
			eb(f+4*(e--<64?e:63),0,F);
			if(d<3)f=2;
			else if(d<4)eb(f,n>1,H),f=3;
			else{f=r=0;
				for(s=n;s>>=1;)eb(r++,0,G);
				r<l2b(d-1)&&eb(r,1,G);
				r&&eb2(r,n,L[e<19?e-3:15])
			}d-=n;Q=T[c]=nc++
		}
	}
	done=done||function(O){return O};
	for(var d,e=A.length,f=16,m,n=e,x=-1>>>0,y=128,z=e,B=0,o=e,cs=0,nc,nl=0,C=new Int32Array(n),P=new Uint32Array(n),N=new Uint32Array(n),O=[],H=[],Q=[],S=[],T=[],E=[],F=[],G=[],L=[],Y=new Uint8Array(y);y;)Y[--y]=4096/(y+96);
	if(!n)return done(O,z,0);
	for(;f;)L[--f]=[];
	for(Q.max=0|Math.sqrt(C.size=n)+1;n--;N[n]=P[n]=z)E[A[n]]=1;
	for(Q.pairs=H[primes[H.hN=15]-1]=0;++n<256;)if(E[n])E[n]=cs++;
	for(m=n=nc=cs;o--;)C[o]=E[A[o]];
	for(initRDS(H,Q,C,P,N,cut&3);T[--m]=m;);
	for(;m=getMaxPair(Q);f?++n:--S.length)
		findMR(Q,C,P,N,m),
		addMRrule(S,C,P,m,n),
		e-=f=replaceMR(H,Q,C,P,N,m,n,cut);
	f=N=H.length=0;
	eB(5,d=l2b(e)+1);eB(--d,e^1<<d);eB(1,E[d=0]>-1);
	for(m=e;n=d<256;eB(e*2-1,n)){
		for(e=E[d]>-1;e==E[++d]>-1&&d<256;n++);
		if(n<256)e=l2b(+n)+1;else e=5,n=0}
	for(n=E.length=0;m;)if(~C[n])Q=d=e=0,rw(C[n++]),eb(f+4*(e<64?e-1:63),0,F),m--;else n=P[n];
	for(n=5;n--;y=y<<8>>>0)
		if(255>y>>>24)
			for(f=0xffffffff<y,O[o++]=255&f+B,B=y>>>24,f+=255;N;N--)O[o++]=255&f;
		else++N;
	return done(O,z,o)}

function rcDec(A,done,rate){
	function dB(i,c,b){
		for(c=0;i--;c+=c-b)
			for(x>>>=1,b=y-x>>>31,y-=x&--b;x<16777216;x*=256)y=(y<<8|A[a++])>>>0;
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

	if(!A.length)return done([],0,0);
	for(var a=0,c,d,e=128,f=16,h=1,l,m,n=0,o,r,s,x=-1>>>0,y,z,O=[],D=[],E=[],F=[],G=[],L=[],R=[],S=[],T=[],Y=new Uint8Array(e);a<4;)y=(y<<8|A[a++])>>>0;
	for(c=dB(5);e;)Y[--e]=4096/(e+96)|0;
	if(!c)return done(O,z,0);
	for(z=(dB(--c)|1<<c)>>>0,l=dB(1);e<256;l^=1){
		for(o=0;o<9&&!dB(1);)o++;
		for(o=o<9?1<<o|dB(o):256;o--;e++)if(l)T[n++]=e}
	if(!n){for(;++o<z;)O[o]=dB(8);return done(O,z,++o)}
	for(;f;)L[--f]=[];

	O.e=function(R,s,r){
		if(s<m)return this[++o]=T[s];
		for(r=R[s],s=r.length;s;)this.e(R,r[--s])};

	for(m=n;z--;)for(e=s=0;;)
		if(h||db(F,f+4*(e<64?e-1:63))){
			for(e++;n>>l;)l++;
			if((c=db3(E,l-1))>=(d=(1<<l)-n))c+=c+dB(1)-d;
			O.e(R,S[s++]=c);f=1;h=0}
		else{
			if(h=!--e||s<2)break;r=R[n]=[];
			if(c=s<3)f=2;
			else if(s<4)c=1+db(D,f),f=3;
			else{for(f=0,d=l2b(s-1);c<d&&!db(G,c);)c++;c=1<<c|db2(L[e<19?e-3:15],c)}
			for(d=0;r[d++]=S[--s],c--;);S[s++]=n++}
	delete O.e;
	return done(O,a,++o)}
