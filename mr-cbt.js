/*****************************************
	MR-RePair(CBT coder) 2022.5.21
******************************************
 usage:
	cbtEnc(A,done,rate,cut)
	@A	:圧縮元配列	{n|0..255}
	@cut:3連長をどうするか
		0:無視, 1:初走査のみ2文字目省略, 2:置換回数が合わないなら再計算
	@done:call back for last process
	返値	:圧縮配列	{n|0..255}

	cbtDec(A,done,rate)
	@A	:圧縮配列	{n|0..255}
	@done:call back for last process
	返値	:復号配列	{n|0..255}
******************************************/
function cbtEnc(A,cut,done,rate){
	function rw(c,r,s,n,u){
		if(T[c]>=0){
			for(e++||(N=0);nc>>nl;)nl++;
			if(c>=cs)c=T[c];
			if(c<(n=(1<<nl)-nc))s=nl-1;
			else s=nl,c+=n;
			O.e(s+N,N<<s|c);N=1
		}else{s=S[c];r=0;
			for(n=u=s.length-1;rw(s[r++]),u--;);
			if(e<3)O.e(1,0);
			else if(e<4)O.e(2,n>1);
			else u=s=l2b(n),(r=u>=l2b(e-1))||u++,O.e(++s*2-r,n^r<<u);
			e-=n;T[c]=nc++;N=1
		}
	}
	done=done||function(O){return O};
	var b=32,B,e=A.length,l,m=1/0,n=e,z=e,cs=0,nc,nl=0,o=n,H=[],C=new Int32Array(n),P=new Uint32Array(n),N=new Uint32Array(n),S=[],O=[],Q=[],T=[];
	if(!n)return done([0,0,0],0,3);
	O.e=function(l,n){
		if(b>l)return B|=n<<(b-=l);
		b=32-(l-=b);
		this[o++]=(B|=n>>l)>>>24;this[o++]=B>>16&255;this[o++]=B>>8&255;this[o++]=B&255;
		if(b<32)return B=n<<b;B=0};
	for(Q.max=0|Math.sqrt(C.size=n)+1;n--;N[n]=P[n]=z)T[A[n]]=1;
	for(Q.pairs=H[primes[H.hN=15]-1]=0;++n<256;)if(T[n])T[n]=cs++;
	for(n=nc=cs;o;)C[--o]=T[A[o]];
	for(initRDS(H,Q,C,P,N,cut&3);m=getMaxPair(Q);l?++n:--S.length)
		findMR(Q,C,P,N,m),
		addMRrule(S,C,P,m,n),
		e-=l=replaceMR(H,Q,C,P,N,m,n,cut);
	O.e(1,T[H=Q=n=0]>-1);O.e(5,l=l2b(e)+1);
	for(O.e(--l,e^1<<l);l=n<256;O.e(m*2-1,l)){
		for(m=T[n]>-1;m==T[++n]>-1&&n<256;l++);
		if(l<256)m=l2b(+l)+1;else m=5,l=0}
	for(n=T.length=cs;T[--n]=n;);
	for(m=e;m;)~C[n]?O.e(1,N=e=0,rw(C[n++],m--)):n=P[n];
	if(b<32)for(;B;B<<=8)O[o++]=B>>>24;
	if(o>z){
		for(m=n=o=B=O.length=0,b=32;z>>++m;);
		for(O.e(6,m),O.e(--m+9,(z^1<<m)<<9);n<z;)O.e(8,A[n++])
		if(b<32)for(;B;B<<=8)O[o++]=B>>>24
	}
	delete O.e;return rate(0,z,z),done(O,z,o)}

function cbtDec(A,done,rate){
	A.d=function(l,n){n=B>>>32-l;
		if(l<b){if(!l)return 0;B<<=l;b-=l;return n}
		l-=b;b=32-l;
		B=this[a++]<<24|this[a++]<<16|this[a++]<<8|this[a++];
		if(l)n|=B>>>b,B<<=l;
		return n};
	done=done||function(O){return O};
	for(var a=0,b=0,B,l=A.d(1),c=A.d(5),d=256,e=0,z=c?(A.d(--c)|1<<c)>>>0:0,m,n=0,o,r,s,u,O=[],R=[],S=[],T=[],U=[];e<d;l^=1){
		for(o=0,c=l2b(d-e);o<c&&!A.d(1);++o);
		for(o=o<8?1<<o|A.d(o):d;o--;e++)if(l)T[n++]=e}
	if(!z)return done(O,A.length,0);
	if(!n){for(;++o<z;)O[o]=A.d(8);return rate(0,a,a),done(O,a,++o)}
	for(m=n;z--;)for(s=0;;)
		if(!s||A.d(1)){
			for(;n>>l;)l++;
			if((c=A.d(l-1))>=(d=(1<<l)-n))c+=c+A.d(1)-d;
			for(S[s++]=c,u=0;;c=U[--u])
				if(c<m){O[++o]=T[c];if(!u)break}
				else for(r=R[c],c=r.length;c;)U[u++]=r[--c]}
		else{
			if(s<2)break;
			if(s<3)c=1;
			else if(s<4)c=1+A.d(1);
			else{
				for(c=0,d=l2b(s-1);c<d&&!A.d(1);)c++;
				c=1<<c|A.d(c)
			}for(r=R[n]=[];r[c]=S[--s],c--;);S[s++]=n++}
	delete A.d;
	return done(O,A.length,++o)}
