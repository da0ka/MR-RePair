/*****************************************
	MR-RePair(CBT coder) 2020.7.17
******************************************
Re-Pair is the name of the algorithm and the software which implements the recursive pairing algorithm. Its corresponding decompressor is Des-Pair.
this version implemented CBT coding.

 usage:
	cbtEnc(A,cut)
	@A	:圧縮元配列	{n|0..255}
	@cut:初走査の時3連長をどうするか
		0:無視, 1:2文字目省略, 2:1文字目省略
	返値	:圧縮配列	{n|0..255}

	cbtDec(A)
	@A	:圧縮配列	{n|0..255}
	返値	:復号配列	{n|0..255}
******************************************/
function cbtEnc(A,cut){
	function rw(c,r,s,n,u){
		if(T[c]>=0){
			for(e++;nc>>nl;)nl++;
			if(c>=cs)c=T[c];
			if(c<(n=(1<<nl)-nc))s=nl-1;
			else s=nl,c+=n;
			O.e(s+1,1<<s|c)
		}else{s=S[c];r=0;
			for(n=u=s.length-1;rw(s[r++]),u--;);
			if(e<3)O.e(1,0);
			else if(e<4)O.e(2,n>1);
			else u=s=l2b(n),(r=u>=l2b(e-1))||u++,O.e(++s*2-r,n^r<<u);
			e-=n;T[c]=nc++
		}
	}
	var b=32,B,e=A.length,l,m=1/0,n=e,z=e,cs=0,nc,nl=0,o=n,H=[],C=Array(n),P=Array(n),N=Array(n),S=[],O=[],Q=[],T=[];
	if(!n)return done([0,0,0],0,3);
	O.e=function(l,n){
		if(b>l)return B|=n<<(b-=l);
		b=32-(l-=b);
		this[o++]=(B|=n>>l)>>>24;this[o++]=B>>16&255;this[o++]=B>>8&255;this[o++]=B&255;
		if(b<32)return B=n<<b;B=0};
	for(Q.max=Math.sqrt(n)+.5|0;n--;N[n]=P[n]=m)T[A[n]]=1;
	for(Q.pairs=H[primes[H.hN=15]-1]=0;++n<256;)if(T[n])T[n]=cs++;
	for(n=nc=cs;o;)C[--o]=T[A[o]];
	for(initRDS(H,Q,C,P,N,cut&3);m=getMaxPair(Q);l?++n:--S.length)
		findMR(Q,C,P,N,m),
		addMRrule(S,C,P,m,n),
		e-=l=replaceMR(H,Q,C,P,N,m,n);
	O.e(1,T[H=N=Q=n=0]>-1);O.e(5,l=l2b(e)+1);
	for(O.e(--l,e^1<<l);l=n<256;O.e(m*2-1,l)){
		for(m=T[n]>-1;m==T[++n]>-1&&n<256;l++);
		if(l<256)m=l2b(+l)+1;else m=5,l=0}
	for(n=T.length=cs;T[--n]=n;);
	for(m=e;m;)if(~C[n])e=0,rw(C[n++]),O.e(1,0),m--;else n=P[n];
	if(b<32)for(;B;B<<=8)O[o++]=B>>>24;
	if(o>z){
		for(m=n=o=B=O.length=0,b=32;z>>++m;);
		for(O.e(6,m),O.e(--m+9,(z^1<<m)<<9);n<z;)O.e(8,A[n++])
		if(b<32)for(;B;B<<=8)O[o++]=B>>>24
	}
	delete O.e;return O
}
function cbtDec(A){
	A.d=function(l,n){n=B>>>32-l;
		if(l<b){if(!l)return 0;B<<=l;b-=l;return n}
		l-=b;b=32-l;
		B=this[a++]<<24|this[a++]<<16|this[a++]<<8|this[a++];
		if(l)n|=B>>>b,B<<=l;
		return n};
	for(var a=0,b=0,B,l=A.d(1),c=A.d(5),d,e=0,z=c?A.d(--c)|1<<c:0,m,n=0,o,r,s,O=[],R=[],S=[],T=[];e<256;l^=1){
		for(o=0;o<9&&!A.d(1);++o);
		for(o=o<9?1<<o|A.d(o):256;o--;e++)if(l)T[n++]=e}
	if(c<0)return O;
	if(!n){for(;++o<z;)O[o]=A.d(8);return rate(0,a,a),done(O,a,++o)}

	O.e=function(R,s,r){
		if(s<m)return this[++o]=T[s];
		for(r=R[s],s=r.length;s;)this.e(R,r[--s])};

	for(m=n;z--;)
		for(e=s=0;;)
			if(A.d(1)){
				for(e++;n>>l;)l++;
				if((c=A.d(l-1))>=(d=(1<<l)-n))c+=c+A.d(1)-d;
				O.e(R,S[s++]=c)}
			else{
				if(!--e||s<2)break;
				if(s<3)c=1;
				else if(s<4)c=1+A.d(1);
				else{
						for(c=0,d=l2b(s-1);c<d&&!A.d(1);)c++;
						c=1<<c|A.d(c)
				}r=R[n]=[];
				for(d=0;r[d++]=S[--s],c--;);S[s++]=n++}
		delete O.e;delete A.d;
		return O
}
