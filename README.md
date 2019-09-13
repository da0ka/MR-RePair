# MR-RePair
MR-RePair: a variation of RePair algorithm using maximal repeats

It based on https://github.com/tkida/MR-Repair
## functions
`cbtEnc(A,cut)/rcEnc(A,cut)`

cbtEnc using simple bit coder, rcEnc using binary range coder.

@A: Array/Uint8Array. It is uncompressed data

@cut: Number(0-2). It gives small effect for first pass.

@return: compressd `A`

`cbtDec(A)/rcDec(A)`

cbtDec using simple bit coder, rcDec using binary range coder.

@A: Array/Uint8Array. It is compressed data

@return: decompressd `A`

## usage
```
<script type="text/javascript" src="mr-repair.js"></script>
<script type="text/javascript" src="mr-cbt.js"></script>
<script type="text/javascript" src="mr-rc.js"></script>
<script>
var a=[1,2,3,1,2,3,1,2,3],  // input
b=cbtEnc(a),  // b is compressed `a`
c=cbtDec(b);  // c is decompressed `b`

b=rcEnc(a); // better compression for big data
c=rcDec(b); // decompression
</script>
```
