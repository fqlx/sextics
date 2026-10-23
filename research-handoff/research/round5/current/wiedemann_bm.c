#include <stdint.h>
#include <flint/nmod_poly.h>
long source_bm(const uint64_t *seq,long n,uint64_t p,uint64_t*out){
  nmod_berlekamp_massey_t B;
  nmod_berlekamp_massey_init(B,(ulong)p);
  nmod_berlekamp_massey_add_points(B,(const ulong*)seq,(slong)n);
  nmod_berlekamp_massey_reduce(B);
  const nmod_poly_struct *V=nmod_berlekamp_massey_V_poly(B);
  long len=V->length;
  for(long i=0;i<len;i++)out[i]=(uint64_t)V->coeffs[i];
  nmod_berlekamp_massey_clear(B);
  return len;
}
