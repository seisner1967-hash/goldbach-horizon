// SOURCE ONLY. Never compiled, linked or run. This is not a Lean certificate.
// Separate producer: DIT, common-denominator log32, trial-factor catalogue.
#include <gmp.h>
#include <array>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace producer22 {
constexpr uint32_t N = 100000000, K = 134217728;
constexpr uint64_t S = UINT64_C(288230376151711744), MAX_POINT = UINT64_C(1) << 63;
constexpr uint64_t OUTPUT_CAP = UINT64_C(2147483648);
constexpr size_t BIG_CAP = 4096;
static_assert(sizeof(uint32_t) == 4 && sizeof(uint64_t) == 8);
void need(bool b, const char* why) { if (!b) throw std::runtime_error(why); }
const auto start = std::chrono::steady_clock::now();
void deadline() {
  need(std::chrono::steady_clock::now() - start < std::chrono::seconds(3600),
       "RESOURCE_LIMIT_NO_VERDICT_WALL");
}
struct Z {
  mpz_t z;
  Z(uint64_t n = 0) { mpz_init(z); mpz_import(z, 1, -1, sizeof n, 0, 0, &n); }
  Z(const Z& a) { mpz_init_set(z, a.z); }
  Z(Z&& a) noexcept { mpz_init(z); mpz_swap(z, a.z); }
  Z& operator=(const Z& a) { if (this != &a) mpz_set(z, a.z); return *this; }
  Z& operator=(Z&& a) noexcept { mpz_swap(z, a.z); return *this; }
  ~Z() { mpz_clear(z); }
  void cap(size_t b = BIG_CAP) const { need(mpz_sizeinbase(z, 2) <= b, "INTEGER_WORKSPACE_OVERFLOW"); }
  uint64_t u64() const {
    need(mpz_sgn(z) >= 0 && mpz_sizeinbase(z, 2) <= 64, "U64_EXPORT_OVERFLOW");
    uint64_t out = 0; size_t count = 0;
    mpz_export(&out, &count, -1, sizeof out, 0, 0, z);
    need(count <= 1, "U64_EXPORT_COUNT"); return out;
  }
};
Z operator+(const Z& a, const Z& b) { Z r; mpz_add(r.z,a.z,b.z); r.cap(); return r; }
Z operator-(const Z& a, const Z& b) { Z r; mpz_sub(r.z,a.z,b.z); r.cap(); return r; }
Z operator*(const Z& a, const Z& b) { Z r; mpz_mul(r.z,a.z,b.z); r.cap(); return r; }
bool operator<(const Z& a, const Z& b) { return mpz_cmp(a.z,b.z)<0; }
bool operator==(const Z& a, const Z& b) { return mpz_cmp(a.z,b.z)==0; }
bool operator<=(const Z& a, const Z& b) { return mpz_cmp(a.z,b.z)<=0; }
Z power(uint64_t a, unsigned e) { Z b(a), r; mpz_pow_ui(r.z,b.z,e); r.cap(); return r; }
Z absz(const Z& a) { Z r; mpz_abs(r.z,a.z); r.cap(); return r; }
Z div_exact(const Z& a, const Z& b) {
  need(mpz_sgn(b.z)>0 && mpz_divisible_p(a.z,b.z), "INEXACT_OR_ZERO_DIVISION");
  Z r; mpz_divexact(r.z,a.z,b.z); r.cap(); return r;
}
uint32_t mod32(const Z& a, uint32_t p) {
  need(p>1, "INVALID_MODULUS"); return static_cast<uint32_t>(mpz_fdiv_ui(a.z,p));
}
uint32_t mulmod(uint32_t a, uint32_t b, uint32_t p) {
  need(a<p && b<p, "NONCANONICAL_MOD_OPERAND");
  return static_cast<uint32_t>((uint64_t(a)*b)%p);
}
uint32_t powmod(uint32_t a, uint32_t e, uint32_t p) {
  need(p>1, "POW_MODULUS"); uint32_t r=1; a%=p;
  while(e) { if(e&1) r=mulmod(r,a,p); e>>=1; if(e) a=mulmod(a,a,p); }
  return r;
}
uint32_t inverse(uint32_t a, uint32_t p) {
  need(a>0 && a<p, "INVERSE_DOMAIN"); Z aa(a), pp(p), r;
  need(mpz_invert(r.z,aa.z,pp.z)!=0, "NONUNIT_DIVISION"); r.cap(32);
  auto v=static_cast<uint32_t>(r.u64()); need(mulmod(a,v,p)==1,"INVERSE_PRODUCT"); return v;
}
struct Mod { uint32_t p,c,g,w,wi,ki; };
std::array<Mod,5> constants() {
  std::array<Mod,5> rows{{{2013265921,15,31,0,0,0},{2281701377,17,3,0,0,0},
    {3221225473,24,5,0,0,0},{3489660929,26,3,0,0,0},{3892314113,29,3,0,0,0}}};
  Z product(1);
  for(size_t i=0;i<rows.size();++i) {
    auto& r=rows[i]; need(uint64_t(r.c)*K+1==r.p && (r.p&1),"PARAMETER_FORM");
    for(size_t j=0;j<i;++j) need(r.p!=rows[j].p,"DUPLICATE_MODULUS");
    for(uint32_t d=2;uint64_t(d)*d<=r.p;++d) {
      need(r.p%d!=0,"INVALID_MODULAR_PARAMETER_COMPOSITE"); if(!(d&4095)) deadline();
    }
    r.w=powmod(r.g,r.c,r.p);
    need(r.w>0 && powmod(r.w,K,r.p)==1 && powmod(r.w,K/2,r.p)!=1,"ROOT_ORDER_FAILED");
    r.wi=inverse(r.w,r.p); r.ki=inverse(K,r.p); product=product*Z(r.p);
  }
  need(power(2,154)<product,"CRT_COVERAGE");
  need(Z(N+1)*Z(MAX_POINT)*Z(MAX_POINT)<power(2,153),"COEFFICIENT_BOUND");
  need(Z(2)*Z(N+1)*(Z(64)*Z(S)+Z(1))*Z(1000000)<=Z(S)*Z(S),"TAU_GUARD");
  return rows;
}
struct Box { Z lo,hi,d; };
std::pair<Z,Z> series32(uint32_t a, uint32_t d) {
  need(d>0 && uint64_t(3)*a<=d,"SERIES_DOMAIN"); Z H(1), numerator(0);
  for(unsigned j=0;j<32;++j) H=H*Z(2*j+1);
  Z denominator=power(d,63)*H;
  for(unsigned j=0;j<32;++j) {
    Z term=power(a,2*j+1)*power(d,62-2*j)*div_exact(H,Z(2*j+1));
    numerator=numerator+Z(2)*term;
  }
  return {numerator,denominator};
}
Box log32(uint32_t p) {
  need(2<=p && p<=N,"LOG_DOMAIN"); unsigned k=0;
  while((UINT32_C(1)<<(k+1))<=p) ++k;
  need(k<=26,"LOG_REDUCTION"); uint32_t v=UINT32_C(1)<<k;
  auto a=series32(p-v,p+v), b=series32(1,3);
  Z ln=Z(k)*b.first*a.second+a.first*b.second, ld=b.second*a.second;
  Z wn=Z(k+1)*Z(9), wd=Z(260)*power(3,65);
  Box box{ln*wd,ln*wd+wn*ld,ld*wd};
  need(Z(0)<=box.lo && box.lo<=box.hi && Z(0)<box.d,"LOG_BOX_ORDER");
  need((box.hi-box.lo)*Z(S)<box.d,"LOG_WIDTH"); return box;
}
uint64_t point32(uint32_t p) {
  Box b=log32(p); Z numerator=Z(S)*(b.lo+b.hi), den=Z(2)*b.d, q,r;
  mpz_fdiv_qr(q.z,r.z,numerator.z,den.z); q.cap(); r.cap();
  Z twice=Z(2)*r;
  if(den<twice || (twice==den && mpz_odd_p(q.z))) q=q+Z(1);
  if(q<Z(0)) q=Z(0); if(Z(MAX_POINT)<q) q=Z(MAX_POINT);
  need(absz(q*b.d-Z(S)*b.lo)<=b.d && absz(q*b.d-Z(S)*b.hi)<=b.d,
       "LOG_ENDPOINT_GUARD"); return q.u64();
}
uint64_t bytes_written=0;
void bytes(std::ofstream& f, const void* ptr, size_t n) {
  need(n<=OUTPUT_CAP-bytes_written,"RESOURCE_LIMIT_NO_VERDICT_OUTPUT");
  f.write(static_cast<const char*>(ptr),static_cast<std::streamsize>(n));
  need(bool(f),"OUTPUT_WRITE_FAILED"); bytes_written+=n;
}
void u32(std::ofstream& f,uint32_t v) {
  unsigned char b[4]; for(unsigned j=0;j<4;++j) b[j]=static_cast<unsigned char>(v>>(8*j)); bytes(f,b,4);
}
void u64(std::ofstream& f,uint64_t v) {
  unsigned char b[8]; for(unsigned j=0;j<8;++j) b[j]=static_cast<unsigned char>(v>>(8*j)); bytes(f,b,8);
}
std::vector<uint32_t> factors(uint32_t n, const std::vector<uint32_t>& cat) {
  std::vector<uint32_t> out;
  while(n>1) {
    uint32_t q=cat[n]; need(q>=2 && q<=n && n%q==0 && cat[q]==q,"LUCAS_FACTOR_COVERAGE");
    out.push_back(q); do { n/=q; } while(n%q==0);
    need(out.size()<=27,"LUCAS_FACTOR_COUNT");
  }
  return out;
}
bool lucas(uint32_t p, uint32_t g, const std::vector<uint32_t>& qs) {
  if(g==0 || g>=p || powmod(g,p-1,p)!=1) return false;
  for(auto q:qs) if(powmod(g,(p-1)/q,p)==1) return false;
  return true;
}
void catalogue(std::vector<uint32_t>& cat, std::vector<uint64_t>& points,
               const std::filesystem::path& dir) {
  std::ofstream cf(dir/"factors.bin",std::ios::binary), rf(dir/"records.bin",std::ios::binary);
  need(bool(cf)&&bool(rf),"OUTPUT_OPEN_FAILED");
  const char cm[8]={'G','B','C','A','T','2','2',0}, rm[8]={'G','B','R','E','C','2','2',0};
  bytes(cf,cm,8); u64(cf,N); bytes(rf,rm,8); u64(rf,N); u64(rf,0);
  u32(cf,0); u32(cf,0); uint64_t prime_count=0;
  for(uint32_t n=2;n<=N;++n) {
    if(!(n&4095)) deadline(); uint32_t p=n;
    // All divisions, no sieve or probable-prime catalogue.
    for(uint32_t d=2;uint64_t(d)*d<=n;++d) if(n%d==0) { p=d; break; }
    cat[n]=p; need(p>=2 && n%p==0 && (p==n || cat[p]==p),"GENERATED_FACTOR_INVALID");
    if(p==n) {
      auto qs=factors(n-1,cat); uint32_t g=(n==2?1:2);
      while(g<n && !lucas(n,g,qs)) { ++g; if(!(g&4095)) deadline(); }
      need(g<n && lucas(n,g,qs),"LUCAS_WITNESS_NOT_FOUND");
      points[n]=point32(n); u32(rf,n); u32(rf,g); u64(rf,points[n]); ++prime_count;
      need(prime_count<=N/2+1,"RECORD_COUNT_BOUND");
    } else {
      uint32_t rest=n; do { rest/=p; } while(rest%p==0);
      points[n]=(rest==1?points[p]:0);
    }
    u32(cf,p);
  }
  rf.seekp(16); need(bool(rf),"RECORD_COUNT_SEEK");
  // Count rewrite does not extend the payload; its eight bytes were accounted above.
  unsigned char c[8]; for(unsigned j=0;j<8;++j) c[j]=static_cast<unsigned char>(prime_count>>(8*j));
  rf.write(reinterpret_cast<char*>(c),8); rf.flush(); cf.flush(); need(bool(rf)&&bool(cf),"CATALOGUE_FLUSH");
}
void bit_reverse(std::vector<uint32_t>& a) {
  for(uint32_t i=1,j=0;i<K;++i) {
    uint32_t bit=K>>1; while(j&bit) { j^=bit; bit>>=1; } j^=bit;
    if(i<j) std::swap(a[i],a[j]); if(!(i&1048575)) deadline();
  }
}
uint32_t dit_residue(std::vector<uint32_t>& a, const std::vector<uint64_t>& pts,const Mod& m) {
  for(uint32_t n=0;n<K;++n) { a[n]=(n<=N?static_cast<uint32_t>(pts[n]%m.p):0); if(!(n&1048575)) deadline(); }
  bit_reverse(a);
  for(uint32_t len=2;len<=K;len<<=1) {
    uint32_t wl=powmod(m.w,K/len,m.p);
    for(uint32_t block=0;block<K;block+=len) {
      uint32_t w=1;
      for(uint32_t j=0;j<len/2;++j) {
        uint32_t u=a[block+j],v=mulmod(a[block+j+len/2],w,m.p);
        a[block+j]=static_cast<uint32_t>((uint64_t(u)+v)%m.p);
        a[block+j+len/2]=static_cast<uint32_t>((uint64_t(u)+m.p-v)%m.p);
        w=mulmod(w,wl,m.p); if(!(j&1048575)) deadline();
      }
      if(!(block&1048575)) deadline();
    }
  }
  uint32_t stride=powmod(m.wi,N,m.p), phase=1,total=0;
  for(uint32_t j=0;j<K;++j) {
    uint32_t term=mulmod(mulmod(a[j],a[j],m.p),phase,m.p);
    total=static_cast<uint32_t>((uint64_t(total)+term)%m.p); phase=mulmod(phase,stride,m.p);
    if(!(j&1048575)) deadline();
  }
  return mulmod(total,m.ki,m.p);
}
Z crt(const std::array<Mod,5>& ms,const std::array<uint32_t,5>& rs) {
  Z c(0), product(1);
  for(size_t i=0;i<ms.size();++i) {
    uint32_t p=ms[i].p, cm=mod32(c,p), pm=mod32(product,p);
    uint32_t delta=static_cast<uint32_t>((uint64_t(rs[i])+p-cm)%p);
    uint32_t t=mulmod(delta,inverse(pm,p),p); c=c+product*Z(t); product=product*Z(p);
    c.cap(192); product.cap(192); need(Z(0)<=c && c<product,"CRT_CANONICAL_RANGE");
  }
  need(c<power(2,153),"CRT_COEFFICIENT_RANGE");
  for(size_t i=0;i<ms.size();++i) need(mod32(c,ms[i].p)==rs[i],"CRT_RESIDUE_RECHECK");
  return c;
}
int run(const std::filesystem::path& dir) {
  need(!std::filesystem::exists(dir),"FRESH_OUTPUT_DIRECTORY_REQUIRED");
  need(std::filesystem::create_directory(dir),"OUTPUT_DIRECTORY_CREATE");
  auto ms=constants();
  constexpr uint64_t payload=4*uint64_t(K)+12*uint64_t(N+1);
  need(payload==UINT64_C(1736870924) && payload+UINT64_C(134217728)<OUTPUT_CAP,"BUFFER_PAYLOAD_BOUND");
  std::vector<uint32_t> cat(size_t(N)+1); std::vector<uint64_t> pts(size_t(N)+1);
  catalogue(cat,pts,dir); std::vector<uint32_t> a(K); std::array<uint32_t,5> rs{};
  for(size_t i=0;i<ms.size();++i) rs[i]=dit_residue(a,pts,ms[i]);
  Z c=crt(ms,rs); deadline();
  std::ofstream report(dir/"producer.txt",std::ios::binary); need(bool(report),"REPORT_OPEN");
  report<<"ROUND22_NATIVE_DIT_OUTPUT\n"<<N<<' '<<K<<' '<<S<<'\n';
  for(auto r:rs) report<<r<<' '; report<<'\n';
  // Fixed stack buffer, no GMP allocator-owned exported string.
  char text[64]; need(mpz_sizeinbase(c.z,10)+2<=sizeof text,"CRT_TEXT_BOUND");
  mpz_get_str(text,10,c.z); report<<text<<"\nNO_INDEPENDENT_CHECKER_VERDICT\n"; report.flush();
  need(bool(report),"REPORT_FLUSH"); need(std::filesystem::file_size(dir/"producer.txt")<=4096,"REPORT_SIZE");
  need(bytes_written+std::filesystem::file_size(dir/"producer.txt")<=OUTPUT_CAP,"OUTPUT_FINAL_BOUND");
  std::cout<<"PRODUCER_FINISHED_REQUIRES_INDEPENDENT_CHECKER\n"; return 0;
}
} // namespace producer22
int main(int argc,char** argv) {
  try { producer22::need(argc==2,"USAGE_PRODUCER_FRESH_OUTPUT_DIR"); return producer22::run(argv[1]); }
  catch(const std::bad_alloc&) { std::cerr<<"RESOURCE_LIMIT_NO_VERDICT_ALLOCATION\n"; return 2; }
  catch(const std::exception& e) { std::cerr<<"NO_MATHEMATICAL_VERDICT "<<e.what()<<'\n'; return 1; }
}
