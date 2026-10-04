// Operational checker: same exact A32, DIF, CRT and streamed Lucas checks.
// Exact Horner series is checked against the original reduced-fraction series.
#include <gmp.h>
#include <array>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace checker22 {
constexpr uint32_t nmax=100000000, length=134217728;
constexpr uint64_t scale=UINT64_C(288230376151711744), pointmax=UINT64_C(1)<<63;
constexpr uint64_t outcap=UINT64_C(2147483648);
constexpr size_t bigcap=8192;
static_assert(sizeof(uint32_t)==4 && sizeof(uint64_t)==8);
void demand(bool ok,const char* message) { if(!ok) throw std::runtime_error(message); }
const auto born=std::chrono::steady_clock::now();
uint64_t elapsed_seconds() {
  return std::chrono::duration_cast<std::chrono::seconds>(std::chrono::steady_clock::now()-born).count();
}
uint64_t wall_limit_seconds() {
  static const uint64_t seconds=[] {
    const char* value=std::getenv("GOLDBACH_CHECKER_WALL_SECONDS");
    if(!value) return UINT64_C(86400);
    demand(*value!='\0',"WALL_LIMIT_EMPTY");uint64_t parsed=0;
    for(const char* c=value;*c;++c) {
      demand(*c>='0' && *c<='9',"WALL_LIMIT_FORMAT");
      parsed=parsed*10+static_cast<unsigned>(*c-'0');
      demand(parsed<=86400,"WALL_LIMIT_MAX_24_HOURS");
    }
    demand(parsed>0,"WALL_LIMIT_ZERO");return parsed;
  }();
  return seconds;
}
void progress(const char* phase) {
  std::cerr<<"PROGRESS "<<phase<<" elapsed_seconds="<<elapsed_seconds()<<'\n'<<std::flush;
}
void tick() {
  demand(elapsed_seconds()<wall_limit_seconds(),
         "RESOURCE_LIMIT_NO_VERDICT_WALL");
}
struct Integer {
  mpz_t data;
  Integer(uint64_t v=0) { mpz_init(data); mpz_import(data,1,1,sizeof v,0,0,&v); }
  Integer(const Integer& a) { mpz_init_set(data,a.data); }
  Integer(Integer&& a) noexcept { mpz_init(data); mpz_swap(data,a.data); }
  Integer& operator=(const Integer& a) { if(this!=&a) mpz_set(data,a.data); return *this; }
  Integer& operator=(Integer&& a) noexcept { mpz_swap(data,a.data); return *this; }
  ~Integer() { mpz_clear(data); }
  void bounded(size_t bits=bigcap) const { demand(mpz_sizeinbase(data,2)<=bits,"BIG_INTEGER_CAP"); }
  uint64_t word() const {
    demand(mpz_sgn(data)>=0 && mpz_sizeinbase(data,2)<=64,"WORD_EXPORT_RANGE");
    uint64_t r=0;size_t used=0;mpz_export(&r,&used,1,sizeof r,0,0,data);
    demand(used<=1,"WORD_EXPORT_SIZE");return r;
  }
};
Integer plus(const Integer& a,const Integer& b) { Integer r;mpz_add(r.data,a.data,b.data);r.bounded();return r; }
Integer minus(const Integer& a,const Integer& b) { Integer r;mpz_sub(r.data,a.data,b.data);r.bounded();return r; }
Integer times(const Integer& a,const Integer& b) { Integer r;mpz_mul(r.data,a.data,b.data);r.bounded();return r; }
Integer magnitude(const Integer& a) { Integer r;mpz_abs(r.data,a.data);r.bounded();return r; }
int compare(const Integer& a,const Integer& b) { return mpz_cmp(a.data,b.data); }
Integer exponent(const Integer& a,unsigned e) { Integer r;mpz_pow_ui(r.data,a.data,e);r.bounded();return r; }
Integer quotient_exact(const Integer& a,const Integer& b) {
  demand(mpz_sgn(b.data)>0 && mpz_divisible_p(a.data,b.data),"DIVISION_NOT_EXACT");
  Integer r;mpz_divexact(r.data,a.data,b.data);r.bounded();return r;
}
Integer remainder(const Integer& a,const Integer& b) {
  demand(mpz_sgn(b.data)>0,"MOD_ZERO");Integer r;mpz_mod(r.data,a.data,b.data);r.bounded();return r;
}
uint32_t residue(const Integer& a,uint32_t p) {
  return static_cast<uint32_t>(mpz_fdiv_ui(a.data,p));
}
struct Fraction {
  Integer num,den;
  Fraction(Integer a,Integer b):num(std::move(a)),den(std::move(b)) {
    demand(mpz_sgn(den.data)>0,"FRACTION_DENOMINATOR");Integer gcd;
    mpz_gcd(gcd.data,num.data,den.data);gcd.bounded();
    num=quotient_exact(num,gcd);den=quotient_exact(den,gcd);
  }
};
Fraction add_fraction(const Fraction& a,const Fraction& b) {
  return Fraction(plus(times(a.num,b.den),times(b.num,a.den)),times(a.den,b.den));
}
Fraction odd_log_series_reference(uint32_t a,uint32_t d,unsigned terms) {
  demand(d>0 && uint64_t(a)*3<=d && (terms==32 || terms==40),"LOG_SERIES_DOMAIN");
  Fraction acc(Integer(0),Integer(1));
  // Independent construction: each rational term is reduced on accumulation.
  for(unsigned j=0;j<terms;++j) {
    unsigned odd=2*j+1;
    Fraction term(times(Integer(2),exponent(Integer(a),odd)),
                  times(Integer(odd),exponent(Integer(d),odd)));
    acc=add_fraction(acc,term);
  }
  return acc;
}
struct SeriesCoefficients {
  Integer common;
  std::vector<Integer> values;
  explicit SeriesCoefficients(unsigned terms):common(1),values(terms) {
    for(unsigned j=0;j<terms;++j)common=times(common,Integer(2*j+1));
    for(unsigned j=0;j<terms;++j)values[j]=quotient_exact(common,Integer(2*j+1));
  }
};
const SeriesCoefficients& series_coefficients(unsigned terms) {
  static const SeriesCoefficients t32(32),t40(40);
  demand(terms==32 || terms==40,"LOG_SERIES_TERMS");return terms==32?t32:t40;
}
Fraction odd_log_series(uint32_t a,uint32_t d,unsigned terms) {
  demand(d>0 && uint64_t(a)*3<=d && (terms==32 || terms==40),"LOG_SERIES_DOMAIN");
  const auto& c=series_coefficients(terms);
  Integer a2=times(Integer(a),Integer(a)),d2=times(Integer(d),Integer(d));
  Integer numerator=c.values.back(),d_power(1);
  // Homogeneous Horner evaluation keeps every original rational term exact.
  for(unsigned j=terms-1;j>0;--j) {
    d_power=times(d_power,d2);
    numerator=plus(times(numerator,a2),times(c.values[j-1],d_power));
  }
  return Fraction(times(times(Integer(2),Integer(a)),numerator),
                  times(exponent(Integer(d),2*terms-1),c.common));
}
const Fraction& log_two_series(unsigned terms) {
  static const Fraction t32=odd_log_series(1,3,32),t40=odd_log_series(1,3,40);
  demand(terms==32 || terms==40,"LOG_SERIES_TERMS");return terms==32?t32:t40;
}
struct LogInterval { Integer lower,upper,den; };
LogInterval rational_log_impl(uint32_t p,unsigned terms,bool reference) {
  demand(p>=2 && p<=nmax && (terms==32 || terms==40),"LOG_ARGUMENT_DOMAIN");unsigned k=0;uint32_t base=1;
  while(base<=p/2) { base*=2;++k; }
  demand(k<=26 && base<=p && p<2*uint64_t(base),"LOG_INTEGER_REDUCTION");
  Fraction f=reference?odd_log_series_reference(p-base,p+base,terms):odd_log_series(p-base,p+base,terms);
  Fraction two=reference?odd_log_series_reference(1,3,terms):log_two_series(terms);
  Fraction low=add_fraction(f,Fraction(times(Integer(k),two.num),two.den));
  Fraction tail(times(Integer(k+1),Integer(9)),
                times(Integer(4*(2*terms+1)),exponent(Integer(3),2*terms+1)));
  Fraction high=add_fraction(low,tail);
  LogInterval b{times(low.num,high.den),times(high.num,low.den),times(low.den,high.den)};
  demand(compare(b.lower,Integer(0))>=0 && compare(b.upper,b.lower)>=0,"LOG_INTERVAL_ORDER");
  demand(compare(times(minus(b.upper,b.lower),Integer(scale)),b.den)<0,"LOG_INTERVAL_WIDTH");
  return b;
}
LogInterval rational_log(uint32_t p,unsigned terms) { return rational_log_impl(p,terms,false); }
void verify_series_optimization() {
  std::vector<uint32_t> arguments{2,3,5,7,11,37,97,65521,99999989,100000000};
  for(unsigned k:{2u,3u,4u,5u,7u,8u,10u,12u,14u,16u,18u,20u,21u,22u,23u,24u,25u,26u}) {
    uint32_t b=UINT32_C(1)<<k;
    arguments.push_back(b-1);arguments.push_back(b);arguments.push_back(b+1);
  }
  demand(arguments.size()==64,"PREFLIGHT_ARGUMENT_COUNT");
  for(uint32_t p:arguments)for(unsigned terms:{32u,40u}) {
    LogInterval optimized=rational_log_impl(p,terms,false),reference=rational_log_impl(p,terms,true);
    Fraction ol(optimized.lower,optimized.den),rl(reference.lower,reference.den);
    Fraction ou(optimized.upper,optimized.den),ru(reference.upper,reference.den);
    demand(compare(ol.num,rl.num)==0 && compare(ol.den,rl.den)==0,
           "HORNER_REFERENCE_LOWER_DISAGREEMENT");
    demand(compare(ou.num,ru.num)==0 && compare(ou.den,ru.den)==0,
           "HORNER_REFERENCE_UPPER_DISAGREEMENT");
  }
  std::cerr<<"PREFLIGHT_EXACT_SERIES_COMPARISONS 128 PASS\n"<<std::flush;
}
void enclose_point(const LogInterval& b,uint64_t value) {
  demand(value<=pointmax,"POINT_RANGE");Integer a(value);
  demand(compare(magnitude(minus(times(a,b.den),times(Integer(scale),b.lower))),b.den)<=0,
         "LOG_LOWER_DISTANCE");
  demand(compare(magnitude(minus(times(a,b.den),times(Integer(scale),b.upper))),b.den)<=0,
         "LOG_UPPER_DISTANCE");
}
uint64_t nearest_even_point(const LogInterval& b) {
  Integer numerator=times(Integer(scale),plus(b.lower,b.upper)),den=times(Integer(2),b.den),q,r;
  mpz_fdiv_qr(q.data,r.data,numerator.data,den.data);q.bounded();r.bounded();
  int half=compare(times(Integer(2),r),den);
  if(half>0 || (half==0 && mpz_odd_p(q.data))) q=plus(q,Integer(1));
  if(compare(q,Integer(0))<0) q=Integer(0);
  if(compare(q,Integer(pointmax))>0) q=Integer(pointmax);
  uint64_t v=q.word();enclose_point(b,v);return v;
}
uint32_t product_mod(uint32_t a,uint32_t b,uint32_t modulus) {
  demand(a<modulus && b<modulus,"UNCANONICAL_MULTIPLICAND");
  return static_cast<uint32_t>((uint64_t(a)*uint64_t(b))%modulus);
}
uint32_t power_mod(uint32_t base,uint32_t e,uint32_t p) {
  demand(p>1,"MODULUS_DOMAIN");base%=p;if(e==0)return 1;
  uint32_t bit=UINT32_C(1)<<31;while(!(e&bit))bit>>=1;uint32_t result=1;
  for(;bit;bit>>=1) { result=product_mod(result,result,p);if(e&bit)result=product_mod(result,base,p); }
  return result;
}
struct Parameters { uint32_t prime,candidate_base,root,inverse_root,inverse_length; };
std::array<Parameters,5> verify_parameters() {
  const std::array<uint32_t,5> primes{{2013265921,2281701377,3221225473,3489660929,3892314113}};
  const std::array<uint32_t,5> cofactors{{15,17,24,26,29}},bases{{31,3,5,3,3}};
  std::array<Parameters,5> out{};Integer coverage(1);
  for(size_t i=0;i<5;++i) {
    uint32_t p=primes[i];demand(p==uint64_t(cofactors[i])*length+1 && (p&1),"MODULAR_PARAMETER_FORM");
    for(size_t j=0;j<i;++j)demand(p!=primes[j],"MODULUS_DUPLICATION");
    for(uint32_t d=3;uint64_t(d)*d<=p;d+=2) {
      demand(p%d!=0,"COMPOSITE_MODULUS");if((d&4095)==4095)tick();
    }
    uint32_t root=power_mod(bases[i],cofactors[i],p);
    demand(root>0 && power_mod(root,length,p)==1 && power_mod(root,length/2,p)!=1,"ORDER_NOT_LENGTH");
    uint32_t ri=power_mod(root,p-2,p),li=power_mod(length,p-2,p);
    demand(product_mod(ri,root,p)==1 && product_mod(li,length,p)==1,"FERMAT_INVERSE_PRODUCT");
    out[i]={p,bases[i],root,ri,li};coverage=times(coverage,Integer(p));
  }
  demand(compare(coverage,exponent(Integer(2),154))>0,"MODULI_COVERAGE");
  demand(compare(times(Integer(nmax+1),times(Integer(pointmax),Integer(pointmax))),
                 exponent(Integer(2),153))<0,"POINT_COEFFICIENT_BOUND");
  Integer joint=times(times(Integer(2),Integer(nmax+1)),plus(times(Integer(64),Integer(scale)),Integer(1)));
  demand(compare(times(joint,Integer(1000000)),times(Integer(scale),Integer(scale)))<=0,"TAU_INTEGER_GUARD");
  return out;
}
uint32_t get32(std::ifstream& f) {
  unsigned char b[4];f.read(reinterpret_cast<char*>(b),4);demand(bool(f),"TRUNCATED_U32");
  uint32_t n=0;for(unsigned j=0;j<4;++j)n|=uint32_t(b[j])<<(8*j);return n;
}
uint64_t get64(std::ifstream& f) {
  unsigned char b[8];f.read(reinterpret_cast<char*>(b),8);demand(bool(f),"TRUNCATED_U64");
  uint64_t n=0;for(unsigned j=0;j<8;++j)n|=uint64_t(b[j])<<(8*j);return n;
}
void header(std::ifstream& f,const char expected[8]) {
  char m[8];f.read(m,8);demand(bool(f)&&std::memcmp(m,expected,8)==0,"WRONG_BINARY_SCHEMA");
  demand(get64(f)==nmax,"WRONG_N_HEADER");
}
std::vector<uint32_t> distinct_factors(uint32_t r,const std::vector<uint32_t>& f,uint32_t before) {
  std::vector<uint32_t> qs;
  while(r!=1) {
    demand(r<before && r>=2,"CERTIFICATE_FACTOR_INDEX");uint32_t q=f[r];
    demand(q>=2 && q<=r && r%q==0 && q<before && f[q]==q,"CERTIFICATE_FACTOR_NOT_VERIFIED");
    qs.push_back(q);while(r%q==0)r/=q;demand(qs.size()<=27,"CERTIFICATE_FACTOR_COUNT");
  }
  return qs;
}
void check_lucas(uint32_t p,uint32_t g,const std::vector<uint32_t>& qs) {
  demand(g>=1 && g<p,"LUCAS_BASE_RANGE");demand(power_mod(g,p-1,p)==1,"LUCAS_FULL_EXPONENT");
  for(uint32_t q:qs)demand(power_mod(g,(p-1)/q,p)!=1,"LUCAS_MISSING_FULL_ORDER");
}
void verify_catalogue(const std::filesystem::path& dir,std::vector<uint32_t>& f,
                      std::vector<uint64_t>& pts,uint64_t& records) {
  progress("catalogue_factor_read_start");
  const char cm[8]={'G','B','C','A','T','2','2',0},rm[8]={'G','B','R','E','C','2','2',0};
  demand(std::filesystem::file_size(dir/"factors.bin")==16+4*uint64_t(nmax+1),"FACTOR_FILE_LENGTH");
  std::ifstream cf(dir/"factors.bin",std::ios::binary);demand(bool(cf),"FACTOR_FILE_OPEN");header(cf,cm);
  for(uint32_t n=0;n<=nmax;++n) { f[n]=get32(cf);if(!(n&1048575))tick(); }
  progress("catalogue_factor_read_finish");
  demand(f[0]==0 && f[1]==0,"ZERO_ONE_CATALOGUE");
  std::ifstream rf(dir/"records.bin",std::ios::binary);demand(bool(rf),"RECORD_FILE_OPEN");header(rf,rm);
  records=get64(rf);demand(records<=nmax/2+1,"RECORD_COUNT_LIMIT");
  demand(std::filesystem::file_size(dir/"records.bin")==24+16*records,"RECORD_FILE_LENGTH");
  uint64_t count=0;
  progress("catalogue_lucas_A32_log40_start");
  for(uint32_t n=2;n<=nmax;++n) {
    if(!(n&4095))tick();uint32_t p=f[n];
    demand(p>=2 && p<=n && n%p==0,"FACTOR_COVERAGE");
    if(p==n) {
      demand(count<records,"MISSING_PRIME_RECORD");uint32_t rp=get32(rf),g=get32(rf);uint64_t point=get64(rf);
      demand(rp==n,"UNSORTED_OR_WRONG_PRIME_RECORD");
      check_lucas(n,g,distinct_factors(n-1,f,n));
      // Exact canonical A32 bridge, reconstructed independently of producer log32.
      demand(nearest_even_point(rational_log(n,32))==point,"NONCANONICAL_LOG32_RECORD");
      enclose_point(rational_log(n,40),point);pts[n]=point;++count;
      if(count%100000==0)std::cerr<<"PROGRESS catalogue primes="<<count<<" n="<<n
        <<" elapsed_seconds="<<elapsed_seconds()<<'\n'<<std::flush;
    } else {
      demand(p<n && f[p]==p,"NONPRIME_FACTOR_BASE");
      uint32_t r=n;while(r%p==0)r/=p;pts[n]=(r==1?pts[p]:0);
    }
  }
  demand(count==records,"EXTRA_PRIME_RECORD");
  progress("catalogue_lucas_A32_log40_finish");
}
uint32_t reverse27(uint32_t x) {
  x=((x&UINT32_C(0x55555555))<<1)|((x>>1)&UINT32_C(0x55555555));
  x=((x&UINT32_C(0x33333333))<<2)|((x>>2)&UINT32_C(0x33333333));
  x=((x&UINT32_C(0x0f0f0f0f))<<4)|((x>>4)&UINT32_C(0x0f0f0f0f));
  x=((x&UINT32_C(0x00ff00ff))<<8)|((x>>8)&UINT32_C(0x00ff00ff));
  x=(x<<16)|(x>>16);return x>>5;
}
uint32_t dif_target(std::vector<uint32_t>& data,const std::vector<uint64_t>& points,const Parameters& m) {
  for(uint32_t j=0;j<length;++j) { data[j]=(j<=nmax?static_cast<uint32_t>(points[j]%m.prime):0);if(!(j&1048575))tick(); }
  for(uint32_t size=length;size>1;size/=2) {
    uint32_t unit=power_mod(m.root,length/size,m.prime);
    for(uint32_t offset=0;offset<length;offset+=size) {
      uint32_t twiddle=1;
      for(uint32_t i=0;i<size/2;++i) {
        uint32_t x=data[offset+i],y=data[offset+i+size/2];
        uint32_t difference=static_cast<uint32_t>((uint64_t(x)+m.prime-y)%m.prime);
        data[offset+i]=static_cast<uint32_t>((uint64_t(x)+y)%m.prime);
        data[offset+i+size/2]=product_mod(difference,twiddle,m.prime);
        twiddle=product_mod(twiddle,unit,m.prime);if(!(i&1048575))tick();
      }
      if(!(offset&1048575))tick();
    }
    std::cerr<<"PROGRESS dif prime="<<m.prime<<" stage_size="<<size
      <<" elapsed_seconds="<<elapsed_seconds()<<'\n'<<std::flush;
  }
  for(uint32_t j=0;j<length;++j) {
    uint32_t r=reverse27(j);demand(r<length,"REVERSE_INDEX_RANGE");if(j<r)std::swap(data[j],data[r]);
    if(!(j&1048575))tick();
  }
  uint32_t root_phase=power_mod(m.inverse_root,nmax,m.prime),v=1,acc=0;
  for(uint32_t j=0;j<length;++j) {
    uint32_t sq=product_mod(data[j],data[j],m.prime);
    uint32_t term=product_mod(sq,v,m.prime);
    acc=static_cast<uint32_t>((uint64_t(acc)+term)%m.prime);v=product_mod(v,root_phase,m.prime);
    if(!(j&1048575))tick();
  }
  return product_mod(acc,m.inverse_length,m.prime);
}
struct Wide192 { uint64_t low=0,middle=0,high=0; };
void accumulate_product(Wide192& sum,uint64_t a,uint64_t b) {
  demand(a<=pointmax && b<=pointmax,"FOLD_POINT_RANGE");
  const uint64_t mask=UINT64_C(0xffffffff);uint64_t a0=a&mask,a1=a>>32,b0=b&mask,b1=b>>32;
  uint64_t base=a0*b0,t=a1*b0+(base>>32),u=a0*b1+(t&mask);
  uint64_t lo=(u<<32)|(base&mask),hi=a1*b1+(t>>32)+(u>>32);
  uint64_t old=sum.low;sum.low+=lo;uint64_t carry=sum.low<old;
  old=sum.middle;sum.middle+=hi;uint64_t c1=sum.middle<old;
  old=sum.middle;sum.middle+=carry;uint64_t c2=sum.middle<old;
  demand(c1+c2<=1,"FOLD_CARRY_INVARIANT");
  demand(sum.high<(UINT64_C(1)<<25),"FOLD_HIGH_PREBOUND");sum.high+=c1+c2;
  demand(sum.high<(UINT64_C(1)<<25),"FOLD_COEFFICIENT_RANGE");
}
Integer fold(const std::vector<uint64_t>& pts) {
  Wide192 sum;
  for(uint32_t n=0;n<=nmax;++n) { accumulate_product(sum,pts[n],pts[nmax-n]);if(!(n&1048575))tick(); }
  uint64_t words[3]={sum.low,sum.middle,sum.high};Integer result;
  mpz_import(result.data,3,-1,sizeof(uint64_t),0,0,words);result.bounded(153);return result;
}
Integer crt_basis(const std::array<Parameters,5>& pars,const std::array<uint32_t,5>& rs) {
  Integer product(1);for(auto p:pars)product=times(product,Integer(p.prime));
  Integer result(0);
  for(size_t i=0;i<5;++i) {
    Integer basis=quotient_exact(product,Integer(pars[i].prime));
    uint32_t r=residue(basis,pars[i].prime),inv=power_mod(r,pars[i].prime-2,pars[i].prime);
    demand(product_mod(r,inv,pars[i].prime)==1,"CRT_BASIS_INVERSE");
    Integer term=times(times(basis,Integer(rs[i])),Integer(inv));term.bounded(256);
    result=plus(result,term);result.bounded(256);
  }
  result=remainder(result,product);result.bounded(153);
  for(size_t i=0;i<5;++i)demand(residue(result,pars[i].prime)==rs[i],"CRT_BASIS_RESIDUES");return result;
}
struct Claim { std::array<uint32_t,5> residues;Integer coefficient; };
Claim read_claim(const std::filesystem::path& dir) {
  demand(std::filesystem::file_size(dir/"producer.txt")<=4096,"CLAIM_FILE_SIZE");
  std::ifstream f(dir/"producer.txt",std::ios::binary);demand(bool(f),"CLAIM_OPEN");
  std::string schema,integer,tail;uint64_t n,k,s;Claim out{};
  f>>schema>>n>>k>>s;demand(bool(f)&&schema=="ROUND22_NATIVE_DIT_OUTPUT"&&n==nmax&&k==length&&s==scale,
                            "CLAIM_PARAMETERS");
  for(auto& r:out.residues) { uint64_t v;f>>v;demand(bool(f)&&v<=UINT32_MAX,"CLAIM_RESIDUE_WORD");r=uint32_t(v); }
  f>>integer>>tail;demand(bool(f)&&integer.size()<=47&&!integer.empty()&&tail=="NO_INDEPENDENT_CHECKER_VERDICT",
                          "CLAIM_INTEGER_FORMAT");
  for(char c:integer)demand(c>='0'&&c<='9',"CLAIM_SIGN_OR_NONINTEGER");
  demand(integer.size()==1||integer[0]!='0',"CLAIM_NONCANONICAL_INTEGER");
  demand(mpz_set_str(out.coefficient.data,integer.c_str(),10)==0,"CLAIM_INTEGER_PARSE");out.coefficient.bounded(153);
  std::string extra;demand(!(f>>extra),"CLAIM_TRAILING_FIELDS");return out;
}
void rebuild_reference(const std::filesystem::path& dir,const std::vector<uint32_t>& cat,
                       std::vector<uint64_t>& pts,uint64_t records) {
  std::ifstream rf(dir/"records.bin",std::ios::binary);demand(bool(rf),"REFERENCE_RECORD_OPEN");
  rf.seekg(24);demand(bool(rf),"REFERENCE_RECORD_SEEK");uint64_t count=0;pts[0]=pts[1]=0;
  for(uint32_t n=2;n<=nmax;++n) {
    uint32_t p=cat[n];if(p==n) {
      uint32_t rp=get32(rf);(void)get32(rf);(void)get64(rf);demand(rp==n,"REFERENCE_RECORD_ORDER");
      pts[n]=nearest_even_point(rational_log(n,40));++count;
      if(count%100000==0)std::cerr<<"PROGRESS reference primes="<<count<<" n="<<n
        <<" elapsed_seconds="<<elapsed_seconds()<<'\n'<<std::flush;
    } else { uint32_t r=n;while(r%p==0)r/=p;pts[n]=(r==1?pts[p]:0); }
    if(!(n&4095))tick();
  }
  demand(count==records,"REFERENCE_RECORD_COUNT");
}
void print_integer(const Integer& a) {
  char text[128];demand(mpz_sizeinbase(a.data,10)+2<=sizeof text,"PRINT_BOUND");mpz_get_str(text,10,a.data);std::cout<<text;
}
int run(const std::filesystem::path& dir) {
  std::cerr<<"OPERATIONAL_WALL_LIMIT_SECONDS "<<wall_limit_seconds()<<'\n'<<std::flush;
  progress("preflight_start");verify_series_optimization();progress("preflight_finish");
  auto pars=verify_parameters();Claim claim=read_claim(dir);
  constexpr uint64_t payload=4*uint64_t(length)+12*uint64_t(nmax+1);
  demand(payload==UINT64_C(1736870924)&&payload+UINT64_C(134217728)<outcap,"BUFFER_PAYLOAD_BOUND");
  uint64_t factor_bytes=std::filesystem::file_size(dir/"factors.bin"),
           record_bytes=std::filesystem::file_size(dir/"records.bin"),
           claim_bytes=std::filesystem::file_size(dir/"producer.txt");
  demand(factor_bytes<=outcap && record_bytes<=outcap && claim_bytes<=4096,"INPUT_FILE_SIZE_LIMIT");
  uint64_t input_bytes=factor_bytes+record_bytes+claim_bytes;
  demand(input_bytes<=outcap,"INPUT_OUTPUT_PAYLOAD_LIMIT");
  std::vector<uint32_t> cat(size_t(nmax)+1);std::vector<uint64_t> points(size_t(nmax)+1);uint64_t records=0;
  verify_catalogue(dir,cat,points,records);progress("direct_A32_start");Integer direct_a=fold(points);
  progress("direct_A32_finish");
  std::vector<uint32_t> data(length);std::array<uint32_t,5> rs{};
  for(size_t i=0;i<5;++i) {
    std::cerr<<"PROGRESS dif_modulus_start index="<<i<<" prime="<<pars[i].prime
      <<" elapsed_seconds="<<elapsed_seconds()<<'\n'<<std::flush;
    demand(claim.residues[i]<pars[i].prime,"CLAIM_NONCANONICAL_RESIDUE");rs[i]=dif_target(data,points,pars[i]);
    demand(rs[i]==claim.residues[i],"DIT_DIF_RESIDUE_DISAGREEMENT");
    std::cerr<<"PROGRESS dif_modulus_finish index="<<i<<" residue="<<rs[i]
      <<" elapsed_seconds="<<elapsed_seconds()<<'\n'<<std::flush;
  }
  Integer c=crt_basis(pars,rs);
  demand(compare(c,claim.coefficient)==0 && compare(c,direct_a)==0,"EXACT_CRT_FOLD_DISAGREEMENT");
  progress("exact_CRT_A32_equality_pass");
  // Free the transform before rebuilding the independent points; payload never grows.
  std::vector<uint32_t>().swap(data);progress("reference_log40_start");
  rebuild_reference(dir,cat,points,records);progress("reference_log40_finish");Integer direct_b=fold(points);
  progress("direct_log40_finish");
  Integer error_num=times(times(Integer(2),Integer(nmax+1)),plus(times(Integer(64),Integer(scale)),Integer(1)));
  demand(compare(magnitude(minus(c,direct_b)),error_num)<=0,"INDEPENDENT_LOG_REFERENCE_DISAGREEMENT");
  demand(compare(times(error_num,Integer(1000000)),times(Integer(scale),Integer(scale)))<=0,"FINAL_TAU_GUARD");tick();
  std::cout<<"EXACT_INTEGER_PROJECTION_CHECKED_PENDING_PRIMITIVE_PROOF\nC_A ";print_integer(c);
  std::cout<<"\nDIRECT_A ";print_integer(direct_a);
  std::cout<<"\nC_B ";print_integer(direct_b);std::cout<<"\nERROR_NUMERATOR ";print_integer(error_num);
  std::cout<<"\nERROR_DENOMINATOR ";print_integer(times(Integer(scale),Integer(scale)));
  std::cout<<"\nRECORD_COUNT "<<records<<"\nRESIDUES";
  for(uint32_t r:rs)std::cout<<' '<<r;
  std::cout<<"\nFORMAL_PRIMITIVES false\nSPECTRAL_H1 false\nD_N false\nWIN false\n";return 0;
}
} // namespace checker22
int main(int argc,char** argv) {
  try {
    checker22::demand(argc==2,"USAGE_CHECKER_EXISTING_PRODUCER_DIRECTORY");
    if(std::string(argv[1])=="--self-test") {
      checker22::verify_series_optimization();
      std::cout<<"EXACT_HORNER_REFERENCE_SELF_TEST_PASS\n";return 0;
    }
    return checker22::run(argv[1]);
  }
  catch(const std::bad_alloc&) { std::cerr<<"RESOURCE_LIMIT_NO_VERDICT_ALLOCATION\n";return 2; }
  catch(const std::exception& e) { std::cerr<<"NO_MATHEMATICAL_VERDICT "<<e.what()<<'\n';return 1; }
}
