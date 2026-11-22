/* Independent brute-force computation of the Apery set Ap(S,a) for S=<n^k,(n+1)^k,(n+2)^k>
   via the round-robin algorithm of Boecker--Liptak.  Prints n, F(S), genus g(S), type t(S),
   and the pseudo-Frobenius numbers.  Usage: ./apery k nmin nmax                       */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned long long u64; typedef __int128 i128;
static u64 gcdu(u64 x,u64 y){while(y){u64 t=x%y;x=y;y=t;}return x;}
static u64 ipow(u64 x,int k){u64 r=1;while(k--)r*=x;return r;}
static void print128(i128 v){char buf[64];int i=63;buf[i]=0;int neg=v<0;if(neg)v=-v;if(v==0)buf[--i]='0';while(v>0){buf[--i]='0'+(int)(v%10);v/=10;}if(neg)buf[--i]='-';printf("%s",buf+i);}
int main(int argc,char**argv){
  int k=atoi(argv[1]); u64 nmin=atoll(argv[2]), nmax=atoll(argv[3]);
  for(u64 n=nmin;n<=nmax;n++){
    u64 a=ipow(n,k), g[2]={ipow(n+1,k),ipow(n+2,k)};
    u64 *w=malloc(sizeof(u64)*a); const u64 INF=~0ULL;
    for(u64 i=0;i<a;i++) w[i]=INF; w[0]=0;
    for(int t=0;t<2;t++){
      u64 gg=g[t], d=gcdu(a,gg%a);
      for(u64 r=0;r<d;r++){
        /* find minimum on the cycle r, r+gg, ... (mod a) */
        u64 len=a/d, best=INF, pos=r, p=r;
        for(u64 j=0;j<len;j++){ if(w[p]<best){best=w[p];pos=p;} p=(p+gg)%a; }
        if(best==INF) continue;
        p=pos;
        for(u64 j=0;j<len;j++){ u64 q=(p+gg)%a; if(w[p]!=INF && w[p]+gg<w[q]) w[q]=w[p]+gg; p=q; }
      }
    }
    u64 mx=0; i128 sum=0; int type=0; u64 pf[8]; 
    for(u64 i=0;i<a;i++){ if(w[i]==INF){printf("error\n");return 1;} if(w[i]>mx)mx=w[i]; sum+=w[i]; }
    for(u64 i=0;i<a;i++){
      int maximal=1;
      for(int t=0;t<2;t++){ u64 v=w[i]+g[t]; if(w[v%a]==v){maximal=0;break;} }
      if(maximal){ if(type<8) pf[type]=w[i]-a; type++; }
    }
    /* genus = sum/a - (a-1)/2 */
    i128 twice_g = (2*sum)/a - (i128)(a-1);
    if((2*sum)%a){printf("nonint\n");return 1;}
    printf("%llu %llu ",(unsigned long long)n,(unsigned long long)(mx-a)); print128(twice_g/2); printf(" %d",type);
    for(int t=0;t<type&&t<8;t++) printf(" %llu",(unsigned long long)pf[t]); printf("\n");
    free(w);
  }
  return 0;
}
