// Usage: cross_dense N theta -> k_N(d) = int rho_N(y) rho_N(y+d) dm, d=0..5, all residues (dense).
typedef unsigned long u64;
int printf(const char*, ...); void *malloc(u64); void free(void*); double exp(double); double atof(const char*); int atoi(const char*);
int fflush(void*); 
int main(int argc, char **argv) {
  int Nmax = atoi(argv[1]); double th = atof(argv[2]), t = exp(-th), mu = (1 + t + t * t) / 2;
  float *Z = malloc(sizeof(float)); Z[0] = 1;
  for (int N = 0; N < Nmax; N++) {
    u64 M = 1UL << N, mask = M - 1;
    float *W = malloc(2 * M * sizeof(float));
    for (u64 m = 0; m < M; m++) {
      u64 a = 3 * m;
      W[2*m] = (Z[a & mask] + t * t * Z[(a + 1) & mask]) / mu; W[2*m+1] = t * Z[(a + 2) & mask] / mu;
    }
    free(Z); Z = W;
    u64 L = 2*M, lm = L-1; double k[6]={0};
    for (u64 y = 0; y < L; y++) for (int d=0; d<6; d++) k[d] += (double)Z[y]*Z[(y+d)&lm];
    printf("N=%2d", N+1); for (int d=0; d<6; d++) printf(" k%d=%.4f", d, k[d]/L); printf("\n"); fflush(0);
  }
  return 0;
}
