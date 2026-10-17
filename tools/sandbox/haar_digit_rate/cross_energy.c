// Build: leanc -O3 -c X.c && leanc X.o -o X -lm (no libc headers on the box; prototypes inline).
// Usage: cross_energy N theta   -> lambda_N(1) for the tilted law p ~ (1, e^-theta, e^-2theta).
// lambda_n(1) = 2^n P(sum_{j<n} e_j 2^j/3^{j+1} == 1 mod 2^n), e_j iid pi(e)=g(e)/H^2.
// Forward-propagate weights on delta mod 2^{n-j}: odd delta -> (3d+1)/2,(3d-1)/2 weight a2=2pi(1);
// even delta -> 3d/2 (gam=2pi(0)), (3d+-2)/2 (tau=2pi(2)).  Dense arrays mod 2^{n-j}.
typedef unsigned long u64;
int printf(const char*, ...); void *calloc(u64,u64); void free(void*); double exp(double); double atof(const char*); int atoi(const char*);
int fflush(void*);
int main(int argc, char **argv) {
  int n = atoi(argv[1]); double th = atof(argv[2]), t = exp(-th), H = 1 + t + t*t, H2 = H*H;
  double a2 = 2*(t + t*t*t)/H2, gam = 2*(1 + t*t + t*t*t*t)/H2, tau = 2*t*t/H2;
  // sparse phase: list of (delta,w) as 64-bit ints (exact integers), until 3^j large
  int j = 0; u64 cap = 1UL<<26; long *D = calloc(cap, 8); double *W = calloc(cap, 8); u64 cnt = 1; D[0] = 1; W[0] = 1;
  // simple sparse: no merging (tree), stop when cnt*3 > 2^(n-j) or j==n
  while (j < n && cnt * 3 < (1UL << (n - j)) / 2 && cnt * 3 < cap) {
    long *D2 = calloc(cnt*3, 8); double *W2 = calloc(cnt*3, 8); u64 c2 = 0;
    for (u64 i = 0; i < cnt; i++) { long d = D[i]; double w = W[i];
      if (d & 1) { D2[c2] = (3*d+1)/2; W2[c2++] = w*a2; D2[c2] = (3*d-1)/2; W2[c2++] = w*a2; }
      else { D2[c2] = 3*d/2; W2[c2++] = w*gam; D2[c2] = (3*d+2)/2; W2[c2++] = w*tau; D2[c2] = (3*d-2)/2; W2[c2++] = w*tau; } }
    free(D); free(W); D = D2; W = W2; cnt = c2; j++; }
  int m = n - j; u64 M = 1UL << m; double *A = calloc(M, 8); 
  for (u64 i = 0; i < cnt; i++) A[((u64)D[i]) & (M-1)] += W[i];
  free(D); free(W);
  while (m > 0) { u64 M2 = M >> 1; double *B = calloc(M2 ? M2 : 1, 8);
    for (u64 d = 0; d < M; d++) { double w = A[d]; if (w == 0) continue; u64 h = M2 - 1;
      if (d & 1) { B[((3*d+1)/2) & h] += w*a2; B[((3*d-1)/2) & h] += w*a2; }
      else { B[(3*d/2) & h] += w*gam; B[((3*d+2)/2) & h] += w*tau; B[((3*d-2+2*M)/2) & h] += w*tau; } }
    free(A); A = B; M = M2; m--; }
  printf("n=%d theta=%.3f lambda_n(1)=%.6f\n", n, th, A[0]); return 0; }
