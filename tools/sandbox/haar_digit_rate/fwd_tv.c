typedef unsigned long size_t;
void *calloc(size_t, size_t); int printf(const char*, ...); double atof(const char*); int atoi(const char*);
double fabs(double);
int main(int argc, char **argv) {
  int NMAX = atoi(argv[1]); int KMAX = atoi(argv[2]); int NMIN = atoi(argv[3]);
  double p0 = 18.0/25, p1 = 6.0/25, p2 = 1.0/25;
  if (argc > 6) { p0 = atof(argv[4]); p1 = atof(argv[5]); p2 = atof(argv[6]); }
  double pi0 = p0*p0+p1*p1+p2*p2, pi1 = p1*(p0+p2), pi2 = p0*p2;
  size_t cap = 4; for (int j = 0; j < NMAX; j++) cap = cap*3/2 + 4;
  double *m = calloc(cap, sizeof(double)), *mn = calloc(cap, sizeof(double));
  int K = 1 << KMAX; double *h = calloc(K, 8);
  size_t top = 1; m[1] = 1.0;
  for (int n = 0; n <= NMAX; n++) {
    if (n >= NMIN && n % 2 == 0) {
      double L = 0; for (size_t d = 1; d <= top; d++) L += m[d];
      printf("n=%d L=%.6f TV:", n, L);
      for (int k = 2; k <= KMAX; k += 2) { int M = 1 << k;
        for (int r = 0; r < M; r++) h[r] = 0;
        for (size_t d = 1; d <= top; d++) h[d & (M-1)] += m[d];
        double tv = 0; for (int r = 0; r < M; r++) tv += fabs(h[r] - L/M);
        printf(" %d:%.2e", k, tv/L); }
      printf("\n");
    }
    if (n == NMAX) break;
    for (size_t d = 0; d <= top*3/2+3 && d < cap; d++) mn[d] = 0;
    size_t nt = 0;
    for (size_t d = 1; d <= top; d++) { double w = m[d]; if (w == 0) continue; size_t u = d/2;
      if (d & 1) { mn[3*u+1] += 2*pi1*w; mn[3*u+2] += 2*pi1*w; if (3*u+2 > nt) nt = 3*u+2; }
      else { mn[3*u] += 2*pi0*w; mn[3*u-1] += 2*pi2*w; mn[3*u+1] += 2*pi2*w; if (3*u+1 > nt) nt = 3*u+1; } }
    double *t = m; m = mn; mn = t; top = nt;
  }
  return 0;
}
