typedef unsigned long size_t;
void *calloc(size_t, size_t); int printf(const char*, ...); double atof(const char*); int atoi(const char*);
double cos(double); double sin(double); double sqrt(double);
static void fft(double *re, double *im, int n) { // in-place radix-2
  for (int i = 1, j = 0; i < n; i++) { int bit = n >> 1; for (; j & bit; bit >>= 1) j ^= bit; j ^= bit;
    if (i < j) { double t = re[i]; re[i] = re[j]; re[j] = t; t = im[i]; im[i] = im[j]; im[j] = t; } }
  for (int len = 2; len <= n; len <<= 1) { double ang = 6.283185307179586/len;
    for (int i = 0; i < n; i += len) for (int j = 0; j < len/2; j++) {
      double wr = cos(ang*j), wi = sin(ang*j);
      double ur = re[i+j], ui = im[i+j], vr = re[i+j+len/2]*wr - im[i+j+len/2]*wi, vi = re[i+j+len/2]*wi + im[i+j+len/2]*wr;
      re[i+j] = ur+vr; im[i+j] = ui+vi; re[i+j+len/2] = ur-vr; im[i+j+len/2] = ui-vi; } } }
int main(int argc, char **argv) {
  int NMAX = atoi(argv[1]); int KMAX = atoi(argv[2]); int NMIN = atoi(argv[3]);
  double p0 = 18.0/25, p1 = 6.0/25, p2 = 1.0/25;
  if (argc > 6) { p0 = atof(argv[4]); p1 = atof(argv[5]); p2 = atof(argv[6]); }
  double pi0 = p0*p0+p1*p1+p2*p2, pi1 = p1*(p0+p2), pi2 = p0*p2;
  size_t cap = 4; for (int j = 0; j < NMAX; j++) cap = cap*3/2 + 4;
  double *m = calloc(cap, sizeof(double)), *mn = calloc(cap, sizeof(double));
  int K = 1 << KMAX; double *re = calloc(K, 8), *im = calloc(K, 8);
  size_t top = 1; m[1] = 1.0;
  for (int n = 0; n <= NMAX; n++) {
    if (n >= NMIN && n % 2 == 0) {
      double L = 0; for (size_t d = 1; d <= top; d++) L += m[d];
      printf("n=%d L=%.6f maxk:", n, L);
      for (int k = 2; k <= KMAX; k += 2) { int M = 1 << k;
        for (int r = 0; r < M; r++) { re[r] = 0; im[r] = 0; }
        for (size_t d = 1; d <= top; d++) re[d & (M-1)] += m[d];
        fft(re, im, M); double best = 0;
        for (int a = 1; a < M; a++) { double v = sqrt(re[a]*re[a]+im[a]*im[a]); if (v > best) best = v; }
        printf(" %d:%.2e", k, best/L); }
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
