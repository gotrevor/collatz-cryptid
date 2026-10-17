typedef unsigned long size_t;
void *calloc(size_t, size_t); int printf(const char*, ...); double atof(const char*); int atoi(const char*);
int main(int argc, char **argv) {
  int NMAX = atoi(argv[1]);
  double p0 = 18.0/25, p1 = 6.0/25, p2 = 1.0/25;
  if (argc > 4) { p0 = atof(argv[2]); p1 = atof(argv[3]); p2 = atof(argv[4]); }
  double pi0 = p0*p0+p1*p1+p2*p2, pi1 = p1*(p0+p2), pi2 = p0*p2;
  size_t cap = 4; for (int j = 0; j < NMAX; j++) cap = cap*3/2 + 4;
  double *m = calloc(cap, sizeof(double)), *mn = calloc(cap, sizeof(double));
  size_t top = 1; m[1] = 1.0; double Lprev = 0;
  for (int n = 0; n <= NMAX; n++) {
    double L = 0, c2 = 0, c4 = 0; 
    for (size_t d = 1; d <= top; d++) { L += m[d]; c2 += (d&1) ? -m[d] : m[d];
      int r = d & 3; c4 += (r==0) ? m[d] : (r==2 ? -m[d] : 0); }
    printf("%d %.9f  par=%+.3e  chi4=%+.3e  dL=%+.3e\n", n, L, c2/L, c4/L, L-Lprev);
    Lprev = L;
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
