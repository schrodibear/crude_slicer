void *malloc(unsigned long size);
void free(void *);
void __VERIFIER_error(void);

struct outer {
  int a, b;
  struct inner {
    int d;
    char e;
    int *pi;
  } inner;
  unsigned f;
  struct inner *pinner;
} globouter;

struct inner globinner;

struct inner f(struct inner *pinner, struct inner s)
{
  pinner->d = pinner->e;
  s.pi = globouter.inner.pi;
  return *pinner;
}

int main()
{
  int i = 3;
  globouter.pinner = malloc(sizeof(struct inner));
  globouter.pinner->pi = malloc(sizeof(int));
  globouter.pinner->e = i - 1;
  struct inner r = f(globouter.pinner, globouter.inner);
  *(r.pi) = 4;
  globouter.inner.pi = 0;
  if (r.d == 2) goto out;
  __VERIFIER_error();
 out:
  free(globouter.pinner);
  return 0;
}

