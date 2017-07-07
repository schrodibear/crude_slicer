void *malloc(unsigned long size);
void free(void *);
void __VERIFIER_error(void);

struct outer {
  int a, b;
  struct inner {
    int d;
    char e;
  } inner;
  unsigned f;
  struct inner *pinner;
} globouter;

struct inner globinner;

struct inner f(struct inner *pinner)
{
  pinner->d = pinner->e;
  return *pinner;
}

int main()
{
  int i = 3;
  globouter.pinner = malloc(sizeof(struct inner));
  globouter.pinner->e = i - 1;
  struct inner r = f(globouter.pinner);
  if (r.d == 2) goto out;
  __VERIFIER_error();
 out:
  free(globouter.pinner);
  return 0;
}

