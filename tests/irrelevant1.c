#include <stddef.h>

void *malloc(unsigned long size);
void free(void *);
void __VERIFIER_error(void);
int __VERIFIER_nondet_int(void);

struct outer {
  struct firstinner {
    struct firstinnermost {
      int a[10];
      int b;
      char c;
    } firstinnermost;
  } firstinner;
  struct secondinner {
  } secondinner[4];
  int f;
  void *p;
  void **pp;
} globouter;

struct firstinnermost *get_firstinnermost(struct outer *outer)
{
  return &outer->firstinner.firstinnermost;
}

struct outer *get_outer(struct firstinnermost *firstinnermost)
{
  return (struct outer *)((char *)firstinnermost - offsetof(struct outer, firstinner.firstinnermost));
}

struct secondinner *get_secondinner(struct outer *outer)
{
  return &outer->secondinner[2];
}

struct outer *get_outer_(struct secondinner *secondinner)
{
  return (struct outer*)((char *)(secondinner - 2) - (size_t)(&((struct outer *)0)->secondinner));
}

int *get_b(struct outer* outer)
{
  return &outer->firstinner.firstinnermost.b;
}

struct outer *get_outer__(void **b)
{
  return (struct outer *)((char *)*((int **)b) - offsetof(struct outer, firstinner.firstinnermost.b));
}

struct outer *get_outer___(void **b)
{
  return ((struct outer *)*((int **)b) + 0xFFFFFFFFFFFFFFD8UL);
}

char s[] = "UFFFFFF";

int test(int p)
{
  struct outer *pg0 = &globouter, *pg1 = malloc(sizeof(struct outer));
  void *pv0 = (void *)pg0;
  void *pv1 = (void *)&pg0->firstinner;
  void *pv2 = (void *)&pg0->firstinner.firstinnermost;
                                            /* same regions of pv1~pv2 ensure unfy_voids for n == 0 */
  int x;
  int *px = &x;
  int **ppx = &px;
  void **ppv = (void **)ppx;
  int *px0 = *(int **)ppv;                  /* same regions of px0~px1~px2 ensures unify_voids for n > 0 */
  int *px1 = (int *)((void *)&x);
  int *px2 = (int *)*ppv;
  char *pc0 = (char *)px1;
  *pc0 = 'c';                               /* this write to pc0 should be reflected as a write to region(px1) too */
  struct firstinnermost *fi0 = get_firstinnermost(pg0);
  struct firstinnermost *fi1 = get_firstinnermost(pg1);
  struct outer *pg2 = get_outer(fi0);
  struct outer *pg3 = get_outer(fi1);
  struct secondinner *si0 = get_secondinner(pg2);
  struct secondinner *si1 = get_secondinner(pg3);
  struct outer *pg4 = get_outer_(si0);
  struct outer *pg5 = get_outer_(si1);
  int *pb0 = get_b(pg4);
  int *pb1 = get_b(pg5);
  int **ppb0 = &pb0;
  int **ppb1 = &pb1;
  struct outer *pg6 = get_outer__((void **)ppb0);
  struct outer *pg7 = get_outer___((void **)ppb1);
  pg1->pp = (void **)&s;
  pg3->f = 4;
  pg4->pp = pg7->pp;
 L:
  if(((char*)*pg2->pp)[pg5->f]) {
    __VERIFIER_error();
  }
  if (pg7->f) {
    goto L;
  }
  int *q = &p;
  p = __VERIFIER_nondet_int();
  *q = 0;
  return p;
}

int main()
{
  if(test(0)) {
    __VERIFIER_error();
  }
  return 0;
}
