void __VERIFIER_error();

void ldv_stop() {
 STOP: goto STOP;
}

int a;

void f() {
  a = 1;
  goto next;
  ldv_stop();
  next:
}

int main() {
   f();
   if (a == 1)
     __VERIFIER_error();
   return 0;
}
