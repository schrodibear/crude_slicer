
int main(void)
{
  int i;

  if (i == 0) {i++; i++; return 1;}
  else { }


  if (i == 0) {i++; i++; }
  else { }


  if (i == 0) {i++; i++; }
  else { }

  if (i == 0) {i++; i++; }
  else { }


  if (i == 0) {i++; i++; }
  else { }

    if (i == 0) {i++; i++; }
  else { }


  if (i == 0) {i++; i++; }
  else { }


 U:
  if (i == 1) {
  L0:
    if (i < 4)
      goto L0;
  } else if (i == 2) {
  L1:
    if (i < 4)
      goto L1;
  } else if (i == 3) {
  L2:
    if (i < 4)
      goto L2;
  } else if (i == 4) {
  L3:
    if (i < 4)
      goto L3;
  }

  if (i == 1) {
  L10:
    if (i < 4)
      goto L10;
  } else if (i == 2) {
  L11:
    if (i < 4)
      goto L11;
  } else if (i == 3) {
  L12:
    if (i < 4)
      goto L12;
  } else if (i == 4) {
  L13:
    if (i < 4)
      goto L13;
  }

  if (i < 6) goto U;

  return 0;
}
