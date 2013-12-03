struct foo <a> {
  int x;
  a y;
  int z;
};

int main() {
  struct foo <int> *s1 = alloc(struct foo <int>);
  struct foo <bool> *s2 = alloc(struct foo <bool>);
  s1->x = 1;
  s1->y = (s1->x)+1;
  s1->z = (s1->y)+1;
  s2->y = true;
  if (s2->y) {
    return s1->x + s1->y + s1->z;
  }
  return 0;
}
