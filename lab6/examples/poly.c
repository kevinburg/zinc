struct foo <a> {
  int x;
  a data;
};

a data(struct foo <a> *s) {
  return s->data;
}

int main() {
  struct foo <int> *s = alloc(struct foo <int>);
  s->x = 1;
  s->data = 2;
  return data(s);
}
