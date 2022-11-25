#include <assert.h>
#include <flavorful.h>
#include <stdlib.h>
#include <string.h>

void flavorful_test_imports() {
  {
    imports_list_in_record1_t a;
    flavorful_string_set(&a.a, "list_in_record1");
    imports_f_list_in_record1(&a);

    imports_list_in_record2_t b;
    imports_f_list_in_record2(&b);
    assert(memcmp(b.a.ptr, "list_in_record2", b.a.len) == 0);
    imports_list_in_record2_free(&b);
  }

  {
    imports_list_in_record3_t a;
    a.a.is_some = true;
    a.b.is_some = false;
    a.c.is_some = false;
    a.d.is_some = false;
    a.e.is_some = false;
    a.f.is_some = false;
    flavorful_string_set(&a.a.val, "list_in_record3 input");
    imports_result_list_in_record3_u32_t ret;
    imports_f_list_in_record3(&a, &ret);
    assert(memcmp(ret.val.ok.a.val.ptr, "list_in_record3 output", ret.val.ok.a.val.len) == 0);
    imports_list_in_record3_free(&ret.val.ok);
  }

  {
    imports_list_in_record4_t a, b;
    flavorful_string_set(&a.a, "input4");
    imports_f_list_in_record4(&a, &b);
    assert(memcmp(b.a.ptr, "result4", b.a.len) == 0);
    imports_list_in_record4_free(&b);
  }

  {
    imports_list_in_variant1_v1_t a;
    imports_list_in_variant1_v2_t b;
    imports_list_in_variant1_v3_t c;
    a.is_some = true;
    flavorful_string_set(&a.val, "foo");
    b.is_err = true;
    flavorful_string_set(&b.val.err, "bar");
    c.tag = 0;
    flavorful_string_set(&c.val.f0, "baz");
    imports_f_list_in_variant1(&a, &b, &c);
  }

  {
    flavorful_string_t a;
    assert(imports_f_list_in_variant2(&a));
    assert(memcmp(a.ptr, "list_in_variant2", a.len) == 0);
    flavorful_string_free(&a);
  }

  {
    imports_list_in_variant3_t a;
    a.is_some = true;
    flavorful_string_set(&a.val, "input3");
    flavorful_string_t b;
    assert(imports_f_list_in_variant3(&a, &b));
    assert(memcmp(b.ptr, "output3", b.len) == 0);
    flavorful_string_free(&b);
  }

  assert(imports_errno_result() == IMPORTS_MY_ERRNO_B);

  {
    flavorful_string_t a;
    flavorful_string_set(&a, "typedef1");
    flavorful_string_t b_str;
    flavorful_string_set(&b_str, "typedef2");
    imports_list_typedef3_t b;
    b.ptr = &b_str;
    b.len = 1;
    imports_list_typedef2_t c;
    imports_list_typedef3_t d;
    imports_list_typedefs(&a, &b, &c, &d);

    assert(memcmp(c.ptr, "typedef3", c.len) == 0);
    assert(d.len == 1);
    assert(memcmp(d.ptr[0].ptr, "typedef4", d.ptr[0].len) == 0);

    imports_list_typedef2_free(&c);
    imports_list_typedef3_free(&d);
  }

  {
    imports_list_bool_t a;
    bool a_val[] = {true, false};
    a.ptr = a_val;
    a.len = 2;

    imports_list_result_void_void_t b;
    imports_result_void_void_t b_val[2];
    b_val[0].is_err = false;
    b_val[1].is_err = true;
    b.ptr = b_val;
    b.len = 2;

    imports_list_my_errno_t c;
    imports_my_errno_t c_val[2];
    c_val[0] = IMPORTS_MY_ERRNO_SUCCESS;
    c_val[1] = IMPORTS_MY_ERRNO_A;
    c.ptr = c_val;
    c.len = 2;

    imports_list_bool_t d;
    imports_list_result_void_void_t e;
    imports_list_my_errno_t f;
    imports_list_of_variants(&a, &b, &c, &d, &e, &f);

    assert(d.len == 2);
    assert(d.ptr[0] == false);
    assert(d.ptr[1] == true);

    assert(e.len == 2);
    assert(e.ptr[0].is_err == true);
    assert(e.ptr[1].is_err == false);

    assert(f.len == 2);
    assert(f.ptr[0] == IMPORTS_MY_ERRNO_A);
    assert(f.ptr[1] == IMPORTS_MY_ERRNO_B);

    imports_list_bool_free(&d);
    imports_list_result_void_void_free(&e);
    imports_list_my_errno_free(&f);
  }
}

void flavorful_f_list_in_record1(flavorful_list_in_record1_t *a) {
  assert(memcmp(a->a.ptr, "list_in_record1", a->a.len) == 0);
  flavorful_list_in_record1_free(a);
}

void flavorful_f_list_in_record2(flavorful_list_in_record2_t *ret0) {
  flavorful_string_dup(&ret0->a, "list_in_record2");
}

void flavorful_f_list_in_record3(flavorful_list_in_record3_t *a, flavorful_list_in_record3_t *ret0) {
  assert(memcmp(a->a.ptr, "list_in_record3 input", a->a.len) == 0);
  flavorful_list_in_record3_free(a);
  flavorful_string_dup(&ret0->a, "list_in_record3 output");
}

void flavorful_f_list_in_record4(flavorful_list_in_alias_t *a, flavorful_list_in_alias_t *ret0) {
  assert(memcmp(a->a.ptr, "input4", a->a.len) == 0);
  flavorful_list_in_alias_free(a);
  flavorful_string_dup(&ret0->a, "result4");
}

void flavorful_f_list_in_variant1(flavorful_list_in_variant1_v1_t *a, flavorful_list_in_variant1_v2_t *b, flavorful_list_in_variant1_v3_t *c) {
  assert(a->is_some);
  assert(memcmp(a->val.ptr, "foo", a->val.len) == 0);
  flavorful_list_in_variant1_v1_free(a);

  assert(b->is_err);
  assert(memcmp(b->val.err.ptr, "bar", b->val.err.len) == 0);
  flavorful_list_in_variant1_v2_free(b);

  assert(c->tag == 0);
  assert(memcmp(c->val.f0.ptr, "baz", c->val.f0.len) == 0);
  flavorful_list_in_variant1_v3_free(c);
}

bool flavorful_f_list_in_variant2(flavorful_string_t *ret0) {
  flavorful_string_dup(ret0, "list_in_variant2");
  return true;
}

bool flavorful_f_list_in_variant3(flavorful_list_in_variant3_t *a, flavorful_string_t *ret0) {
  assert(a->is_some);
  assert(memcmp(a->val.ptr, "input3", a->val.len) == 0);
  flavorful_list_in_variant3_free(a);
  flavorful_string_dup(ret0, "output3");
  return true;
}

flavorful_my_errno_t flavorful_errno_result(void) {
  return FLAVORFUL_MY_ERRNO_B;
}

void flavorful_list_typedefs(flavorful_list_typedef_t *a, flavorful_list_typedef3_t *c, flavorful_list_typedef2_t *ret0, flavorful_list_typedef3_t *ret1) {
  assert(memcmp(a->ptr, "typedef1", a->len) == 0);
  flavorful_list_typedef_free(a);

  assert(c->len == 1);
  assert(memcmp(c->ptr[0].ptr, "typedef2", c->ptr[0].len) == 0);
  flavorful_list_typedef3_free(c);

  ret0->ptr = malloc(8);
  ret0->len = 8;
  memcpy(ret0->ptr, "typedef3", 8);

  ret1->ptr = malloc(sizeof(flavorful_string_t));
  ret1->len = 1;
  flavorful_string_dup(&ret1->ptr[0], "typedef4");
}
