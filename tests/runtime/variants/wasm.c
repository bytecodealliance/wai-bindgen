#include <assert.h>
#include <imports.h>
#include <exports.h>

void exports_test_imports() {
  {
    imports_option_float32_t a;
    uint8_t r;
    a.is_some = true;
    a.val = 1;
    assert(imports_roundtrip_option(&a, &r) && r == 1);
    assert(r == 1);
    a.is_some = false;
    assert(!imports_roundtrip_option(&a, &r));
    a.is_some = true;
    a.val = 2;
    assert(imports_roundtrip_option(&a, &r) && r == 2);
  }


  {
    imports_result_u32_float32_t a;
    imports_result_float64_u8_t b;

    a.is_err = false;
    a.val.ok = 2;
    imports_roundtrip_result(&a, &b);
    assert(!b.is_err);
    assert(b.val.ok == 2.0);

    a.val.ok = 4;
    imports_roundtrip_result(&a, &b);
    assert(!b.is_err);
    assert(b.val.ok == 4);

    a.is_err = true;
    a.val.err = 5.3;
    imports_roundtrip_result(&a, &b);
    assert(b.is_err);
    assert(b.val.err == 5);
  }

  assert(imports_roundtrip_enum(IMPORTS_E1_A) == IMPORTS_E1_A);
  assert(imports_roundtrip_enum(IMPORTS_E1_B) == IMPORTS_E1_B);

  assert(imports_invert_bool(true) == false);
  assert(imports_invert_bool(false) == true);

  {
    imports_casts_t c, ret;
    c.f0.tag = IMPORTS_C1_A;
    c.f0.val.a = 1;
    c.f1.tag = IMPORTS_C2_A;
    c.f1.val.a = 2;
    c.f2.tag = IMPORTS_C3_A;
    c.f2.val.a = 3;
    c.f3.tag = IMPORTS_C4_A;
    c.f3.val.a = 4;
    c.f4.tag = IMPORTS_C5_A;
    c.f4.val.a = 5;
    c.f5.tag = IMPORTS_C6_A;
    c.f5.val.a = 6;
    imports_variant_casts(&c, &ret);
    assert(ret.f0.tag == IMPORTS_C1_A && ret.f0.val.a == 1);
    assert(ret.f1.tag == IMPORTS_C2_A && ret.f1.val.a == 2);
    assert(ret.f2.tag == IMPORTS_C3_A && ret.f2.val.a == 3);
    assert(ret.f3.tag == IMPORTS_C4_A && ret.f3.val.a == 4);
    assert(ret.f4.tag == IMPORTS_C5_A && ret.f4.val.a == 5);
    assert(ret.f5.tag == IMPORTS_C6_A && ret.f5.val.a == 6);
  }

  {
    imports_casts_t c, ret;
    c.f0.tag = IMPORTS_C1_B;
    c.f0.val.b = 1;
    c.f1.tag = IMPORTS_C2_B;
    c.f1.val.b = 2;
    c.f2.tag = IMPORTS_C3_B;
    c.f2.val.b = 3;
    c.f3.tag = IMPORTS_C4_B;
    c.f3.val.b = 4;
    c.f4.tag = IMPORTS_C5_B;
    c.f4.val.b = 5;
    c.f5.tag = IMPORTS_C6_B;
    c.f5.val.b = 6;
    imports_variant_casts(&c, &ret);
    assert(ret.f0.tag == IMPORTS_C1_B && ret.f0.val.b == 1);
    assert(ret.f1.tag == IMPORTS_C2_B && ret.f1.val.b == 2);
    assert(ret.f2.tag == IMPORTS_C3_B && ret.f2.val.b == 3);
    assert(ret.f3.tag == IMPORTS_C4_B && ret.f3.val.b == 4);
    assert(ret.f4.tag == IMPORTS_C5_B && ret.f4.val.b == 5);
    assert(ret.f5.tag == IMPORTS_C6_B && ret.f5.val.b == 6);
  }

  {
    imports_zeros_t c, ret;
    c.f0.tag = IMPORTS_Z1_A;
    c.f0.val.a = 1;
    c.f1.tag = IMPORTS_Z2_A;
    c.f1.val.a = 2;
    c.f2.tag = IMPORTS_Z3_A;
    c.f2.val.a = 3;
    c.f3.tag = IMPORTS_Z4_A;
    c.f3.val.a = 4;
    imports_variant_zeros(&c, &ret);
    assert(ret.f0.tag == IMPORTS_Z1_A && ret.f0.val.a == 1);
    assert(ret.f1.tag == IMPORTS_Z2_A && ret.f1.val.a == 2);
    assert(ret.f2.tag == IMPORTS_Z3_A && ret.f2.val.a == 3);
    assert(ret.f3.tag == IMPORTS_Z4_A && ret.f3.val.a == 4);
  }

  {
    imports_zeros_t c, ret;
    c.f0.tag = IMPORTS_Z1_B;
    c.f1.tag = IMPORTS_Z2_B;
    c.f2.tag = IMPORTS_Z3_B;
    c.f3.tag = IMPORTS_Z4_B;
    imports_variant_zeros(&c, &ret);
    assert(ret.f0.tag == IMPORTS_Z1_B);
    assert(ret.f1.tag == IMPORTS_Z2_B);
    assert(ret.f2.tag == IMPORTS_Z3_B);
    assert(ret.f3.tag == IMPORTS_Z4_B);
  }

  {
    imports_option_typedef_t a;
    a.is_some = false;
    bool b = false;
    imports_result_typedef_t c;
    c.is_err = true;
    imports_variant_typedefs(&a, b, &c);
  }

  {
    imports_tuple3_bool_result_void_void_my_errno_t ret;
    imports_result_void_void_t b;
    b.is_err = false;
    imports_variant_enums(true, &b, IMPORTS_MY_ERRNO_SUCCESS, &ret);
    assert(ret.f0 == false);
    assert(ret.f1.is_err);
    assert(ret.f2 == IMPORTS_MY_ERRNO_A);
  }
}

bool exports_roundtrip_option(exports_option_float32_t *a, uint8_t *ret0) {
  if (a->is_some) {
    *ret0 = a->val;
  }
  return a->is_some;
}

void exports_roundtrip_result(exports_result_u32_float32_t *a, exports_result_float64_u8_t *ret0) {
  ret0->is_err = a->is_err;
  if (a->is_err) {
    ret0->val.err = a->val.err;
  } else {
    ret0->val.ok = a->val.ok;
  }
}

exports_e1_t exports_roundtrip_enum(exports_e1_t a) {
  return a;
}

bool exports_invert_bool(bool a) {
  return !a;
}

void exports_variant_casts(exports_casts_t *a, exports_casts_t *ret) {
  *ret = *a;
}

void exports_variant_zeros(exports_zeros_t *a, exports_zeros_t *b) {
  *b = *a;
}

void exports_variant_typedefs(exports_option_typedef_t *a, exports_bool_typedef_t b, exports_result_typedef_t *c) {
}

