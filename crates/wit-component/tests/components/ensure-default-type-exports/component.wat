(component
  (type (;0;) u8)
  (type (;1;) (record (field "x" 0)))
  (type (;2;) (func (param "b" 1)))
  (type (;3;) 
    (instance
      (alias outer 1 2 (type (;0;)))
      (export "a" (func (type 0)))
    )
  )
  (export "foo" (type 0))
  (export "bar" (type 1))
  (import "foo" (instance (;0;) (type 3)))
  (core module (;0;)
    (type (;0;) (func (param i32)))
    (type (;1;) (func (param i32 i32 i32 i32) (result i32)))
    (import "foo" "a" (func (;0;) (type 0)))
    (func (;1;) (type 1) (param i32 i32 i32 i32) (result i32)
      unreachable
    )
    (func (;2;) (type 0) (param i32)
      unreachable
    )
    (memory (;0;) 1)
    (export "memory" (memory 0))
    (export "canonical_abi_realloc" (func 1))
    (export "a" (func 2))
  )
  (alias export 0 "a" (func (;0;)))
  (core func (;0;) (canon lower (func 0)))
  (core instance (;0;) 
    (export "a" (func 0))
  )
  (core instance (;1;) (instantiate 0
      (with "foo" (instance 0))
    )
  )
  (core alias export 1 "memory" (memory (;0;)))
  (core alias export 1 "canonical_abi_realloc" (func (;1;)))
  (core alias export 1 "a" (func (;2;)))
  (func (;1;) (type 2) (canon lift (core func 2)))
  (export "a" (func 1))
)