use crate::csharp_ident::ToCSharpIdent;
use crate::interface::{InterfaceGenerator, ParameterType};
use crate::world_generator::CSharp;
use heck::ToUpperCamelCase;
use std::fmt::Write;
use std::mem;
use std::ops::Deref;
use wit_bindgen_core::abi::{Bindgen, Bitcast, Instruction};
use wit_bindgen_core::{uwrite, uwriteln, Direction, Ns};
use wit_parser::abi::WasmType;
use wit_parser::{
    Alignment, ArchitectureSize, Docs, FunctionKind, Handle, Resolve, SizeAlign, Type, TypeDefKind,
    TypeId,
};

/// FunctionBindgen generates the C# code for calling functions defined in wit
pub(crate) struct FunctionBindgen<'a, 'b> {
    pub(crate) interface_gen: &'b mut InterfaceGenerator<'a>,
    func_name: &'b str,
    kind: &'b FunctionKind,
    params: Box<[String]>,
    results: Vec<TypeId>,
    pub(crate) src: String,
    locals: Ns,
    block_storage: Vec<BlockStorage>,
    blocks: Vec<Block>,
    payloads: Vec<String>,
    pub(crate) needs_cleanup: bool,
    import_return_pointer_area_size: usize,
    import_return_pointer_area_align: usize,
    pub(crate) resource_drops: Vec<(String, String)>,
    is_block: bool,
    fixed_statments: Vec<Fixed>,
    parameter_type: ParameterType,
}

impl<'a, 'b> FunctionBindgen<'a, 'b> {
    pub(crate) fn new(
        interface_gen: &'b mut InterfaceGenerator<'a>,
        func_name: &'b str,
        kind: &'b FunctionKind,
        params: Box<[String]>,
        results: Vec<TypeId>,
        parameter_type: ParameterType,
    ) -> FunctionBindgen<'a, 'b> {
        let mut locals = Ns::default();
        // Ensure temporary variable names don't clash with parameter names:
        for param in &params[..] {
            locals.tmp(param);
        }

        Self {
            interface_gen,
            func_name,
            kind,
            params,
            results,
            src: String::new(),
            locals,
            block_storage: Vec::new(),
            blocks: Vec::new(),
            payloads: Vec::new(),
            needs_cleanup: false,
            import_return_pointer_area_size: 0,
            import_return_pointer_area_align: 0,
            resource_drops: Vec::new(),
            is_block: false,
            fixed_statments: Vec::new(),
            parameter_type: parameter_type,
        }
    }

    fn lower_variant(
        &mut self,
        cases: &[(&str, Option<Type>)],
        lowered_types: &[WasmType],
        op: &str,
        results: &mut Vec<String>,
    ) {
        let blocks = self
            .blocks
            .drain(self.blocks.len() - cases.len()..)
            .collect::<Vec<_>>();

        let payloads = self
            .payloads
            .drain(self.payloads.len() - cases.len()..)
            .collect::<Vec<_>>();

        let lowered = lowered_types
            .iter()
            .map(|_| self.locals.tmp("lowered"))
            .collect::<Vec<_>>();

        results.extend(lowered.iter().cloned());

        let declarations = lowered
            .iter()
            .zip(lowered_types)
            .map(|(lowered, ty)| format!("{} {lowered};", crate::world_generator::wasm_type(*ty)))
            .collect::<Vec<_>>()
            .join("\n");

        let cases = cases
            .iter()
            .zip(blocks)
            .zip(payloads)
            .enumerate()
            .map(
                |(i, (((name, ty), Block { body, results, .. }), payload))| {
                    let payload = if let Some(ty) = self.interface_gen.non_empty_type(ty.as_ref()) {
                        let ty = self.interface_gen.type_name_with_qualifier(ty, true);
                        let name = name.to_upper_camel_case();

                        format!("{ty} {payload} = {op}.As{name};")
                    } else {
                        String::new()
                    };

                    let assignments = lowered
                        .iter()
                        .zip(&results)
                        .map(|(lowered, result)| format!("{lowered} = {result};\n"))
                        .collect::<Vec<_>>()
                        .concat();

                    format!(
                        "case {i}: {{
                         {payload}
                         {body}
                         {assignments}
                         break;
                     }}"
                    )
                },
            )
            .collect::<Vec<_>>()
            .join("\n");

        uwrite!(
            self.src,
            r#"
            {declarations}

            switch ({op}.Tag) {{
                {cases}

                default: throw new ArgumentException($"invalid discriminant: {{{op}}}");
            }}
            "#
        );
    }

    fn lift_variant(
        &mut self,
        ty: &Type,
        cases: &[(&str, Option<Type>)],
        op: &str,
        results: &mut Vec<String>,
    ) {
        let blocks = self
            .blocks
            .drain(self.blocks.len() - cases.len()..)
            .collect::<Vec<_>>();
        let ty = self.interface_gen.type_name_with_qualifier(ty, true);
        //let ty = self.gen.type_name(ty);
        let generics_position = ty.find('<');
        let lifted = self.locals.tmp("lifted");

        let cases = cases
            .iter()
            .zip(blocks)
            .enumerate()
            .map(|(i, ((case_name, case_ty), Block { body, results, .. }))| {
                let payload = if self
                    .interface_gen
                    .non_empty_type(case_ty.as_ref())
                    .is_some()
                {
                    results.into_iter().next().unwrap()
                } else if generics_position.is_some() {
                    if let Some(ty) = case_ty.as_ref() {
                        format!(
                            "{}.INSTANCE",
                            self.interface_gen.type_name_with_qualifier(ty, true)
                        )
                    } else {
                        format!(
                            "new global::{}None()",
                            self.interface_gen.csharp_gen.qualifier()
                        )
                    }
                } else {
                    String::new()
                };

                let method = case_name.to_csharp_ident_upper();

                let call = if let Some(position) = generics_position {
                    let (ty, generics) = ty.split_at(position);
                    format!("{ty}{generics}.{method}")
                } else {
                    format!("{ty}.{method}")
                };

                format!(
                    "case {i}: {{
                         {body}
                         {lifted} = {call}({payload});
                         break;
                     }}"
                )
            })
            .collect::<Vec<_>>()
            .join("\n");

        uwrite!(
            self.src,
            r#"
            {ty} {lifted};

            switch ({op}) {{
                {cases}

                default: throw new ArgumentException($"invalid discriminant: {{{op}}}");
            }}
            "#
        );

        results.push(lifted);
    }

    fn handle_result_import(&mut self, operands: &mut Vec<String>) {
        if self.interface_gen.csharp_gen.opts.with_wit_results {
            uwriteln!(self.src, "return {};", operands[0]);
            return;
        }

        let mut payload_is_void = false;
        let mut previous = operands[0].clone();
        let mut vars: Vec<(String, Option<String>)> = Vec::with_capacity(self.results.len());
        if let Direction::Import = self.interface_gen.direction {
            for ty in &self.results {
                let tmp = self.locals.tmp("tmp");
                uwrite!(
                    self.src,
                    "\
                    if ({previous}.IsOk) 
                    {{
                        var {tmp} = {previous}.AsOk;
                    "
                );
                let TypeDefKind::Result(result) = &self.interface_gen.resolve.types[*ty].kind
                else {
                    unreachable!();
                };
                let exception_name = result
                    .err
                    .map(|ty| self.interface_gen.type_name_with_qualifier(&ty, true));
                vars.push((previous.clone(), exception_name));
                payload_is_void = result.ok.is_none();
                previous = tmp;
            }
        }
        uwriteln!(
            self.src,
            "return {};",
            if payload_is_void { "" } else { &previous }
        );
        for (level, var) in vars.iter().enumerate().rev() {
            self.interface_gen.csharp_gen.needs_wit_exception = true;
            let (var_name, exception_name) = var;
            let exception_name = match exception_name {
                Some(type_name) => &format!("WitException<{}>", type_name),
                None => "WitException",
            };
            uwrite!(
                self.src,
                "\
                }} 
                else 
                {{
                    throw new {exception_name}({var_name}.AsErr!, {level});
                }}
                "
            );
        }
    }

    fn handle_result_call(
        &mut self,
        func: &&wit_parser::Function,
        target: String,
        func_name: String,
        oper: String,
    ) -> String {
        let ret = self.locals.tmp("ret");
        if self.interface_gen.csharp_gen.opts.with_wit_results {
            uwriteln!(self.src, "var {ret} = {target}.{func_name}({oper});");
            return ret;
        }

        // otherwise generate exception code
        let ty = self
            .interface_gen
            .type_name_with_qualifier(func.results.iter_types().next().unwrap(), true);
        uwriteln!(self.src, "{ty} {ret};");
        let mut cases = Vec::with_capacity(self.results.len());
        let mut oks = Vec::with_capacity(self.results.len());
        let mut payload_is_void = false;
        for (index, ty) in self.results.iter().enumerate() {
            let TypeDefKind::Result(result) = &self.interface_gen.resolve.types[*ty].kind else {
                unreachable!();
            };
            let err_ty = if let Some(ty) = result.err {
                self.interface_gen.type_name_with_qualifier(&ty, true)
            } else {
                "None".to_owned()
            };
            let ty = self
                .interface_gen
                .type_name_with_qualifier(&Type::Id(*ty), true);
            let head = oks.concat();
            let tail = oks.iter().map(|_| ")").collect::<Vec<_>>().concat();
            cases.push(format!(
                "\
                case {index}: 
                {{
                    ret = {head}{ty}.Err(({err_ty}) e.Value){tail};
                    break;
                }}
                "
            ));
            oks.push(format!("{ty}.Ok("));
            payload_is_void = result.ok.is_none();
        }
        if !self.results.is_empty() {
            self.src.push_str(
                "
                try 
                {\n
                ",
            );
        }
        let head = oks.concat();
        let tail = oks.iter().map(|_| ")").collect::<Vec<_>>().concat();
        let val = if payload_is_void {
            uwriteln!(self.src, "{target}.{func_name}({oper});");
            "new None()".to_owned()
        } else {
            format!("{target}.{func_name}({oper})")
        };
        uwriteln!(self.src, "{ret} = {head}{val}{tail};");
        if !self.results.is_empty() {
            self.interface_gen.csharp_gen.needs_wit_exception = true;
            let cases = cases.join("\n");
            uwriteln!(
                self.src,
                r#"}} 
                    catch (WitException e) 
                    {{
                        switch (e.NestingLevel) 
                        {{
                            {cases}

                            default: throw new ArgumentException($"invalid nesting level: {{e.NestingLevel}}");
                        }}
                    }}
                "#
            );
        }
        ret
    }
}

impl Bindgen for FunctionBindgen<'_, '_> {
    type Operand = String;

    fn emit(
        &mut self,
        _resolve: &Resolve,
        inst: &Instruction<'_>,
        operands: &mut Vec<String>,
        results: &mut Vec<String>,
    ) {
        match inst {
            Instruction::GetArg { nth } => results.push(self.params[*nth].clone()),
            Instruction::I32Const { val } => results.push(val.to_string()),
            Instruction::ConstZero { tys } => results.extend(tys.iter().map(|ty| {
                match ty {
                    WasmType::I32 => "0",
                    WasmType::I64 => "0L",
                    WasmType::F32 => "0.0F",
                    WasmType::F64 => "0.0D",
                    WasmType::Pointer => "0",
                    WasmType::PointerOrI64 => "0L",
                    WasmType::Length => "0",
                }
                .to_owned()
            })),
            Instruction::I32Load { offset }
            | Instruction::PointerLoad { offset }
            | Instruction::LengthLoad { offset } => results.push(format!("BitConverter.ToInt32(new Span<byte>((void*)({} + {offset}), 4))",operands[0],offset = offset.size_wasm32())),
            Instruction::I32Load8U { offset } => results.push(format!("new Span<byte>((void*)({} + {offset}), 1)[0]",operands[0],offset = offset.size_wasm32())),
            Instruction::I32Load8S { offset } => results.push(format!("(sbyte)new Span<byte>((void*)({} + {offset}), 1)[0]",operands[0],offset = offset.size_wasm32())),
            Instruction::I32Load16U { offset } => results.push(format!("BitConverter.ToUInt16(new Span<byte>((void*)({} + {offset}), 2))",operands[0],offset = offset.size_wasm32())),
            Instruction::I32Load16S { offset } => results.push(format!("BitConverter.ToInt16(new Span<byte>((void*)({} + {offset}), 2))",operands[0],offset = offset.size_wasm32())),
            Instruction::I64Load { offset } => results.push(format!("BitConverter.ToInt64(new Span<byte>((void*)({} + {offset}), 8))",operands[0],offset = offset.size_wasm32())),
            Instruction::F32Load { offset } => results.push(format!("BitConverter.ToSingle(new Span<byte>((void*)({} + {offset}), 4))",operands[0],offset = offset.size_wasm32())),
            Instruction::F64Load { offset } => results.push(format!("BitConverter.ToDouble(new Span<byte>((void*)({} + {offset}), 8))",operands[0],offset = offset.size_wasm32())),
            Instruction::I32Store { offset }
            | Instruction::PointerStore { offset }
            | Instruction::LengthStore { offset } => uwriteln!(self.src, "BitConverter.TryWriteBytes(new Span<byte>((void*)({} + {offset}), 4), {});", operands[1], operands[0],offset = offset.size_wasm32()),
            Instruction::I32Store8 { offset } => uwriteln!(self.src, "*(byte*)({} + {offset}) = (byte){};", operands[1], operands[0],offset = offset.size_wasm32()),
            Instruction::I32Store16 { offset } => uwriteln!(self.src, "BitConverter.TryWriteBytes(new Span<byte>((void*)({} + {offset}), 2), (short){});", operands[1], operands[0],offset = offset.size_wasm32()),
            Instruction::I64Store { offset } => uwriteln!(self.src, "BitConverter.TryWriteBytes(new Span<byte>((void*)({} + {offset}), 8), unchecked((long){}));", operands[1], operands[0],offset = offset.size_wasm32()),
            Instruction::F32Store { offset } => uwriteln!(self.src, "BitConverter.TryWriteBytes(new Span<byte>((void*)({} + {offset}), 4), unchecked((float){}));", operands[1], operands[0],offset = offset.size_wasm32()),
            Instruction::F64Store { offset } => uwriteln!(self.src, "BitConverter.TryWriteBytes(new Span<byte>((void*)({} + {offset}), 8), unchecked((double){}));", operands[1], operands[0],offset = offset.size_wasm32()),

            Instruction::I64FromU64 => results.push(format!("unchecked((long)({}))", operands[0])),
            Instruction::I32FromChar => results.push(format!("((int){})", operands[0])),
            Instruction::I32FromU32 => results.push(format!("unchecked((int)({}))", operands[0])),
            Instruction::U8FromI32 => results.push(format!("((byte){})", operands[0])),
            Instruction::S8FromI32 => results.push(format!("((sbyte){})", operands[0])),
            Instruction::U16FromI32 => results.push(format!("((ushort){})", operands[0])),
            Instruction::S16FromI32 => results.push(format!("((short){})", operands[0])),
            Instruction::U32FromI32 => results.push(format!("unchecked((uint)({}))", operands[0])),
            Instruction::U64FromI64 => results.push(format!("unchecked((ulong)({}))", operands[0])),
            Instruction::CharFromI32 => results.push(format!("unchecked((uint)({}))", operands[0])),

            Instruction::I64FromS64
            | Instruction::I32FromU16
            | Instruction::I32FromS16
            | Instruction::I32FromU8
            | Instruction::I32FromS8
            | Instruction::I32FromS32
            | Instruction::F32FromCoreF32
            | Instruction::CoreF32FromF32
            | Instruction::CoreF64FromF64
            | Instruction::F64FromCoreF64
            | Instruction::S32FromI32
            | Instruction::S64FromI64 => results.push(operands[0].clone()),

            Instruction::Bitcasts { casts } => {
                results.extend(casts.iter().zip(operands).map(|(cast, op)| perform_cast(op, cast)))
            }

            Instruction::I32FromBool => {
                results.push(format!("({} ? 1 : 0)", operands[0]));
            }
            Instruction::BoolFromI32 => results.push(format!("({} != 0)", operands[0])),

            Instruction::FlagsLower {
                flags,
                name: _,
                ty: _,
            } => {
                if flags.flags.len() > 32 {
                    results.push(format!(
                        "unchecked((int)(((long){}) & uint.MaxValue))",
                        operands[0].to_string()
                    ));
                    results.push(format!(
                        "unchecked(((int)((long){} >> 32)))",
                        operands[0].to_string()
                    ));
                } else {
                    results.push(format!("(int){}", operands[0].to_string()));
                }
            }

            Instruction::FlagsLift { flags, name, ty } => {
                let qualified_type_name = format!(
                    "{}{}",
                    self.interface_gen.qualifier(true, ty),
                    name.to_string().to_upper_camel_case()
                );
                if flags.flags.len() > 32 {
                    results.push(format!(
                        "({})(unchecked((uint)({})) | (ulong)(unchecked((uint)({}))) << 32)",
                        qualified_type_name,
                        operands[0].to_string(),
                        operands[1].to_string()
                    ));
                } else {
                    results.push(format!("({})({})", qualified_type_name, operands[0]))
                }
            }

            Instruction::RecordLower { record, .. } => {
                let op = &operands[0];
                for f in record.fields.iter() {
                    results.push(format!("{}.{}", op, f.name.to_csharp_ident()));
                }
            }
            Instruction::RecordLift { ty, name, .. } => {
                let qualified_type_name = format!(
                    "{}{}",
                    self.interface_gen.qualifier(true, ty),
                    name.to_string().to_upper_camel_case()
                );
                let mut result = format!("new {} (\n", qualified_type_name);

                result.push_str(&operands.join(", "));
                result.push_str(")");

                results.push(result);
            }
            Instruction::TupleLift { .. } => {
                results.push(format!("({})", operands.join(", ")));
            }

            Instruction::TupleLower { tuple, ty: _ } => {
                let op = &operands[0];
                match tuple.types.len() {
                    1 => results.push(format!("({})", op)),
                    _ => {
                        for i in 0..tuple.types.len() {
                            results.push(format!("{}.Item{}", op, i + 1));
                        }
                    }
                }
            }

            Instruction::VariantPayloadName => {
                let payload = self.locals.tmp("payload");
                results.push(payload.clone());
                self.payloads.push(payload);
            }

            Instruction::VariantLower {
                variant,
                results: lowered_types,
                ..
            } => self.lower_variant(
                &variant
                    .cases
                    .iter()
                    .map(|case| (case.name.deref(), case.ty))
                    .collect::<Vec<_>>(),
                lowered_types,
                &operands[0],
                results,
            ),

            Instruction::VariantLift { variant, ty, .. } => self.lift_variant(
                &Type::Id(*ty),
                &variant
                    .cases
                    .iter()
                    .map(|case| (case.name.deref(), case.ty))
                    .collect::<Vec<_>>(),
                &operands[0],
                results,
            ),

            Instruction::OptionLower {
                results: lowered_types,
                payload,
                ..
            } => {
                let some = self.blocks.pop().unwrap();
                let none = self.blocks.pop().unwrap();
                let some_payload = self.payloads.pop().unwrap();
                let none_payload = self.payloads.pop().unwrap();

                let lowered = lowered_types
                    .iter()
                    .map(|_| self.locals.tmp("lowered"))
                    .collect::<Vec<_>>();

                results.extend(lowered.iter().cloned());

                let declarations = lowered
                    .iter()
                    .zip(lowered_types.iter())
                    .map(|(lowered, ty)| format!("{} {lowered};", crate::world_generator::wasm_type(*ty)))
                    .collect::<Vec<_>>()
                    .join("\n");

                let op = &operands[0];

                let nesting = if let Type::Id(id) = payload {
                    matches!(&self.interface_gen.resolve.types[*id].kind, TypeDefKind::Option(_))
                } else {
                    false
                };

                let mut block = |ty: Option<&Type>, Block { body, results, .. }, payload, nesting| {
                    let payload = if let Some(ty) = self.interface_gen.non_empty_type(ty) {
                        let ty = self.interface_gen.type_name_with_qualifier(ty, true);
                        if nesting {
                            format!("var {payload} = {op}.Value;")
                        } else {
                            format!("var {payload} = ({ty}) {op};")
                        }
                    } else {
                        String::new()
                    };

                    let assignments = lowered
                        .iter()
                        .zip(&results)
                        .map(|(lowered, result)| format!("{lowered} = {result};\n"))
                        .collect::<Vec<_>>()
                        .concat();

                    format!(
                        "{payload}
                         {body}
                         {assignments}"
                    )
                };

                let none = block(None, none, none_payload, nesting);
                let some = block(Some(payload), some, some_payload, nesting);

                let test = if nesting {
                    ".HasValue"
                } else {
                    " != null"
                };

                uwrite!(
                    self.src,
                    r#"
                    {declarations}

                    if ({op}{test}) {{
                        {some}
                    }} else {{
                        {none}
                    }}
                    "#
                );
            }

            Instruction::OptionLift { payload, ty } => {
                let some = self.blocks.pop().unwrap();
                let _none = self.blocks.pop().unwrap();

                let ty = self.interface_gen.type_name_with_qualifier(&Type::Id(*ty), true);
                let lifted = self.locals.tmp("lifted");
                let op = &operands[0];

                let nesting = if let Type::Id(id) = payload {
                    matches!(&self.interface_gen.resolve.types[*id].kind, TypeDefKind::Option(_))
                } else {
                    false
                };

                let payload = if self.interface_gen.non_empty_type(Some(*payload)).is_some() {
                    some.results.into_iter().next().unwrap()
                } else {
                    "null".into()
                };

                let some = some.body;

                let (none_value, some_value) = if nesting {
                    (format!("{ty}.None"), format!("new ({payload})"))
                } else {
                    ("null".into(), payload)
                };

                uwrite!(
                    self.src,
                    r#"
                    {ty} {lifted};

                    switch ({op}) {{
                        case 0: {{
                            {lifted} = {none_value};
                            break;
                        }}

                        case 1: {{
                            {some}
                            {lifted} = {some_value};
                            break;
                        }}

                        default: throw new ArgumentException("invalid discriminant: " + ({op}));
                    }}
                    "#
                );

                results.push(lifted);
            }

            Instruction::ResultLower {
                results: lowered_types,
                result,
                ..
            } => self.lower_variant(
                &[("Ok", result.ok), ("Err", result.err)],
                lowered_types,
                &operands[0],
                results,
            ),

            Instruction::ResultLift { result, ty } => self.lift_variant(
                &Type::Id(*ty),
                &[("Ok", result.ok), ("Err", result.err)],
                &operands[0],
                results,
            ),

            Instruction::EnumLower { .. } => results.push(format!("(int){}", operands[0])),

            Instruction::EnumLift { ty, .. } => {
                let t = self.interface_gen.type_name_with_qualifier(&Type::Id(*ty), true);
                let op = &operands[0];
                results.push(format!("({}){}", t, op));

                // uwriteln!(
                //    self.src,
                //    "Debug.Assert(Enum.IsDefined(typeof({}), {}));",
                //    t,
                //    op
                // );
            }

            Instruction::ListCanonLower { element, .. } => {
                let list: &String = &operands[0];
                match self.interface_gen.direction {
                    Direction::Import => {
                        let ptr: String = self.locals.tmp("listPtr");
                        let handle: String = self.locals.tmp("gcHandle");

                        if !self.is_block && self.parameter_type == ParameterType::Span {
                            self.fixed_statments.push(Fixed {
                                item_to_pin: list.clone(),
                                ptr_name: ptr.clone(),
                            });
                        }else if !self.is_block && self.parameter_type == ParameterType::Memory {
                            self.fixed_statments.push(Fixed {
                                item_to_pin: format!("{list}.Span"),
                                ptr_name: ptr.clone(),
                            });
                        } else {
                            // With variants we can't use span since the Fixed statment can't always be applied to all the variants
                            // Despite the name GCHandle.Alloc here this does not re-allocate the object but it does make an
                            // allocation for the handle in a special resource pool which can result in GC pressure.
                            // It pins the array with the garbage collector so that it can be passed to unmanaged code.
                            // It is required to free the pin after use which is done in the Cleanup section.
                            self.needs_cleanup = true;
                            uwrite!(
                                self.src,
                                "
                                var {handle} = GCHandle.Alloc({list}, GCHandleType.Pinned);
                                var {ptr} = {handle}.AddrOfPinnedObject();
                                cleanups.Add(()=> {handle}.Free());
                                "
                            );
                        }
                        results.push(format!("(nint){ptr}")); 
                        results.push(format!("({list}).Length"));
                    }
                    Direction::Export => {
                        let (_, ty) = list_element_info(element);
                        let address = self.locals.tmp("address");
                        let size = self.interface_gen.csharp_gen.sizes.size(element).size_wasm32();
                        let byte_length = self.locals.tmp("byteLength");
                        uwrite!(
                            self.src,
                            "
                            var {byte_length} = ({size}) * {list}.Length;
                            var {address} = NativeMemory.Alloc((nuint)({byte_length}));
                            {list}.AsSpan().CopyTo(new Span<{ty}>({address},{byte_length}));
                            "
                        );

                        results.push(format!("(int)({address})"));
                        results.push(format!("{list}.Length"));
                    }
                }
            }

            Instruction::ListCanonLift { element, .. } => {
                let (_, ty) = list_element_info(element);
                let array = self.locals.tmp("array");
                let address = &operands[0];
                let length = &operands[1];

                uwrite!(
                    self.src,
                    "
                    var {array} = new {ty}[{length}];
                    new Span<{ty}>((void*)({address}), {length}).CopyTo(new Span<{ty}>({array}));
                    "
                );

                results.push(array);
            }

            Instruction::StringLower { realloc } => {
                let op = &operands[0];
                let str_ptr = self.locals.tmp("strPtr");
                let utf8_bytes = self.locals.tmp("utf8Bytes");
                let length = self.locals.tmp("length");
                let gc_handle = self.locals.tmp("gcHandle");

                if realloc.is_none() {
                    uwriteln!(
                        self.src,
                        "
                        var {utf8_bytes} = Encoding.UTF8.GetBytes({op});
                        var {length} = {utf8_bytes}.Length;
                        var {gc_handle} = GCHandle.Alloc({utf8_bytes}, GCHandleType.Pinned);
                        var {str_ptr} = {gc_handle}.AddrOfPinnedObject();
                        "
                    );

                    self.needs_cleanup = true;
                    uwrite!(
                        self.src,
                        "
                        cleanups.Add(()=> {gc_handle}.Free());
                        "
                    );
                    results.push(format!("{str_ptr}.ToInt32()"));
                } else {
                    let string_span = self.locals.tmp("stringSpan");
                    uwriteln!(
                        self.src,
                        "
                        var {string_span} = {op}.AsSpan();
                        var {length} = Encoding.UTF8.GetByteCount({string_span});
                        var {str_ptr} = NativeMemory.Alloc((nuint){length});
                        Encoding.UTF8.GetBytes({string_span}, new Span<byte>({str_ptr}, {length}));
                        "
                    );
                    results.push(format!("(int){str_ptr}"));
                }

                results.push(format!("{length}"));
                if FunctionKind::Freestanding == *self.kind || self.interface_gen.direction == Direction::Export {
                    self.interface_gen.require_interop_using("System.Text");
                    self.interface_gen.require_interop_using("System.Runtime.InteropServices");
                } else {
                    self.interface_gen.require_using("System.Text");
                    self.interface_gen.require_using("System.Runtime.InteropServices");
                }
            }

            Instruction::StringLift { .. } => {
                if FunctionKind::Freestanding == *self.kind || self.interface_gen.direction == Direction::Export {
                    self.interface_gen.require_interop_using("System.Text");
                } else {
                    self.interface_gen.require_using("System.Text");
                }

                results.push(format!(
                    "Encoding.UTF8.GetString((byte*){}, {})",
                    operands[0], operands[1]
                ));
            }

            Instruction::ListLower { element, realloc } => {
                let Block {
                    body,
                    results: block_results,
                    element: block_element,
                    base,
                } = self.blocks.pop().unwrap();
                assert!(block_results.is_empty());

                let list = &operands[0];
                let size = self.interface_gen.csharp_gen.sizes.size(element).size_wasm32();
                let ty = self.interface_gen.type_name_with_qualifier(element, true);
                let index = self.locals.tmp("index");

                let address = self.locals.tmp("address");
                let buffer_size = self.locals.tmp("bufferSize");
                //TODO: wasm64
                let align = self.interface_gen.csharp_gen.sizes.align(element).align_wasm32();

                let (array_size, element_type) = crate::world_generator::dotnet_aligned_array(
                    size,
                    align,
                );
                let ret_area = self.locals.tmp("retArea");

                match realloc {
                    None => {
                        self.needs_cleanup = true;
                        uwrite!(self.src,
                            "
                            void* {address};
                            if (({size} * {list}.Count) < 1024) {{
                                var {ret_area} = stackalloc {element_type}[({array_size}*{list}.Count)+1];
                                {address} = (void*)(((int){ret_area}) + ({align} - 1) & -{align});
                            }} 
                            else
                            {{
                                var {buffer_size} = {size} * (nuint){list}.Count;
                                {address} = NativeMemory.AlignedAlloc({buffer_size}, {align});
                                cleanups.Add(() => NativeMemory.AlignedFree({address}));
                            }}
                            "
                        );
                    }
                    Some(_) => {
                        //cabi_realloc_post_return will be called to clean up this allocation
                        uwrite!(self.src,
                            "
                            var {buffer_size} = {size} * (nuint){list}.Count;
                            void* {address} = NativeMemory.AlignedAlloc({buffer_size}, {align});
                            "
                        );
                    }
                }

                uwrite!(self.src,
                    "
                    for (int {index} = 0; {index} < {list}.Count; ++{index}) {{
                        {ty} {block_element} = {list}[{index}];
                        int {base} = (int){address} + ({index} * {size});
                        {body}
                    }}
                    "
                );

                results.push(format!("(int){address}"));
                results.push(format!("{list}.Count"));
            }

            Instruction::ListLift { element, .. } => {
                let Block {
                    body,
                    results: block_results,
                    base,
                    ..
                } = self.blocks.pop().unwrap();
                let address = &operands[0];
                let length = &operands[1];
                let array = self.locals.tmp("array");
                let ty = self.interface_gen.type_name_with_qualifier(element, true);
                let size = self.interface_gen.csharp_gen.sizes.size(element).size_wasm32();
                let index = self.locals.tmp("index");

                let result = match &block_results[..] {
                    [result] => result,
                    _ => todo!("result count == {}", results.len()),
                };

                uwrite!(
                    self.src,
                    "
                    var {array} = new List<{ty}>({length});
                    for (int {index} = 0; {index} < {length}; ++{index}) {{
                        nint {base} = {address} + ({index} * {size});
                        {body}
                        {array}.Add({result});
                    }}
                    "
                );

                results.push(array);
            }

            Instruction::IterElem { .. } => {
                results.push(self.block_storage.last().unwrap().element.clone())
            }

            Instruction::IterBasePointer => {
                results.push(self.block_storage.last().unwrap().base.clone())
            }

            Instruction::CallWasm { sig, .. } => {
                let assignment = match &sig.results[..] {
                    [_] => {
                        let result = self.locals.tmp("result");
                        let assignment = format!("var {result} = ");
                        results.push(result);
                        assignment
                    }

                    [] => String::new(),

                    _ => unreachable!(),
                };

                let func_name = self.func_name.to_upper_camel_case();

                let operands = operands.join(", ");

                uwriteln!(
                    self.src,
                    "{assignment} {func_name}WasmInterop.wasmImport{func_name}({operands});"
                );
            }

            Instruction::CallInterface { func, .. } => {
                let module = self.interface_gen.name;
                let func_name = self.func_name.to_upper_camel_case();
                let interface_name = CSharp::get_class_name_from_qualified_name(module).1;

                let class_name_root = interface_name
                    .strip_prefix("I")
                    .unwrap()
                    .to_upper_camel_case();

                let mut oper = String::new();

                for (i, param) in operands.iter().enumerate() {
                    if i == 0 && matches!(self.kind, FunctionKind::Method(_)) {
                        continue;
                    }

                    oper.push_str(&format!("({param})"));

                    if i < operands.len() && operands.len() != i + 1 {
                        oper.push_str(", ");
                    }
                }

                match self.kind {
                    FunctionKind::Freestanding | FunctionKind::Static(_) | FunctionKind::Method(_) => {
                        let target = match self.kind {
                            FunctionKind::Static(id) => self.interface_gen.csharp_gen.all_resources[id].export_impl_name(),
                            FunctionKind::Method(_) => operands[0].clone(),
                            _ => format!("{class_name_root}Impl")
                        };

                        match func.results.len() {
                            0 => uwriteln!(self.src, "{target}.{func_name}({oper});"),
                            1 => {
                                let ret = self.handle_result_call(func, target, func_name, oper);
                                results.push(ret);
                            }
                            _ => {
                                let ret = self.locals.tmp("ret");
                                uwriteln!(
                                    self.src,
                                    "var {ret} = {target}.{func_name}({oper});"
                                );
                                let mut i = 1;
                                for _ in func.results.iter_types() {
                                    results.push(format!("{ret}.Item{i}"));
                                    i += 1;
                                }
                            }
                        }
                    }
                    FunctionKind::Constructor(id) => {
                        let target = self.interface_gen.csharp_gen.all_resources[id].export_impl_name();
                        let ret = self.locals.tmp("ret");
                        uwriteln!(self.src, "var {ret} = new {target}({oper});");
                        results.push(ret);
                    }
                }

                for (_,  drop) in &self.resource_drops {
                    uwriteln!(self.src, "{drop}?.Dispose();");
                }
            }

            Instruction::Return { amt, .. } => {
                if self.fixed_statments.len() > 0 {
                    let fixed: String = self.fixed_statments.iter().map(|f| format!("{} = {}", f.ptr_name, f.item_to_pin)).collect::<Vec<_>>().join(", ");
                    self.src.insert_str(0, &format!("fixed (void* {fixed})
                        {{
                        "));
                }

                if self.needs_cleanup {
                    self.src.insert_str(0, "var cleanups = new List<Action>();
                        ");

                    uwriteln!(self.src, "
                    foreach (var cleanup in cleanups)
                    {{
                        cleanup();
                    }}");
                }

                if !matches!((self.interface_gen.direction, self.kind), (Direction::Import, FunctionKind::Constructor(_))) {
                    match *amt {
                        0 => (),
                        1 => {
                            self.handle_result_import(operands);
                        }
                        _ => {
                            let results: String = operands.join(", ");
                            uwriteln!(self.src, "return ({results});")
                        }
                    }
                }

                if self.fixed_statments.len() > 0 {
                    uwriteln!(self.src, "}}");
                }
            }

            Instruction::Malloc { .. } => unimplemented!(),

            Instruction::GuestDeallocate { .. } => {
                // the original alloc here comes from cabi_realloc implementation (wasi-libc in .net)
                uwriteln!(self.src, r#"NativeMemory.Free((void*){});"#, operands[0]);
            }

            Instruction::GuestDeallocateString => {
                uwriteln!(self.src, r#"NativeMemory.Free((void*){});"#, operands[0]);
            }

            Instruction::GuestDeallocateVariant { blocks } => {
                let cases = self
                    .blocks
                    .drain(self.blocks.len() - blocks..)
                    .enumerate()
                    .map(|(i, Block { body, results, .. })| {
                        assert!(results.is_empty());

                        format!(
                            "case {i}: {{
                                 {body}
                                 break;
                             }}"
                        )
                    })
                    .collect::<Vec<_>>()
                    .join("\n");

                    let op = &operands[0];

                    uwrite!(
                        self.src,
                        "
                        switch ({op}) {{
                            {cases}
                        }}
                        "
                    );
            }

            Instruction::GuestDeallocateList { element: element_type } => {
                let Block {
                    body,
                    results: block_results,
                    base,
                    element: _,
                } = self.blocks.pop().unwrap();
                assert!(block_results.is_empty());

                let address = &operands[0];
                let length = &operands[1];
                let size = self.interface_gen.csharp_gen.sizes.size(element_type).size_wasm32();

                if !body.trim().is_empty() {
                    let index = self.locals.tmp("index");

                    uwrite!(
                        self.src,
                        "
                        for (int {index} = 0; {index} < {length}; ++{index}) {{
                            int {base} = (int){address} + ({index} * {size});
                            {body}
                        }}
                        "
                    );
                }

                uwriteln!(self.src, r#"NativeMemory.Free((void*){});"#, operands[0]);
            }

            Instruction::HandleLower {
                handle,
                ..
            } => {
                let (Handle::Own(ty) | Handle::Borrow(ty)) = handle;
                let is_own = matches!(handle, Handle::Own(_));
                let handle = self.locals.tmp("handle");
                let id = dealias(self.interface_gen.resolve, *ty);
                let ResourceInfo { direction, .. } = &self.interface_gen.csharp_gen.all_resources[&id];
                let op = &operands[0];

                uwriteln!(self.src, "var {handle} = {op}.Handle;");

                match direction {
                    Direction::Import => {
                        if is_own {
                            uwriteln!(self.src, "{op}.Handle = 0;");
                        }
                    }
                    Direction::Export => {
                        self.interface_gen.csharp_gen.needs_rep_table = true;
                        let local_rep = self.locals.tmp("localRep");
                        let export_name = self.interface_gen.csharp_gen.all_resources[&id].export_impl_name();
                        if is_own {
                            // Note that we set `{op}.Handle` to zero below to ensure that application code doesn't
                            // try to use the instance while the host has ownership.  We'll set it back to non-zero
                            // if and when the host gives ownership back to us.
                            uwriteln!(
                                self.src,
                                "if ({handle} == 0) {{
                                     var {local_rep} = {export_name}.repTable.Add({op});
                                     {handle} = {export_name}.WasmInterop.wasmImportResourceNew({local_rep});
                                 }}
                                 {op}.Handle = 0;
                                 "
                            );
                        } else {
                            uwriteln!(
                                self.src,
                                "if ({handle} == 0) {{
                                     var {local_rep} = {export_name}.repTable.Add({op});
                                     {handle} = {export_name}.WasmInterop.wasmImportResourceNew({local_rep});
                                     {op}.Handle = {handle};
                                 }}"
                            );
                        }
                    }
                }
                results.push(format!("{handle}"));
            }

            Instruction::HandleLift {
                handle,
                ..
            } => {
                let (Handle::Own(ty) | Handle::Borrow(ty)) = handle;
                let is_own = matches!(handle, Handle::Own(_));
                let mut resource = self.locals.tmp("resource");
                let id = dealias(self.interface_gen.resolve, *ty);
                let ResourceInfo { direction, .. } = &self.interface_gen.csharp_gen.all_resources[&id];
                let op = &operands[0];

                match direction {
                    Direction::Import => {
                        let import_name = self.interface_gen.type_name_with_qualifier(&Type::Id(id), true);

                        if let FunctionKind::Constructor(_) = self.kind {
                            resource = "this".to_owned();
                            uwriteln!(self.src,"{resource}.Handle = {op};");
                        } else {
                            let var = if is_own { "var" } else { "" };
                            uwriteln!(
                                self.src,
                                "{var} {resource} = new {import_name}(new {import_name}.THandle({op}));"
                            );
                        }
                        if !is_own {
                            self.resource_drops.push((import_name, resource.clone()));
                        }
                    }
                    Direction::Export => {
                        self.interface_gen.csharp_gen.needs_rep_table = true;

                        let export_name = self.interface_gen.csharp_gen.all_resources[&id].export_impl_name();
                        if is_own {
                            uwriteln!(
                                self.src,
                                "var {resource} = ({export_name}) {export_name}.repTable.Get\
                                ({export_name}.WasmInterop.wasmImportResourceRep({op}));
                                {resource}.Handle = {op};"
                            );
                        } else {
                            uwriteln!(self.src, "var {resource} = ({export_name}) {export_name}.repTable.Get({op});");
                        }
                    }
                }
                results.push(resource);
            }

            Instruction::Flush { amt } => {
                results.extend(operands.iter().take(*amt).map(|v| v.clone()));
            }

            Instruction::AsyncMalloc { .. }
            | Instruction::AsyncPostCallInterface { .. }
            | Instruction::AsyncCallReturn { .. }
            | Instruction::FutureLower { .. }
            | Instruction::FutureLift { .. }
            | Instruction::StreamLower { .. }
            | Instruction::StreamLift { .. }
            | Instruction::ErrorContextLower { .. }
            | Instruction::ErrorContextLift { .. }
            | Instruction::AsyncCallWasm { .. } => todo!(),
        }
    }

    fn return_pointer(&mut self, size: ArchitectureSize, align: Alignment) -> String {
        let ptr = self.locals.tmp("ptr");

        match self.interface_gen.direction {
            Direction::Import => {
                self.import_return_pointer_area_size =
                    self.import_return_pointer_area_size.max(size.size_wasm32());
                self.import_return_pointer_area_align = self
                    .import_return_pointer_area_align
                    .max(align.align_wasm32());
                let (array_size, element_type) = crate::world_generator::dotnet_aligned_array(
                    self.import_return_pointer_area_size,
                    self.import_return_pointer_area_align,
                );
                let ret_area = self.locals.tmp("retArea");
                // We can use the stack here to get a return pointer when importing.
                // We do need to do a slight over-allocation since C# doesn't provide a way
                // to align the allocation via the stackalloc command, unlike with a fixed array where the pointer will be aligned.
                // We get the final ptr to pass to the wasm runtime by shifting to the
                // correctly aligned pointer (sometimes it can be already aligned).
                uwrite!(
                    self.src,
                    "
                    var {ret_area} = stackalloc {element_type}[{array_size}+1];
                    var {ptr} = ((int){ret_area}) + ({align} - 1) & -{align};
                    ",
                    align = align.align_wasm32()
                );
                format!("{ptr}")
            }
            Direction::Export => {
                // exports need their return area to be live until the post-return call.
                self.interface_gen.csharp_gen.return_area_size = self
                    .interface_gen
                    .csharp_gen
                    .return_area_size
                    .max(size.size_wasm32());
                self.interface_gen.csharp_gen.return_area_align = self
                    .interface_gen
                    .csharp_gen
                    .return_area_align
                    .max(align.align_wasm32());

                uwrite!(
                    self.src,
                    "
                    var {ptr} = InteropReturnArea.returnArea.AddressOfReturnArea();
                    "
                );
                self.interface_gen.csharp_gen.needs_export_return_area = true;

                format!("{ptr}")
            }
        }
    }

    fn push_block(&mut self) {
        self.block_storage.push(BlockStorage {
            body: mem::take(&mut self.src),
            element: self.locals.tmp("element"),
            base: self.locals.tmp("basePtr"),
        });

        self.is_block = true;
    }

    fn finish_block(&mut self, operands: &mut Vec<String>) {
        let BlockStorage {
            body,
            element,
            base,
        } = self.block_storage.pop().unwrap();

        self.blocks.push(Block {
            body: mem::replace(&mut self.src, body),
            results: mem::take(operands),
            element,
            base,
        });
        self.is_block = false;
    }

    fn sizes(&self) -> &SizeAlign {
        &self.interface_gen.csharp_gen.sizes
    }

    fn is_list_canonical(&self, _resolve: &Resolve, element: &Type) -> bool {
        crate::world_generator::is_primitive(element)
    }
}

/// Dereference any number `TypeDefKind::Type` aliases to retrieve the target type.
fn dealias(resolve: &Resolve, mut id: TypeId) -> TypeId {
    loop {
        match &resolve.types[id].kind {
            TypeDefKind::Type(Type::Id(that_id)) => id = *that_id,
            _ => break id,
        }
    }
}

fn list_element_info(ty: &Type) -> (usize, &'static str) {
    match ty {
        Type::S8 => (1, "sbyte"),
        Type::S16 => (2, "short"),
        Type::S32 => (4, "int"),
        Type::S64 => (8, "long"),
        Type::U8 => (1, "byte"),
        Type::U16 => (2, "ushort"),
        Type::U32 => (4, "uint"),
        Type::U64 => (8, "ulong"),
        Type::F32 => (4, "float"),
        Type::F64 => (8, "double"),
        _ => unreachable!(),
    }
}

fn perform_cast(op: &String, cast: &Bitcast) -> String {
    match cast {
        Bitcast::I32ToF32 => format!("BitConverter.Int32BitsToSingle((int){op})"),
        Bitcast::I64ToF32 => format!("BitConverter.Int32BitsToSingle((int){op})"),
        Bitcast::F32ToI32 => format!("BitConverter.SingleToInt32Bits({op})"),
        Bitcast::F32ToI64 => format!("BitConverter.SingleToInt32Bits({op})"),
        Bitcast::I64ToF64 => format!("BitConverter.Int64BitsToDouble({op})"),
        Bitcast::F64ToI64 => format!("BitConverter.DoubleToInt64Bits({op})"),
        Bitcast::I32ToI64 => format!("(long) ({op})"),
        Bitcast::I64ToI32 => format!("(int) ({op})"),
        Bitcast::I64ToP64 => format!("{op}"),
        Bitcast::P64ToI64 => format!("{op}"),
        Bitcast::LToI64 | Bitcast::PToP64 => format!("(long) ({op})"),
        Bitcast::I64ToL | Bitcast::P64ToP => format!("(int) ({op})"),
        Bitcast::I32ToP
        | Bitcast::PToI32
        | Bitcast::I32ToL
        | Bitcast::LToI32
        | Bitcast::LToP
        | Bitcast::PToL
        | Bitcast::None => op.to_owned(),
        Bitcast::Sequence(sequence) => {
            let [first, second] = &**sequence;
            perform_cast(&perform_cast(op, first), second)
        }
    }
}

struct Block {
    body: String,
    results: Vec<String>,
    element: String,
    base: String,
}

struct Fixed {
    item_to_pin: String,
    ptr_name: String,
}

struct BlockStorage {
    body: String,
    element: String,
    base: String,
}

#[derive(Clone)]
pub struct ResourceInfo {
    pub(crate) module: String,
    pub(crate) name: String,
    pub(crate) docs: Docs,
    pub(crate) direction: Direction,
}

impl ResourceInfo {
    /// Returns the name of the exported implementation of this resource.
    ///
    /// The result is only valid if the resource is actually being exported by the world.
    fn export_impl_name(&self) -> String {
        format!(
            "{}Impl.{}",
            CSharp::get_class_name_from_qualified_name(&self.module)
                .1
                .strip_prefix("I")
                .unwrap()
                .to_upper_camel_case(),
            self.name.to_upper_camel_case()
        )
    }
}
