use proc_macro::TokenStream;
use syn::parse::{Error, Parse, ParseStream, Result};
use syn::punctuated::Punctuated;
use syn::{token, Token};
use witx_bindgen_gen_core::{witx2, Files, Generator};
use witx_bindgen_gen_wasmtime::Async;

#[proc_macro]
pub fn import(input: TokenStream) -> TokenStream {
    run(input, true)
}

#[proc_macro]
pub fn export(input: TokenStream) -> TokenStream {
    run(input, false)
}

fn run(input: TokenStream, import: bool) -> TokenStream {
    let input = syn::parse_macro_input!(input as Opts);
    let mut gen = input.opts.build();
    let mut files = Files::default();
    for iface in input.interfaces {
        gen.generate(&iface, import, &mut files);
    }
    let (_, contents) = files.iter().next().unwrap();

    let mut header = "
        use witx_bindgen_wasmtime::{wasmtime, anyhow, bitflags};
    "
    .parse::<TokenStream>()
    .unwrap();
    let contents = std::str::from_utf8(contents).unwrap();
    let contents = contents.parse::<TokenStream>().unwrap();
    header.extend(contents);

    // Include a dummy `include_str!` for any files we read so rustc knows that
    // we depend on the contents of those files.
    let cwd = std::env::current_dir().unwrap();
    for file in input.files.iter() {
        header.extend(
            format!(
                "const _: &str = include_str!(\"{}\");\n",
                cwd.join(file).display()
            )
            .parse::<TokenStream>()
            .unwrap(),
        );
    }

    return header;
}

struct Opts {
    opts: witx_bindgen_gen_wasmtime::Opts,
    interfaces: Vec<witx2::Interface>,
    files: Vec<String>,
}

mod kw {
    syn::custom_keyword!(src);
    syn::custom_keyword!(paths);
}

impl Parse for Opts {
    fn parse(input: ParseStream<'_>) -> Result<Opts> {
        let call_site = proc_macro2::Span::call_site();
        let mut opts = witx_bindgen_gen_wasmtime::Opts::default();
        let mut files = Vec::new();
        opts.tracing = cfg!(feature = "tracing");

        let interfaces = if input.peek(token::Brace) {
            let content;
            syn::braced!(content in input);
            let mut interfaces = Vec::new();
            let fields = Punctuated::<ConfigField, Token![,]>::parse_terminated(&content)?;
            for field in fields.into_pairs() {
                match field.into_value() {
                    ConfigField::Interfaces(v) => interfaces = v,
                    ConfigField::Async(v) => opts.async_ = v,
                }
            }
            if interfaces.is_empty() {
                return Err(Error::new(
                    call_site,
                    "must either specify `src` or `paths` keys",
                ));
            }
            interfaces
        } else {
            while !input.is_empty() {
                let s = input.parse::<syn::LitStr>()?;
                files.push(s.value());
            }
            let mut interfaces = Vec::new();
            for path in files.iter() {
                let iface =
                    witx2::Interface::parse_file(path).map_err(|e| Error::new(call_site, e))?;
                interfaces.push(iface);
            }
            interfaces
        };
        Ok(Opts {
            opts,
            interfaces,
            files,
        })
    }
}

enum ConfigField {
    Interfaces(Vec<witx2::Interface>),
    Async(witx_bindgen_gen_wasmtime::Async),
}

impl Parse for ConfigField {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let l = input.lookahead1();
        if l.peek(kw::src) {
            input.parse::<kw::src>()?;
            let name;
            syn::bracketed!(name in input);
            let name = name.parse::<syn::LitStr>()?;
            input.parse::<Token![:]>()?;
            let s = input.parse::<syn::LitStr>()?;
            let interface = witx2::Interface::parse(&name.value(), &s.value())
                .map_err(|e| Error::new(s.span(), e))?;
            Ok(ConfigField::Interfaces(vec![interface]))
        } else if l.peek(kw::paths) {
            input.parse::<kw::paths>()?;
            input.parse::<Token![:]>()?;
            let paths;
            let bracket = syn::bracketed!(paths in input);
            let paths = Punctuated::<syn::LitStr, Token![,]>::parse_terminated(&paths)?;
            let values = paths.iter().map(|s| s.value()).collect::<Vec<_>>();
            let mut interfaces = Vec::new();
            for value in &values {
                let interface =
                    witx2::Interface::parse_file(value).map_err(|e| Error::new(bracket.span, e))?;
                interfaces.push(interface);
            }
            Ok(ConfigField::Interfaces(interfaces))
        } else if l.peek(token::Async) {
            if !cfg!(feature = "async") {
                return Err(
                    input.error("async support not enabled in the `witx-bindgen-wasmtime` crate")
                );
            }
            input.parse::<token::Async>()?;
            input.parse::<Token![:]>()?;
            let val = if input.parse::<Option<Token![*]>>()?.is_some() {
                Async::All
            } else {
                let names;
                syn::bracketed!(names in input);
                let paths = Punctuated::<syn::LitStr, Token![,]>::parse_terminated(&names)?;
                let values = paths.iter().map(|s| s.value()).collect();
                Async::Only(values)
            };
            Ok(ConfigField::Async(val))
        } else {
            Err(l.error())
        }
    }
}
