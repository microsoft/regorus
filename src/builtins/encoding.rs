// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
#[allow(unused)]
use crate::builtins::utils::{
    ensure_args_count, ensure_object, ensure_string, ensure_string_collection,
};
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;

#[allow(unused)]
use anyhow::{anyhow, bail, Context, Result};

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    #[cfg(feature = "base64")]
    {
        m.insert("base64.decode", (base64_decode, 1));
        m.insert("base64.encode", (base64_encode, 1));
        m.insert("base64.is_valid", (base64_is_valid, 1));
    }
    #[cfg(feature = "base64url")]
    {
        m.insert("base64url.decode", (base64url_decode, 1));
        m.insert("base64url.encode", (base64url_encode, 1));
        m.insert("base64url.encode_no_pad", (base64url_encode_no_pad, 1));
    }
    #[cfg(feature = "hex")]
    {
        m.insert("hex.decode", (hex_decode, 1));
        m.insert("hex.encode", (hex_encode, 1));
    }
    #[cfg(feature = "urlquery")]
    {
        m.insert("urlquery.decode", (urlquery_decode, 1));
        m.insert("urlquery.decode_object", (urlquery_decode_object, 1));
        m.insert("urlquery.encode", (urlquery_encode, 1));
        m.insert("urlquery.encode_object", (urlquery_encode_object, 1));
    }
    m.insert("json.is_valid", (json_is_valid, 1));
    m.insert("json.marshal", (json_marshal, 1));
    m.insert("json.marshal_with_options", (json_marshal_with_options, 2));
    m.insert("json.unmarshal", (json_unmarshal, 1));

    #[cfg(feature = "yaml")]
    {
        m.insert("yaml.is_valid", (yaml_is_valid, 1));
        m.insert("yaml.marshal", (yaml_marshal, 1));
        m.insert("yaml.unmarshal", (yaml_unmarshal, 1));
    }
}

#[cfg(feature = "base64")]
fn base64_decode(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "base64.decode";
    ensure_args_count(span, name, params, args, 1)?;

    let encoded_str = ensure_string(name, &params[0], &args[0])?;
    let decoded_bytes = data_encoding::BASE64.decode(encoded_str.as_bytes())?;
    Ok(Value::String(
        String::from_utf8_lossy(&decoded_bytes).into(),
    ))
}

#[cfg(feature = "base64")]
fn base64_encode(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "base64.encode";
    ensure_args_count(span, name, params, args, 1)?;

    let string = ensure_string(name, &params[0], &args[0])?;
    Ok(Value::String(
        data_encoding::BASE64.encode(string.as_bytes()).into(),
    ))
}

#[cfg(feature = "base64")]
fn base64_is_valid(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "base64.is_valid";
    ensure_args_count(span, name, params, args, 1)?;

    let encoded_str = ensure_string(name, &params[0], &args[0])?;
    Ok(Value::Bool(
        data_encoding::BASE64.decode(encoded_str.as_bytes()).is_ok(),
    ))
}

#[cfg(feature = "base64url")]
fn base64url_decode(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "base64url.decode";
    ensure_args_count(span, name, params, args, 1)?;

    let encoded_str = ensure_string(name, &params[0], &args[0])?;
    let decoded_bytes = match data_encoding::BASE64URL.decode(encoded_str.as_bytes()) {
        Ok(b) => b,
        Err(_) => {
            #[cfg(feature = "base64url")]
            {
                data_encoding::BASE64URL_NOPAD
                    .decode(encoded_str.as_bytes())
                    .map_err(|_| anyhow!(params[0].span().error("not a valid url")))?
            }
            #[cfg(not(feature = "base64url"))]
            {
                bail!(params[0].span().error("not a valid url"));
            }
        }
    };

    Ok(Value::String(
        String::from_utf8_lossy(&decoded_bytes).into(),
    ))
}

#[cfg(feature = "base64url")]
fn base64url_encode(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "base64url.encode";
    ensure_args_count(span, name, params, args, 1)?;

    let string = ensure_string(name, &params[0], &args[0])?;
    Ok(Value::String(
        data_encoding::BASE64URL.encode(string.as_bytes()).into(),
    ))
}

#[cfg(feature = "base64url")]
fn base64url_encode_no_pad(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "base64url.encode_no_pad";
    ensure_args_count(span, name, params, args, 1)?;

    let string = ensure_string(name, &params[0], &args[0])?;
    Ok(Value::String(
        data_encoding::BASE64URL_NOPAD
            .encode(string.as_bytes())
            .into(),
    ))
}

#[cfg(feature = "hex")]
fn hex_decode(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "hex.decode";
    ensure_args_count(span, name, params, args, 1)?;

    let encoded_str = ensure_string(name, &params[0], &args[0])?;
    let decoded_bytes = data_encoding::HEXLOWER_PERMISSIVE.decode(encoded_str.as_bytes())?;
    Ok(Value::String(
        String::from_utf8_lossy(&decoded_bytes).into(),
    ))
}

#[cfg(feature = "hex")]
fn hex_encode(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "hex.encode";
    ensure_args_count(span, name, params, args, 1)?;

    let string = ensure_string(name, &params[0], &args[0])?;
    Ok(Value::String(
        data_encoding::HEXLOWER_PERMISSIVE
            .encode(string.as_bytes())
            .into(),
    ))
}

#[cfg(feature = "urlquery")]
fn urlquery_decode(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "urlquery.decode";
    ensure_args_count(span, name, params, args, 1)?;

    let string = ensure_string(name, &params[0], &args[0])?;
    let url_string = "https://non-existent?".to_owned() + string.as_ref();
    let url = match url::Url::parse(&url_string) {
        Ok(v) => v,
        Err(_) => bail!(params[0].span().error("not a valid url query")),
    };

    let mut query_str = "".to_owned();
    for (k, v) in url.query_pairs() {
        query_str += &k;
        if v != "" {
            query_str += "=";
            query_str += &v;
        }
    }
    Ok(Value::String(query_str.into()))
}

#[cfg(feature = "urlquery")]
fn urlquery_decode_object(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "urlquery.decode_object";
    ensure_args_count(span, name, params, args, 1)?;

    let string = ensure_string(name, &params[0], &args[0])?;
    let url_string = "https://non-existent?".to_owned() + string.as_ref();
    let url = match url::Url::parse(&url_string) {
        Ok(v) => v,
        Err(_) => bail!(params[0].span().error("not a valid url query")),
    };

    let mut map = std::collections::BTreeMap::new();
    for (k, v) in url.query_pairs() {
        let key = Value::String(k.clone().into());
        let value = Value::String(v.clone().into());
        if let Ok(a) = map.entry(key).or_insert(Value::new_array()).as_array_mut() {
            a.push(value)
        }
    }
    Ok(Value::from_map(map))
}

#[cfg(feature = "urlquery")]
fn urlquery_encode(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "urlquery.encode";
    ensure_args_count(span, name, params, args, 1)?;

    let s = ensure_string(name, &params[0], &args[0])?;
    let mut url = match url::Url::parse("https://non-existent") {
        Ok(v) => v,
        Err(_) => bail!(params[0].span().error("not a valid url query")),
    };

    url.query_pairs_mut().append_pair(&s, "");
    let query_str = url.query().unwrap_or("");
    if query_str.is_empty() {
        Ok(Value::String("".into()))
    } else {
        Ok(Value::String(query_str[..query_str.len() - 1].into()))
    }
}

#[cfg(feature = "urlquery")]
fn urlquery_encode_object(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "urlquery.encode_object";
    ensure_args_count(span, name, params, args, 1)?;

    let obj = ensure_object(name, &params[0], args[0].clone())?;
    let mut url = match url::Url::parse("https://non-existent") {
        Ok(v) => v,
        Err(_) => bail!(params[0].span().error("not a valid url query")),
    };

    for (key, value) in obj.iter() {
        let key = ensure_string(name, &params[0], key)?;
        match value {
            Value::String(v) => {
                url.query_pairs_mut().append_pair(key.as_ref(), v.as_ref());
            }
            _ => {
                let values = ensure_string_collection(name, &params[0], value)?;
                for v in values {
                    url.query_pairs_mut().append_pair(key.as_ref(), v);
                }
            }
        }
    }

    Ok(Value::String(url.query().unwrap_or("").into()))
}

#[cfg(feature = "yaml")]
fn yaml_is_valid(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "yaml.is_valid";
    ensure_args_count(span, name, params, args, 1)?;

    let yaml_str = ensure_string(name, &params[0], &args[0])?;
    Ok(Value::Bool(Value::from_yaml_str(&yaml_str).is_ok()))
}

#[cfg(feature = "yaml")]
fn yaml_marshal(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "yaml.marshal";
    ensure_args_count(span, name, params, args, 1)?;
    Ok(Value::String(
        serde_yaml::to_string(&args[0])
            .with_context(|| span.error("could not serialize to yaml"))?
            .into(),
    ))
}

#[cfg(feature = "yaml")]
fn yaml_unmarshal(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "yaml.unmarshal";
    ensure_args_count(span, name, params, args, 1)?;
    let yaml_str = ensure_string(name, &params[0], &args[0])?;
    Value::from_yaml_str(&yaml_str).with_context(|| span.error("could not deserialize yaml."))
}

fn json_is_valid(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "json.is_valid";
    ensure_args_count(span, name, params, args, 1)?;

    let json_str = ensure_string(name, &params[0], &args[0])?;
    Ok(Value::Bool(Value::from_json_str(&json_str).is_ok()))
}

fn json_marshal(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "json.marshal";
    ensure_args_count(span, name, params, args, 1)?;
    Ok(Value::String(
        serde_json::to_string(&args[0])
            .with_context(|| span.error("could not serialize to json"))?
            .into(),
    ))
}

fn json_marshal_with_options(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "json.marshal_with_options";
    ensure_args_count(span, name, params, args, 2)?;

    let options = ensure_object(name, &params[1], args[1].clone())?;
    let (mut pretty, mut indent, mut prefix) = (true, Some("\t".to_owned()), None);
    for (option, option_value) in options.iter() {
        match option {
            Value::String(s) if s.as_ref() == "pretty" && option_value.as_bool().is_ok() => {
                pretty = option_value == &Value::Bool(true);
            }
            Value::String(s) if s.as_ref() == "pretty" => bail!(params[1]
                .span()
                .error("marshaling option `pretty` must be true or false")),
            Value::String(s) if s.as_ref() == "prefix" && option_value.as_string().is_ok() => {
                prefix = Some(option_value.as_string()?.as_ref().to_string());
            }
            Value::String(s) if s.as_ref() == "prefix" => bail!(params[1]
                .span()
                .error("marshaling option `pretty` must be string")),
            Value::String(s) if s.as_ref() == "indent" && option_value.as_string().is_ok() => {
                indent = Some(option_value.as_string()?.as_ref().to_string());
            }
            Value::String(s) if s.as_ref() == "indent" => bail!(params[1]
                .span()
                .error("marshaling option `pretty` must be string")),
            _ => bail!(params[1]
                .span()
                .error("marshaling option must be one of `indent`, `prefix` or `pretty`")),
        }
    }

    if !pretty || options.is_empty() {
        return Ok(Value::String(
            serde_json::to_string(&args[0])
                .with_context(|| span.error("could not serialize to json"))?
                .into(),
        ));
    }

    let lines: Vec<String> = serde_json::to_string_pretty(&args[0])
        .with_context(|| span.error("could not serialize to json"))?
        .split('\n')
        .map(|line| {
            let mut line = line.to_string();

            if let Some(indent) = &indent {
                let start_trimmed = line.trim_start();
                let leading_spaces = line.len() - start_trimmed.len();
                let indentation_level = leading_spaces / 2;
                line = indent.repeat(indentation_level) + start_trimmed;
            }

            if let Some(prefix) = &prefix {
                line = prefix.to_owned() + &line;
            }
            line
        })
        .collect();

    Ok(Value::from(lines.join("\n")))
}

fn json_unmarshal(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "json.unmarshal";
    ensure_args_count(span, name, params, args, 1)?;
    let json_str = ensure_string(name, &params[0], &args[0])?;
    Value::from_json_str(&json_str).with_context(|| span.error("could not deserialize json."))
}
