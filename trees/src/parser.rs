#![cfg(feature = "alloc")]
extern crate nom;

use nom::{
  branch::alt,
  bytes::complete::{tag, take},
  character::complete::{anychar, char, multispace0, none_of},
  combinator::{map, map_opt, map_res, value, verify},
  error::ParseError,
  multi::{fold_many0, separated_list0},
  number::complete::double,
  sequence::{delimited, preceded, separated_pair},
  IResult, Parser,
};

fn leaf_parser(i: &str) -> IResult<&str, Program> {
    match complete::tag("~")(i) {
	Ok((remaining_input,_)) => Ok((remaining_input,Leaf)),
	Err(e) => Err(e)
    }
}


fn ws<'a, O, E: ParseError<&'a str>, F: Parser<&'a str, O, E>>(f: F) -> impl Parser<&'a str, O, E> {
  delimited(multispace0, f, multispace0)
}


fn object(input: &str) -> IResult<&str, HashMap<String, Tree>> {
  map(
    delimited(
      char('{'),
      ws(separated_list0(
        ws(char(',')),
        separated_pair(string, ws(char(':')), json_value),
      )),
      char('}'),
    ),
    |key_values| key_values.into_iter().collect(),
  )(input)
}

fn json_value(input: &str) -> IResult<&str, Tree> {

    alt((
	leaf_parser, 
//    map(object, Object),
  ))(input)
}

fn json(input: &str) -> IResult<&str, Tree> {
  ws(json_value).parse(input)
}

#[test]
fn json_string() {
  assert_eq!(string("\"\""), Ok(("", "".to_string())));
  assert_eq!(string("\"abc\""), Ok(("", "abc".to_string())));
  assert_eq!(
    string("\"abc\\\"\\\\\\/\\b\\f\\n\\r\\t\\u0001\\u2014\u{2014}def\""),
    Ok(("", "abc\"\\/\x08\x0C\n\r\t\x01——def".to_string())),
  );
  assert_eq!(string("\"\\uD83D\\uDE10\""), Ok(("", "😐".to_string())));

  assert!(string("\"").is_err());
  assert!(string("\"abc").is_err());
  assert!(string("\"\\\"").is_err());
  assert!(string("\"\\u123\"").is_err());
  assert!(string("\"\\uD800\"").is_err());
  assert!(string("\"\\uD800\\uD800\"").is_err());
  assert!(string("\"\\uDC00\"").is_err());
}

#[test]
fn json_object() {
  use JsonValue::*;

  let input = r#"{"a":42,"b":"x"}"#;

  let expected = Object(
    vec![
      ("a".to_string(), Num(42.0)),
      ("b".to_string(), Str("x".to_string())),
    ]
    .into_iter()
    .collect(),
  );

  assert_eq!(json(input), Ok(("", expected)));
}

#[test]
fn json_array() {
  use JsonValue::*;

  let input = r#"[42,"x"]"#;

  let expected = Array(vec![Num(42.0), Str("x".to_string())]);

  assert_eq!(json(input), Ok(("", expected)));
}

#[test]
fn json_whitespace() {
  use JsonValue::*;

  let input = r#"
  {
    "null" : null,
    "true"  :true ,
    "false":  false  ,
    "number" : 123e4 ,
    "string" : " abc 123 " ,
    "array" : [ false , 1 , "two" ] ,
    "object" : { "a" : 1.0 , "b" : "c" } ,
    "empty_array" : [  ] ,
    "empty_object" : {   }
  }
  "#;

  assert_eq!(
    json(input),
    Ok((
      "",
      Object(
        vec![
          ("null".to_string(), Null),
          ("true".to_string(), Bool(true)),
          ("false".to_string(), Bool(false)),
          ("number".to_string(), Num(123e4)),
          ("string".to_string(), Str(" abc 123 ".to_string())),
          (
            "array".to_string(),
            Array(vec![Bool(false), Num(1.0), Str("two".to_string())])
          ),
          (
            "object".to_string(),
            Object(
              vec![
                ("a".to_string(), Num(1.0)),
                ("b".to_string(), Str("c".to_string())),
              ]
              .into_iter()
              .collect()
            )
          ),
          ("empty_array".to_string(), Array(vec![]),),
          ("empty_object".to_string(), Object(HashMap::new()),),
        ]
        .into_iter()
        .collect()
      )
    ))
  );
}
