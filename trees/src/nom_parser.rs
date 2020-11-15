/// Type-erased errors.
pub type BoxError = std::boxed::Box<dyn
	std::error::Error   // must implement Error to satisfy ?
	+ std::marker::Send // needed for threads
	+ std::marker::Sync // needed for threads
				    >;

#[derive(Clone, Default, Debug)]
pub struct Mount {
	pub device: std::string::String,
	pub mount_point: std::string::String,
	pub file_system_type: std::string::String,
	pub options: std::vec::Vec<std::string::String>,
}

pub(self) mod parsers {
	use super::Mount;

	fn not_whitespace(i: &str) -> nom::IResult<&str, &str> {
		nom::bytes::complete::is_not(" \t")(i)
	}
	
	#[cfg(test)]
	mod tests {
		use super::*;
		
		#[test]
		fn test_not_whitespace() {
			assert_eq!(not_whitespace("abcd efg"), Ok((" efg", "abcd")));
			assert_eq!(not_whitespace("abcd\tefg"), Ok(("\tefg", "abcd")));
			assert_eq!(not_whitespace(" abcdefg"), Err(nom::Err::Error((" abcdefg", nom::error::ErrorKind::IsNot))));
		}
	}
}
