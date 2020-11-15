
#[macro_use]
extern crate nom;


named!(get_greeting<&str,&str>,
    tag_s!("hi")
);

fn main() {
    let res = get_greeting("hi there");
    println!("{:?}",res);
}
// Done(" there", "hi")
