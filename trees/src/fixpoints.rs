// fixpoints by Shepmaster at https://stackoverflow.com/questions/42174338/write-fix-point-function-in-rust

type Lazy<'a, T> = Box<FnBox() -> T + 'a>;

// fix: (Lazy<T> -> T) -> T
fn fix<'a, T, F>(f: F) -> T
where F: Fn(Lazy<'a, T>) -> T + Copy + 'a
{
    f(Box::new(move || fix(f)))
}

fn factorial(n: u64) -> u64 {
    // f: Lazy<u64 -> u64> -> u64 -> u64
    fn f(fac: Lazy<'static, Box<FnBox(u64) -> u64>>) -> Box<FnBox(u64) -> u64> {
        Box::new(move |n| {
            if n == 0 {
                1
            } else { 
                n * fac()(n - 1)
            }
        })
    }
    fix(f)(n)
}
