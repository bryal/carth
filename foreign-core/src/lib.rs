#[export_name = "print-int"]
pub extern "C" fn print_int(n: i64) {
    println!("{}", n)
}
