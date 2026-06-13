macro_rules! make_char_fns {
    ($(fn $name:ident => $char_method_name:ident;)+) => {
        $(
            #[doc = concat!("A copy of [`char::", stringify!($name), "`] with signature adjusted to be usable as a [`Pattern`](crate::Pattern)")]
            pub fn $name(c: char) -> bool {
                c.$char_method_name()
            }
        )+
    };
}

make_char_fns! {
    fn alphabetic => is_alphabetic;
    fn alphanumeric => is_alphanumeric;
    fn control => is_control;
    fn numeric => is_numeric;
    fn lowercase => is_lowercase;
    fn uppercase => is_uppercase;
    fn whitespace => is_whitespace;
    fn ascii => is_ascii;
    fn ascii_alphabetic => is_ascii_alphabetic;
    fn ascii_uppercase => is_ascii_uppercase;
    fn ascii_lowercase => is_ascii_lowercase;
    fn ascii_alphanumeric => is_ascii_alphanumeric;
    fn ascii_digit => is_ascii_digit;
    fn ascii_hexdigit => is_ascii_hexdigit;
    fn ascii_punctuation => is_ascii_punctuation;
    fn ascii_graphic => is_ascii_graphic;
    fn ascii_whitespace => is_ascii_whitespace;
    fn ascii_control => is_ascii_control;
}
