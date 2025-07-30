//! Contains the Args struct for managing and parsing CLI arguments as well as the for this required
//! components

use std::collections::{HashMap, HashSet};

/// Handles command-line arguments and stores them for later use if parsing succeeds. Arguments that
/// are configured as a [flag][ValueStyle::Flag] do not expect a value. Note that both arguments
/// that can be specified [multiple times][`Kind::Multiple`] and
/// [comma separated values][`Kind::CSV`] land in [`.list()`][Args::list()]. Arguments that were
/// given but are either not included in the specifiers passed to [`Args::parse()`] or aren't values
/// associated with preceding keys, for example positional arguments or unexpected arguments, land
/// in [`.other()`][Args::other()].
#[derive(Debug, PartialEq, Clone)]
pub struct Args {
    integers: HashMap<String, i32>,
    booleans: HashMap<String, bool>,
    strings: HashMap<String, String>,
    lists: HashMap<String, Vec<String>>,
    flags: HashSet<String>,
    others: Vec<String>,
}

impl Args {
    /// Creates a new Args struct using the given `args` as the vector to parse
    /// into the desired forms. Note that the first element is always ignored,
    /// as this function is made to get the result of
    /// [`std::env::args().collect::<Vec<String>>()`][std::env::args()]
    pub fn parse(args: &[String], specifiers: &[Specifier]) -> Result<Self, String> {
        let mut integers = HashMap::new();
        let mut booleans = HashMap::new();
        let mut strings = HashMap::new();
        let mut lists: HashMap<String, Vec<String>> = HashMap::new();
        let mut flags = HashSet::new();
        let mut others = Vec::new();
        let mut all_args = HashSet::new();

        let args = if args.len() > 1 { &args[1..] } else { &[] };

        let specifiers_map: HashMap<&str, &Specifier> =
            specifiers.iter().map(|s| (s.key.as_str(), s)).collect();

        let specifiers = specifiers.iter();

        let mut seen = HashSet::new();
        for x in specifiers.clone() {
            let key = x.key.as_str();
            let style = x.style;
            let kind = x.kind;
            let req = x.required;

            if !seen.insert(key) {
                return Err(format!(
                    "Invalid specifiers array: duplicate key field '{key}'"
                ));
            }

            if matches!(style, ValueStyle::Flag) && !matches!(kind, Kind::Flag) {
                return Err(format!(
                    "Invalid specifier: when style is Flag, kind has to be {}'{}'",
                    "Flag as well\nKey: ", key
                ));
            }

            if matches!(kind, Kind::Flag) && !matches!(style, ValueStyle::Flag) {
                return Err(format!(
                    "Invalid specifier: when kind is Flag, style has to be {}'{}'",
                    "Flag as well\nKey: ", key
                ));
            }

            if matches!(kind, Kind::Flag) && req {
                return Err(format!(
                    "Invalid specifier: when style is Flag, the argument {}'{}'",
                    "cannot be made required\nKey: ", key
                ));
            }
        }

        let mut i = 0;
        while i < args.len() {
            let arg = &args[i];

            if let Some((key, specifier)) = specifiers_map.iter().find_map(|(k, s)| {
                let arg = &args[i];
                if arg.starts_with(k) {
                    match s.style {
                        ValueStyle::Equals => {
                            if arg.starts_with(&format!("{k}=")) {
                                Some((k.to_string(), *s))
                            } else {
                                None
                            }
                        }
                        ValueStyle::NextOrEquals => {
                            if arg.starts_with(&format!("{k}=")) || arg == k {
                                Some((k.to_string(), *s))
                            } else {
                                None
                            }
                        }
                        _ => {
                            if arg == k {
                                Some((k.to_string(), *s))
                            } else {
                                None
                            }
                        }
                    }
                } else {
                    None
                }
            }) {
                let value = match specifier.style {
                    ValueStyle::Flag => "true".into(),
                    ValueStyle::Next => {
                        if i + 1 >= args.len() {
                            return Err(format!(
                                "Expected value immediately following argument '{key}'"
                            ));
                        }
                        i += 1;
                        args[i].clone()
                    }
                    ValueStyle::Equals => {
                        // Unwrap here: Thanks to the if-let match statement above, this has to work
                        let index = arg.find('=').unwrap();
                        if index + 1 < arg.len() {
                            arg[index + 1..].to_string()
                        } else {
                            return Err(format!(
                                "Expected value immediately following '=' after argument '{key}'"
                            ));
                        }
                    }
                    ValueStyle::NextOrEquals => {
                        if let Some(index) = arg.find('=') {
                            if index + 1 < arg.len() {
                                arg[index + 1..].to_string()
                            } else {
                                return Err(format!(
                                    "Expected value immediately following '=' after argument '{key}'"
                                ));
                            }
                        } else {
                            if i + 1 >= args.len() {
                                return Err(format!(
                                    "Expected value immediately following argument '{key}'"
                                ));
                            }
                            i += 1;
                            args[i].clone()
                        }
                    }
                };

                if value.is_empty() {
                    return Err(format!("Value string has length 0 for argument '{key}'"));
                }

                all_args.insert(key.clone());

                match specifier.kind {
                    Kind::Multiple => {
                        if let Some(v) = lists.get_mut(&key) {
                            v.push(value);
                        } else {
                            lists.insert(key, vec![value]);
                        }
                    }
                    Kind::Integer => {
                        match value.parse::<i32>() {
                            Ok(x) => match integers.insert(key.clone(), x) {
                                None => {}
                                Some(_) => {
                                    return Err(format!("Unexpected duplicate argument '{key}'"));
                                }
                            },
                            Err(_) => {
                                return Err(format!(
                                    "Error parsing value '{value}' as integer for argument '{key}'"
                                ));
                            }
                        };
                    }
                    Kind::Boolean => {
                        match value.to_lowercase().parse::<bool>() {
                            Ok(x) => match booleans.insert(key.clone(), x) {
                                None => {}
                                Some(_) => {
                                    return Err(format!("Unexpected duplicate argument '{key}'"));
                                }
                            },
                            Err(_) => {
                                return Err(format!(
                                    "Error parsing value '{value}' as boolean for argument '{key}'"
                                ));
                            }
                        };
                    }
                    Kind::String => match strings.insert(key.clone(), value) {
                        None => {}
                        Some(_) => return Err(format!("Unexpected duplicate argument '{key}'")),
                    },
                    Kind::Flag => {
                        if flags.contains(&key) {
                            return Err(format!("Unexpected duplicate flag '{key}'"));
                        }
                        flags.insert(key);
                    }
                    Kind::CSV => {
                        match lists
                            .insert(key.clone(), value.split(',').map(str::to_string).collect())
                        {
                            None => {}
                            Some(_) => {
                                return Err(format!("Unexpected duplicate argument '{key}'"));
                            }
                        }
                    }
                }
            } else {
                others.push(arg.clone());
            }

            i += 1;
        }

        for specifier in specifiers {
            let key = &specifier.key;
            if specifier.required && !all_args.contains(key) {
                return Err(format!("Missing required argument '{key}'"));
            }
        }

        Ok(Self {
            integers,
            booleans,
            strings,
            lists,
            flags,
            others,
        })
    }

    /// If the given key was parsed in [`Args::parse()`], this will return the value that was
    /// parsed, if the key does not exist, it returns None
    pub fn integer(&self, key: &str) -> Option<i32> {
        self.integers.get(key).copied()
    }

    /// If the given key was parsed in [`Args::parse()`], this will return the value that was
    /// parsed, if the key does not exist, it returns None
    pub fn boolean(&self, key: &str) -> Option<bool> {
        self.booleans.get(key).copied()
    }

    /// If the given key was parsed in [`Args::parse()`], this will return the value that was
    /// parsed, if the key does not exist, it returns None
    pub fn string(&self, key: &str) -> Option<String> {
        self.strings.get(key).cloned()
    }

    /// If the given key was parsed in [`Args::parse()`], this will return the value that was
    /// parsed, if the key does not exist, it returns None
    pub fn list(&self, key: &str) -> Option<Vec<String>> {
        self.lists.get(key).cloned()
    }

    /// Returns [`true`] if the given key was found during argument parsing in [`Args::parse()`]
    /// and [`false`] otherwise
    pub fn flag(&self, key: &str) -> bool {
        self.flags.contains(key)
    }

    /// Returns a readonly version of the private `self.others` vector
    pub fn other(&self) -> &Vec<String> {
        &self.others
    }
}

/// Used to specify rules for a specific argument
#[derive(Debug, PartialEq, Clone)]
pub struct Specifier {
    /// The argument key/name to use for the argument. Note that arguments are traditionally
    /// prefixed with `-` or `--`, although this is not enforced.
    pub key: String,
    /// The arguments key-value relationship style
    pub style: ValueStyle,
    /// The type of the argument's value
    pub kind: Kind,
    /// Whether this argument is required to be given or not
    pub required: bool,
}

impl Specifier {
    /// Creates a new [`Specifier`] instance with all the values given.
    ///
    /// # Example
    /// Create a new instance
    /// ```
    /// use maximyoga_term_utils::cli::args::{
    ///     Specifier,
    ///     ValueStyle::NextOrEquals,
    ///     Kind::Integer
    /// };
    /// assert_eq!(
    ///     Specifier::new("--count".into(), NextOrEquals, Integer, true),
    ///     Specifier {
    ///         key: "--count".into(),
    ///         style: NextOrEquals,
    ///         kind: Integer,
    ///         required: true
    ///     }
    /// )
    /// ```
    pub fn new(key: &str, style: ValueStyle, kind: Kind, required: bool) -> Self {
        Self {
            key: key.into(),
            style,
            kind,
            required,
        }
    }

    /// Creates a new [`Specifier`] instance with the given key as the flag's name, and all the
    /// other values tailored for flag-specific requirements. This method is made for convenience,
    /// since, when used in [`Args::parse()`], Specifiers for flags are expected to be the same,
    /// except for the key.
    ///
    /// # Example
    /// Create a new instance for a flag
    /// ```
    /// use maximyoga_term_utils::cli::args::{
    ///     Specifier,
    ///     Kind::Flag,
    ///     ValueStyle::Flag as FlagStyle
    /// };
    /// assert_eq!(
    ///     Specifier::flag("-h"),
    ///     Specifier::new("-h", FlagStyle, Flag, false)
    /// )
    /// ```
    pub fn flag(key: &str) -> Self {
        Self {
            key: key.into(),
            style: ValueStyle::Flag,
            kind: Kind::Flag,
            required: false,
        }
    }
}

/// Specifies the type of the value the argument is supposed to receive. Default is [`Kind::String`]
#[derive(Debug, PartialEq, Copy, Clone, Default)]
pub enum Kind {
    /// Allows the argument to be given multiple times. The argument's values will be parsed as
    /// Strings
    Multiple,
    /// An integer, ranging from [`i32::MIN`] to [`i32::MAX`]
    Integer,
    /// A boolean, allows only "true" or "false" (case-insensitive)
    Boolean,
    /// Just stores the value string as-is
    #[default]
    String,
    /// A boolean value that is [`true`] when the flag is given and [`false`] otherwise
    Flag,
    /// A comma-separated list of string values. Whitespace is not trimmed, expected format is
    /// `value1,value2,"value 3",...` (no spaces around commas)
    CSV,
}

/// Specifies how the value works in relation to the key, for example what separator it uses, or how
/// else to get it. Default is [`ValueStyle::NextOrEquals`]
#[derive(Debug, PartialEq, Copy, Clone, Default)]
pub enum ValueStyle {
    /// The argument is a flag and is [`true`] when given, [`false`] otherwise.
    Flag,
    /// The value comes after the key and is therefore the next item, as in `arg value`
    Next,
    /// The value is separated from the key via an '=', as in `arg=value`
    Equals,
    /// The value can come after the key is therefore the next item, as in `arg value`, or it can be
    /// separated from the key via a '=', as in `arg=value`
    #[default]
    NextOrEquals,
}

/// Testing module for [`Args::parse()`]
#[cfg(test)]
pub mod parse_tests {
    use super::*;
    #[test]
    fn general_success() {
        let process_args: Vec<String> = [
            "program",
            "--arg1",
            "12",
            "-m=1",
            "--flag1",
            "--arg2=Hi there",
            "--arg3",
            "123",
            "x=a,b,3",
            "-m",
            "2",
        ]
        .into_iter()
        .map(str::to_string)
        .collect();

        let args = Args::parse(
            &process_args,
            &[
                Specifier::new("--arg1", ValueStyle::Next, Kind::Integer, false),
                Specifier::new("--arg2", ValueStyle::Equals, Kind::String, true),
                Specifier::new("-m", ValueStyle::NextOrEquals, Kind::Multiple, false),
                Specifier::new("x", ValueStyle::Equals, Kind::CSV, true),
                Specifier::flag("--flag1"),
            ],
        );
        assert!(args.is_ok());
        let args = args.unwrap();

        assert!(args.flag("--flag1"));
        assert_eq!(args.integer("--arg1"), Some(12));
        assert_eq!(
            args.list("-m"),
            Some(vec!["1".to_string(), "2".to_string()])
        );
        assert_eq!(args.string("--arg2"), Some(String::from("Hi there")));
        assert_eq!(args.other(), &vec!["--arg3".to_string(), "123".to_string()]);
        assert_eq!(
            args.list("x"),
            Some(vec!["a".to_string(), "b".to_string(), "3".to_string()])
        );

        assert!(!args.flag("non-existent"));
        assert!(args.integer("--arg4").is_none());
        assert!(args.string("--arg1").is_none());
    }

    #[test]
    fn required_missing() {
        let args = Args::parse(
            &[],
            &[Specifier::new(
                "--arg1",
                ValueStyle::Next,
                Kind::Integer,
                true,
            )],
        );
        assert!(args.is_err());
        assert_eq!(args.unwrap_err(), "Missing required argument '--arg1'");
    }

    #[test]
    fn duplicate_argument() {
        let process_args: Vec<String> = ["program", "-m=1", "-m", "2"]
            .into_iter()
            .map(str::to_string)
            .collect();

        let args = Args::parse(
            &process_args,
            &[Specifier::new(
                "-m",
                ValueStyle::NextOrEquals,
                Kind::String,
                false,
            )],
        );
        assert!(args.is_err());
        assert_eq!(args.unwrap_err(), "Unexpected duplicate argument '-m'");
    }

    #[test]
    fn duplicate_specifier_key() {
        let args = Args::parse(&[], &[Specifier::flag("-n"), Specifier::flag("-n")]);
        assert!(args.is_err());
        assert_eq!(
            args.unwrap_err(),
            "Invalid specifiers array: duplicate key field '-n'"
        );
    }

    #[test]
    fn flag_wrong_kind() {
        let args = Args::parse(
            &["".into(), "-f=".into()],
            &[Specifier::new("-f", ValueStyle::Flag, Kind::String, false)],
        );
        assert!(args.is_err());
        assert_eq!(
            args.unwrap_err(),
            "Invalid specifier: when style is Flag, kind has to be Flag as well\nKey: '-f'"
        )
    }

    #[test]
    fn flag_wrong_style() {
        let args = Args::parse(
            &["".into(), "-f".into()],
            &[Specifier::new("-f", ValueStyle::Next, Kind::Flag, false)],
        );
        assert!(args.is_err());
        assert_eq!(
            args.unwrap_err(),
            "Invalid specifier: when kind is Flag, style has to be Flag as well\nKey: '-f'"
        )
    }

    #[test]
    fn flag_required() {
        let args = Args::parse(
            &["".into(), "-f".into()],
            &[Specifier::new("-f", ValueStyle::Flag, Kind::Flag, true)],
        );
        assert!(args.is_err());
        assert_eq!(
            args.unwrap_err(),
            "Invalid specifier: when style is Flag, the argument cannot be made required\nKey: '-f'"
        )
    }

    #[test]
    fn missing_next_value() {
        let args = Args::parse(
            &["".into(), "-f".into()],
            &[Specifier::new("-f", ValueStyle::Next, Kind::String, true)],
        );
        assert!(args.is_err());
        assert_eq!(
            args.unwrap_err(),
            "Expected value immediately following argument '-f'"
        )
    }

    #[test]
    fn missing_equals_value() {
        let args = Args::parse(
            &["".into(), "-f=".into()],
            &[Specifier::new("-f", ValueStyle::Equals, Kind::String, true)],
        );
        assert!(args.is_err());
        assert_eq!(
            args.unwrap_err(),
            "Expected value immediately following '=' after argument '-f'"
        )
    }

    #[test]
    fn missing_next_value_2() {
        let args = Args::parse(
            &["".into(), "-f".into()],
            &[Specifier::new(
                "-f",
                ValueStyle::NextOrEquals,
                Kind::String,
                true,
            )],
        );
        assert!(args.is_err());
        assert_eq!(
            args.unwrap_err(),
            "Expected value immediately following argument '-f'"
        )
    }

    #[test]
    fn missing_equals_value_2() {
        let args = Args::parse(
            &["".into(), "-f=".into()],
            &[Specifier::new(
                "-f",
                ValueStyle::NextOrEquals,
                Kind::String,
                true,
            )],
        );
        assert!(args.is_err());
        assert_eq!(
            args.unwrap_err(),
            "Expected value immediately following '=' after argument '-f'"
        )
    }

    #[test]
    fn empty_next_value() {
        let args = Args::parse(
            &["".into(), "-f".into(), "".into()],
            &[Specifier::new("-f", ValueStyle::Next, Kind::String, true)],
        );
        assert!(args.is_err());
        assert_eq!(
            args.unwrap_err(),
            "Value string has length 0 for argument '-f'"
        )
    }

    #[test]
    fn invalid_integer() {
        let args = Args::parse(
            &["".into(), "-f".into(), "a".into()],
            &[Specifier::new("-f", ValueStyle::Next, Kind::Integer, true)],
        );
        assert!(args.is_err());
        assert_eq!(
            args.unwrap_err(),
            "Error parsing value 'a' as integer for argument '-f'"
        );
    }

    #[test]
    fn invalid_boolean() {
        let args = Args::parse(
            &["".into(), "-f".into(), "a".into()],
            &[Specifier::new("-f", ValueStyle::Next, Kind::Boolean, true)],
        );
        assert!(args.is_err());
        assert_eq!(
            args.unwrap_err(),
            "Error parsing value 'a' as boolean for argument '-f'"
        );
    }

    #[test]
    fn duplicate_flag() {
        let args = Args::parse(
            &["".into(), "-f".into(), "-f".into()],
            &[Specifier::flag("-f")],
        );
        assert!(args.is_err());
        assert_eq!(args.unwrap_err(), "Unexpected duplicate flag '-f'");
    }
}