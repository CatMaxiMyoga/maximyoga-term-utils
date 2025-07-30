//! Contains the Args struct for managing and parsing CLI arguments as well as the for this required
//! components

use std::collections::HashMap;

/// Handles command-line arguments and, if no problem occurs, stores them to allow for managing and
/// working with them. Arguments that are configured as a [flag][ValueStyle::Flag] do not expect a
/// value. Note that both arguments that can be specified [multiple times][`Kind::Multiple`] and
/// [comma separated values][`Kind::CSV`] land in [`.lists()`][Args::lists()]. Arguments that were
/// given but are either not included in the specifiers passed to [`Args::parse()`] or aren't values
/// associated with preceding keys, for example positional arguments or unexpected arguments, land
/// in [`.others()`][Args::others()].
#[derive(Debug, PartialEq, Clone)]
pub struct Args {
    integers: HashMap<String, i32>,
    booleans: HashMap<String, bool>,
    strings: HashMap<String, String>,
    lists: HashMap<String, Vec<String>>,
    flags: Vec<String>,
    others: Vec<String>,
}

impl Args {
    /// Creates a new Args struct using the given `args` as the vector to parse
    /// into the desired forms
    pub fn parse(args: &[String], specifiers: &[Specifier]) -> Result<Self, String> {
        let mut integers = HashMap::new();
        let mut booleans = HashMap::new();
        let mut strings = HashMap::new();
        let mut lists: HashMap<String, Vec<String>> = HashMap::new();
        let mut flags = Vec::new();
        let mut others = Vec::new();
        let mut all_keys = Vec::new();

        let specifiers = specifiers.iter();

        let mut i = 0;
        while i < args.len() {
            let arg = &args[i];

            if let Some(specifier) = specifiers.clone().find(|x| {
                if arg.starts_with(&x.key) {
                    match x.style {
                        ValueStyle::Equals => arg.contains('='),
                        ValueStyle::NextOrEquals => arg.contains('=') || arg == &x.key,
                        _ => arg == &x.key,
                    }
                } else {
                    false
                }
            }) {
                let key = specifier.key.clone();

                if all_keys.contains(&key) && !matches!(specifier.kind, Kind::Multiple) {
                    return Err(format!(
                        "Invalid specifiers array: duplicate key field '{key}'"
                    ));
                }

                let value = match specifier.style {
                    ValueStyle::Flag => {
                        if !matches!(specifier.kind, Kind::Flag) {
                            return Err(format!(
                                "Invalid specifier: when style is Flag, kind has to be Flag {}{:?}",
                                "as well\nKey: ", specifier.key
                            ));
                        } else if specifier.required {
                            return Err(format!(
                                "Invalid specifier: when style is Flag, the argument cannot {}{:?}",
                                "be made required\nKey: ", specifier.key
                            ));
                        }
                        "true".into()
                    }
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

                all_keys.push(key.clone());

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
                                    "Error parsing value '{value}' for argument '{key}'"
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
                                    "Error parsing value '{value}' for argument '{key}'"
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
                        flags.push(key);
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
        }

        for specifier in specifiers {
            let key = &specifier.key;
            if specifier.required && !all_keys.contains(key) {
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
        self.flags.contains(&key.to_string())
    }

    /// Returns a readonly version of the private `self.others` vector
    pub fn other(&self) -> &Vec<String> {
        &self.others
    }
}

/// Used to specify rules for a specific argument
#[derive(Debug, PartialEq, Clone)]
pub struct Specifier {
    /// The argument key/name to use for the argument. Must be unique.
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
    /// # Examples
    /// Create a new instance
    /// ```
    /// use maximyoga_term_utils::cli::args::{Specifier, ValueStyle::NextOrEquals, Kind::Integer};
    /// let spec = Specifier::new("--count".into(), NextOrEquals, Integer, true);
    /// assert_eq!(spec, Specifier {
    ///     key: "--count".into(),
    ///     style: NextOrEquals,
    ///     kind: Integer,
    ///     required: true
    /// })
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
    /// # Examples
    /// Create a new instance for a flag
    /// ```
    /// use maximyoga_term_utils::cli::args::{
    ///     Specifier,
    ///     Kind::Flag,
    ///     ValueStyle::Flag as FlagStyle
    /// };
    /// let spec = Specifier::flag("-h");
    /// assert_eq!(spec, Specifier::new("-h", FlagStyle, Flag, false))
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

/// Specifies the type of the value the argument is supposed to receive.
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum Kind {
    /// Allows the argument to be given multiple times. The argument's values will be parsed as
    /// Strings
    Multiple,
    /// An integer, ranging from [`i32::MIN`] to [`i32::MAX`]
    Integer,
    /// A boolean, allows only "true" or "false" (case-insensitive)
    Boolean,
    /// Just stores the value string as-is
    String,
    /// A boolean value that is [`true`] when the flag is given and [`false`] otherwise
    Flag,
    /// A comma-separated list of string values. Whitespace is not trimmed, expected format is
    /// `value1,value2,"value 3",...` (no spaces around commas)
    CSV,
}

/// Specifies how the value works in relation to the key, for example what separator it uses, or how
/// else to get it.
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum ValueStyle {
    /// The argument is a flag and is [`true`] when given, [`false`] otherwise.
    Flag,
    /// The value comes after the key and is therefore the next item, as in `arg value`
    Next,
    /// The value is separated from the key via an '=', as in `arg=value`
    Equals,
    /// The value can come after the key is therefore the next item, as in `arg value`, or it can be
    /// separated from the key via a '=', as in `arg=value`
    NextOrEquals,
}

/// Tests
#[cfg(test)]
pub mod tests {}