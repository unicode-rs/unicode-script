//! This crate exposes the Unicode `Script` and `Script_Extension`
//! properties from [UAX #24](http://www.unicode.org/reports/tr24/)

#![cfg_attr(not(feature = "with_std"), no_std)]

#[rustfmt::skip]
mod tables;

pub use tables::{Script, ScriptExtension, UNICODE_VERSION};

use tables::{get_script, get_script_extension};

impl Script {
    /// Get the full name of a script
    pub fn full_name(self) -> &'static str {
        self.inner_full_name()
    }

    /// Get the four-character short name of a script
    pub fn short_name(self) -> &'static str {
        self.inner_short_name()
    }

    /// Is this script "Recommended" according to
    /// [UAX #31](www.unicode.org/reports/tr31/#Table_Recommended_Scripts)?
    pub fn is_recommended(self) -> bool {
        use Script::*;
        match self {
            Common | Inherited | Arabic | Armenian | Bengali | Bopomofo | Cyrillic | Devanagari
            | Ethiopic | Georgian | Greek | Gujarati | Gurmukhi | Han | Hangul | Hebrew
            | Hiragana | Kannada | Katakana | Khmer | Lao | Latin | Malayalam | Myanmar | Oriya
            | Sinhala | Tamil | Telugu | Thaana | Thai | Tibetan => true,
            _ => false,
        }
    }
}

impl From<char> for Script {
    fn from(o: char) -> Self {
        o.script()
    }
}

impl ScriptExtension {
    /// Obtain the list of scripts contained inside this ScriptExtension
    #[cfg(feature = "with_std")]
    pub fn scripts(self) -> Vec<Script> {
        self.inner_scripts()
    }

    /// Check if this ScriptExtension contains the given script
    pub fn contains_script(self, script: Script) -> bool {
        self.inner_contains_script(script)
    }

    /// Find the intersection between two ScriptExtensions. Returns Unknown if things
    /// do not intersect.
    ///
    /// "Common" (`Zyyy`) and "Inherited" (`Zinh`) are considered as intersecting
    /// everything.
    pub fn intersection(&mut self, other: Self) -> Self {
        self.inner_intersect(other)
    }

    /// Intersect this ScriptExtension with another ScriptExtension. Produces Unknown if things
    /// do not intersect. This is equivalent to [`ScriptExtension::intersection`] but it stores the result
    /// in `self`
    ///
    /// "Common" (`Zyyy`) and "Inherited" (`Zinh`) are considered as intersecting
    /// everything.
    pub fn intersect_with(&mut self, other: Self) {
        *self = self.inner_intersect(other)
    }

    /// Checks if the script extension is empty (unknown)
    pub fn is_empty(self) -> bool {
        self == ScriptExtension::Single(Script::Unknown)
    }
}

impl From<char> for ScriptExtension {
    fn from(o: char) -> Self {
        o.script_extension()
    }
}

/// Extension trait on `char` for calculating script properties
pub trait UnicodeScript {
    /// Get the script for a given character
    fn script(&self) -> Script;
    /// Get the Script_Extension for a given character
    fn script_extension(&self) -> ScriptExtension;
}

impl UnicodeScript for char {
    fn script(&self) -> Script {
        get_script(*self).unwrap_or(Script::Unknown)
    }

    fn script_extension(&self) -> ScriptExtension {
        get_script_extension(*self).unwrap_or_else(|| ScriptExtension::Single(self.script()))
    }
}
