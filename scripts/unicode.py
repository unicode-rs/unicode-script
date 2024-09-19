#!/usr/bin/env python
#
# Copyright 2011-2015 The Rust Project Developers. See the COPYRIGHT
# file at the top-level directory of this distribution and at
# http://rust-lang.org/COPYRIGHT.
#
# Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
# http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
# <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
# option. This file may not be copied, modified, or distributed
# except according to those terms.

# This script uses the following Unicode tables:
# - PropertyValueAliases.txt
# - ScriptExtensions.txt
# - Scripts.txt
#
# Since this should not require frequent updates, we just store this
# out-of-line and check the unicode.rs file into git.

import fileinput, re, os, sys

preamble = '''// Copyright 2012-2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// NOTE: The following code was generated by "scripts/unicode.py", do not edit directly

#![allow(missing_docs, non_upper_case_globals, non_snake_case)]

pub use tables_impl::*;

#[rustfmt::skip]
mod tables_impl {
use crate::ScriptExtension;
'''

# Close `mod impl {`
ending='''
}
'''

UNICODE_VERSION = (16, 0, 0)

UNICODE_VERSION_NUMBER = "%s.%s.%s" %UNICODE_VERSION

def escape_char(c):
    return "'\\u{%x}'" % c

def fetch(f):
    if not os.path.exists(os.path.basename(f)):
        if "emoji" in f:
            os.system("curl -O https://www.unicode.org/Public/emoji/%s.%s/%s"
                      % (UNICODE_VERSION[0], UNICODE_VERSION[1], f))
        else:
            os.system("curl -O https://www.unicode.org/Public/%s/ucd/%s"
                      % (UNICODE_VERSION_NUMBER, f))

    if not os.path.exists(os.path.basename(f)):
        sys.stderr.write("cannot load %s" % f)
        exit(1)

def group_cats(cats):
    cats_out = {}
    for cat in cats:
        cats_out[cat] = group_cat(cats[cat])
    return cats_out

def aliases():
    """
    Fetch the shorthand aliases for each longhand Script name
    """
    fetch("PropertyValueAliases.txt")
    longforms = {}
    shortforms = {}
    re1 = re.compile(r"^ *sc *; *(\w+) *; *(\w+)")
    for line in fileinput.input(os.path.basename("PropertyValueAliases.txt")):
        m = re1.match(line)
        if m:
            l = m.group(2).strip()
            s = m.group(1).strip()
            assert(s not in longforms)
            assert(l not in shortforms)
            longforms[s] = l
            shortforms[l] = s
        else:
            continue

    return (longforms, shortforms)

def format_table_content(f, content, indent):
    line = " "*indent
    first = True
    for chunk in content.split(","):
        if len(line) + len(chunk) < 98:
            if first:
                line += chunk
            else:
                line += ", " + chunk
            first = False
        else:
            f.write(line + ",\n")
            line = " "*indent + chunk
    f.write(line)

# Implementation from unicode-segmentation
def load_properties(f, interestingprops):
    fetch(f)
    props = {}
    # Note: these regexes are different from those in unicode-segmentation,
    # becase we need to handle spaces here
    re1 = re.compile(r"^ *([0-9A-F]+) *; *([^#]+) *#")
    re2 = re.compile(r"^ *([0-9A-F]+)\.\.([0-9A-F]+) *; *([^#]+) *#")

    for line in fileinput.input(os.path.basename(f)):
        prop = None
        d_lo = 0
        d_hi = 0
        m = re1.match(line)
        if m:
            d_lo = m.group(1)
            d_hi = m.group(1)
            prop = m.group(2).strip()
        else:
            m = re2.match(line)
            if m:
                d_lo = m.group(1)
                d_hi = m.group(2)
                prop = m.group(3).strip()
            else:
                continue
        if interestingprops and prop not in interestingprops:
            continue
        d_lo = int(d_lo, 16)
        d_hi = int(d_hi, 16)
        if prop not in props:
            props[prop] = []
        props[prop].append((d_lo, d_hi))

    return props

# Implementation from unicode-segmentation
def emit_table(f, name, t_data, t_type = "&'static [(char, char)]", is_pub=True,
        pfun=lambda x: "(%s,%s)" % (escape_char(x[0]), escape_char(x[1])), is_const=True):
    pub_string = "const"
    if not is_const:
        pub_string = "let"
    if is_pub:
        pub_string = "pub " + pub_string
    f.write("    %s %s: %s = &[\n" % (pub_string, name, t_type))
    data = ""
    first = True
    for dat in t_data:
        if not first:
            data += ","
        first = False
        data += pfun(dat)
    format_table_content(f, data, 8)
    f.write("\n    ];\n\n")

def emit_search(f):
    f.write("""
pub fn bsearch_range_value_table<T: Copy>(c: char, r: &'static [(char, char, T)]) -> Option<T> {
    use core::cmp::Ordering::{Equal, Less, Greater};
    match r.binary_search_by(|&(lo, hi, _)| {
        if lo <= c && c <= hi { Equal }
        else if hi < c { Less }
        else { Greater }
    }) {
        Ok(idx) => {
            let (_, _, cat) = r[idx];
            Some(cat)
        }
        Err(_) => None
    }
}

#[inline]
pub fn get_script(c: char) -> Option<Script> {
    bsearch_range_value_table(c, SCRIPTS)
}

#[inline]
pub fn get_script_extension(c: char) -> Option<ScriptExtension> {
    bsearch_range_value_table(c, SCRIPT_EXTENSIONS)
}
""")

def emit_enums(f, script_list, extension_list, longforms):
    """
    Emit the Script and ScriptExtension enums as well as any related utility functions
    """

    f.write("""
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
#[non_exhaustive]
#[allow(non_camel_case_types)]
#[repr(u8)]
/// A value of the `Script` property
pub enum Script {
    /// Unknown script
    Unknown = 0xFF,
    /// Zyyy
    Common = 0xFE,
    /// Zinh,
    Inherited = 0xFD,
""")
    for (i, script) in enumerate(script_list):
        f.write("    /// %s\n    %s = %s,\n" % (script, longforms[script], i))
    f.write("}\n")
    f.write("pub const NEXT_SCRIPT: u8 = %s;" % len(script_list))
    f.write("""

pub mod script_extensions {
    use crate::ScriptExtension;
    pub const COMMON: ScriptExtension = ScriptExtension::new_common();
    pub const INHERITED: ScriptExtension = ScriptExtension::new_inherited();
    pub const UNKNOWN: ScriptExtension = ScriptExtension::new_unknown();
""")
    for (i, script) in enumerate(script_list):
        first = 0
        second = 0
        third = 0
        # need to replace L because `hex()` will spit out an L suffix for larger numbers
        if i < 64:
            first = hex(1 << i).replace("L", "")
        elif i < 128:
            second = hex(1 << (i - 64)).replace("L", "")
        else:
            third = hex(1 << (i - 128)).replace("L", "")
        f.write("    /// %s\n    pub const %s: ScriptExtension = ScriptExtension::new(%s, %s, %s);\n" %
                (longforms[script], longforms[script].upper(), first, second, third))
        if script != longforms[script]:
            f.write("    /// %s\n    pub const %s: ScriptExtension = %s;\n" %
                    (longforms[script], script.upper(), longforms[script].upper()))
    for ext in extension_list:
        longform = ", ".join([longforms[s] for s in ext])
        name = "_".join([s.upper() for s in ext])
        expr = ext[0].upper()
        for e in ext[1:]:
            expr = "%s.union(%s)" % (expr, e.upper())
        f.write("    /// %s\n    pub const %s: ScriptExtension = %s;\n" % (longform, name, expr))
    f.write("""}

""")

    # Generate implementation for the `Script`
    generate_script_impl(f)


def generate_script_impl(f):
    """Generates an `impl Script { ... }` section with all the required functions"""

    # Open `impl Script` section.
    f.write("""impl Script {
""")

    # Generate impl of `inner_full_name`.
    f.write("""
    #[inline]
    pub(crate) fn inner_full_name(self) -> &'static str {
        match self {
            Script::Unknown => "Unknown",
            Script::Common => "Common",
            Script::Inherited => "Inherited",
""")
    for script in script_list:
        f.write("            Script::%s => \"%s\",\n" % (longforms[script], longforms[script]))
    f.write("""        }
    }
""")

    # Generate impl of `inner_from_full_name`.
    f.write("""
    #[inline]
    pub(crate) fn inner_from_full_name(input: &str) -> Option<Self> {
        match input {
            "Unknown" => Some(Script::Unknown),
            "Common" => Some(Script::Common),
            "Inherited" => Some(Script::Inherited),
""")
    for script in script_list:
        f.write("            \"%s\" => Some(Script::%s),\n" % (longforms[script], longforms[script]))
    f.write("            _ => None,\n" )
    f.write("""        }
    }
""")

    # Generate impl of `inner_short_name`
    f.write("""
    #[inline]
    pub(crate) fn inner_short_name(self) -> &'static str {
        match self {
            Script::Unknown => "",
            Script::Common => "Zyyy",
            Script::Inherited => "Zinh",
""")
    for script in script_list:
        f.write("            Script::%s => \"%s\",\n" % (longforms[script], script))
    f.write("""        }
    }
""")

    # Generate impl of `inner_from_short_name`
    f.write("""
    #[inline]
    pub(crate) fn inner_from_short_name(input: &str) -> Option<Self> {
        match input {
            "Zyyy" => Some(Script::Common),
            "Zinh" => Some(Script::Inherited),
""")
    for script in script_list:
        f.write("            \"%s\" => Some(Script::%s),\n" % (script, longforms[script]))
    f.write("""        _ => None,\n""")
    f.write("""        }
    }
""")

    # Generate impl of `for_integer`
    f.write("""
    #[inline]
    pub(crate) fn for_integer(value: u8) -> Self {
        match value {
""")
    for (i, script) in enumerate(script_list):
        f.write("            %s => Script::%s,\n" % (i, longforms[script]))
    f.write("""            _ => unreachable!(),
        }
    }
""")

    # Close `impl Script` section
    f.write("""
}
""")

def extension_name(ext):
    """Get the rust source for a given ScriptExtension"""
    return "script_extensions::%s" % "_".join([e.upper() for e in ext])


if __name__ == "__main__":
    r = "tables.rs"
    if os.path.exists(r):
        os.remove(r)
    with open(r, "w") as rf:
        # write the file's preamble
        rf.write(preamble)
        rf.write("""
/// The version of [Unicode](http://www.unicode.org/)
/// that this version of unicode-script is based on.
pub const UNICODE_VERSION: (u64, u64, u64) = (%s, %s, %s);
""" % UNICODE_VERSION)


        (longforms, shortforms) = aliases()

        scripts = load_properties("Scripts.txt", [])

        script_table = []
        script_list = []

        for script in scripts:
            if script not in ["Common", "Unknown", "Inherited"]:
                script_list.append(shortforms[script])
            script_table.extend([(x, y, shortforms[script]) for (x, y) in scripts[script]])
        script_list.sort()
        script_table.sort(key=lambda w: w[0])


        extensions = load_properties("ScriptExtensions.txt", [])
        extension_table = []
        extension_list = []

        for ext in extensions:
            split = ext.split(" ")
            split.sort()
            output_ext = [ext]
            if len(split) > 1:
                extension_list.append(split)
                output_ext = split
            extension_table.extend([(x, y, output_ext) for (x, y) in extensions[ext]])
        extension_table.sort(key=lambda w: w[0])


        emit_enums(rf, script_list, extension_list, longforms)
        emit_search(rf)

        emit_table(rf, "SCRIPTS", script_table, t_type = "&'static [(char, char, Script)]",
                   is_pub=False , pfun=lambda x: "(%s,%s, Script::%s)" % (escape_char(x[0]), escape_char(x[1]), longforms[x[2]]))
        emit_table(rf, "SCRIPT_EXTENSIONS", extension_table, t_type = "&'static [(char, char, ScriptExtension)]",
                   is_pub=False , pfun=lambda x: "(%s,%s,%s)" % (escape_char(x[0]), escape_char(x[1]), extension_name(x[2])))

        # emit_table(rf, "FOObar", properties)

        rf.write(ending)
