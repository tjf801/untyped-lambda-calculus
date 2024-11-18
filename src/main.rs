#![feature(box_patterns)]
#![feature(box_into_inner)]

use std::fmt::{Debug, Display, };
use std::str::FromStr;



/// <Syntax> ::= 
///     <Neutral>
///   | <Neutral> <Syntax>
/// <Neutral> ::= 
///     <Ident> [ "@" <int> ]
///   | "(" <Syntax> ")"
///   | ( "λ" | "fun" | "lambda" ) <Ident> ( ":" | "↦" | "->" | "." ) <Syntax>
#[derive(Clone, Debug)]
enum Syntax {
    // ( "λ" | "fun" | "lambda" ) <Ident> ( ":" | "↦" | "->" | "." ) <Syntax>
    Lambda(String, Box<Self>),
    
    // <Ident>
    Variable { name: String, shadow_idx: usize, de_bruin_idx: usize },
    
    // <Neutral> <Syntax>
    Apply(Box<Self>, Box<Self>)
}

impl Display for Syntax {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Variable { name, shadow_idx, de_bruin_idx } => {
                if f.alternate() {
                    f.write_fmt(format_args!("{de_bruin_idx}"))
                } else if *shadow_idx == 0 {
                    f.write_str(name)
                } else {
                    f.write_fmt(format_args!("{name}@{shadow_idx}"))
                }
            }
            Self::Lambda(var, body) => {
                if f.alternate() {
                    f.write_str("λ.")?;
                    if body.is_apply() {
                        f.write_str(" ")?;
                    }
                } else {
                    f.write_fmt(format_args!("λ{var}: "))?;
                }
                <Self as Display>::fmt(body, f)
            }
            Self::Apply(func, arg) => {
                let func_parens = func.is_lambda() || (func.is_apply() && arg.is_apply());
                let arg_parens = !arg.is_var();
                
                if func_parens { f.write_str("(")? }
                <Self as Display>::fmt(func, f)?;
                if func_parens { f.write_str(")")? }
                
                // if !(func_parens && arg_parens) { f.write_str(" ")?; }
                f.write_str(" ")?;
                
                if arg_parens { f.write_str("(")? }
                <Self as Display>::fmt(arg, f)?;
                if arg_parens { f.write_str(")")? }
                
                Ok(())
            }
        }
    }
}

impl Syntax {
    fn is_lambda(&self) -> bool {
        match self { Self::Lambda(_, _) => true, _ => false }
    }
    
    fn is_var(&self) -> bool {
        match self { Self::Variable { .. } => true, _ => false }
    }
    
    fn is_apply(&self) -> bool {
        match self { Self::Apply(_, _) => true, _ => false }
    }
    
    fn shift_free(&mut self, num_places: isize, cutoff: usize) {
        match self {
            Self::Apply(func, body) => {
                func.shift_free(num_places, cutoff);
                body.shift_free(num_places, cutoff);
            }
            Self::Lambda(_ident, body) => {
                body.shift_free(num_places, cutoff + 1);
            }
            Self::Variable { de_bruin_idx, .. } => {
                if *de_bruin_idx >= cutoff {
                    *de_bruin_idx = de_bruin_idx.checked_add_signed(num_places).unwrap();
                }
            }
        }
    }
    
    fn shift_free_name(&mut self, var_name: &str, num_places: isize, cutoff: usize) {
        match self {
            Self::Apply(func, body) => {
                func.shift_free_name(var_name, num_places, cutoff);
                body.shift_free_name(var_name, num_places, cutoff);
            }
            Self::Lambda(ident, body) => {
                if ident == var_name {
                    body.shift_free_name(var_name, num_places, cutoff + 1);
                } else {
                    body.shift_free_name(var_name, num_places, cutoff);
                }
            }
            Self::Variable { name, shadow_idx, .. } => {
                if name == var_name && *shadow_idx >= cutoff {
                    *shadow_idx = shadow_idx.checked_add_signed(num_places).unwrap();
                }
            }
        }
    }
    
    fn substitute(&mut self, j: usize, mut term: Self) {
        match self {
            Self::Variable { de_bruin_idx: k, .. } => {
                if j == *k {
                    *self = term;
                }
            },
            Self::Lambda(var, box body) => {
                term.shift_free(1, 0);
                term.shift_free_name(var, 1, 0);
                body.substitute(j+1, term);
            }
            Self::Apply(func, arg) => {
                func.substitute(j, term.clone());
                arg.substitute(j, term);
            },
        }
    }
    
    fn reduce(&mut self) -> bool {
        match self {
            Self::Apply(box Self::Lambda(v, box body), box arg) => {
                // beta reduce
                let mut arg = arg.clone();
                arg.shift_free(1, 0);
                arg.shift_free_name(v, 1, 0);
                
                body.substitute(0, arg);
                
                body.shift_free(-1, 0);
                body.shift_free_name(v, -1, 0);
                
                *self = body.clone(); // TODO: i hope the optimizer catches this...
                false
            }
            Self::Apply(func, arg) => {
                let left_normal = func.reduce();
                let right_normal = arg.reduce();
                left_normal && right_normal
            }
            Self::Lambda(_, body) => body.reduce(),
            _v => { true },
        }
    }
}


#[derive(Debug)]
enum ParserError {
    ExpectedOpeningParenthesis,
    ExpectedClosingParenthesis,
    ExpectedFunctionDefinition, 
    ExpectedIdentifier,
    ExpectedColon,
    UnknownVariable,
    ExpectedNeutralTerm,
    ExpectedInteger,
}

struct Parser<'a> {
    // source: &'a str,
    // position: usize,
    current: &'a str,
    variables: Vec<String>,
}

impl<'src> Parser<'src> {
    fn new(source: &'src str) -> Self {
        Parser { current: source, variables: vec![] }
    }
    
    fn trim_ws(&mut self) {
        let index = self.current.char_indices()
            .find_map(|(i, c)| (!c.is_whitespace()).then_some(i) )
            .unwrap_or(0);
        self.current = &self.current[index..];
    }
    
    fn pop_open_paren(&mut self) -> Result<(), ParserError> {
        const OPEN_PAREN: &str = "(";
        
        if !self.current.starts_with(OPEN_PAREN) {
            return Err(ParserError::ExpectedOpeningParenthesis)
        }
        
        self.current = &self.current[OPEN_PAREN.len()..];
        self.trim_ws();
        
        Ok(())
    }
    
    fn pop_close_paren(&mut self) -> Result<(), ParserError> {
        const CLOSE_PAREN: &str = ")";
        
        if !self.current.starts_with(CLOSE_PAREN) {
            println!("AAAAAAAAAAAAAA {:?}", self.current);
            return Err(ParserError::ExpectedClosingParenthesis)
        }
        
        self.current = &self.current[CLOSE_PAREN.len()..];
        self.trim_ws();
        
        Ok(())
    }
    
    fn has_lambda_next(&self) -> bool {
        self.current.starts_with("λ") || self.current.starts_with("lambda") || self.current.starts_with("fun") || self.current.starts_with(r"\")
    }
    
    fn pop_lambda(&mut self) -> Result<(), ParserError> {
        if self.current.starts_with("λ") {
            self.current = &self.current["λ".len()..];
            self.trim_ws();
            return Ok(())
        }
        if self.current.starts_with("lambda") {
            self.current = &self.current["lambda".len()..];
            self.trim_ws();
            return Ok(())
        }
        if self.current.starts_with("fun") {
            self.current = &self.current["fun".len()..];
            self.trim_ws();
            return Ok(())
        }
        if self.current.starts_with(r"\") {
            self.current = &self.current[r"\".len()..];
            self.trim_ws();
            return Ok(())
        }
        
        Err(ParserError::ExpectedFunctionDefinition)
    }
    
    fn pop_colon(&mut self) -> Result<(), ParserError> {
        if self.current.starts_with(":") {
            self.current = &self.current[":".len()..];
            self.trim_ws();
            return Ok(())
        }
        if self.current.starts_with(".") {
            self.current = &self.current[".".len()..];
            self.trim_ws();
            return Ok(())
        }
        if self.current.starts_with("↦") {
            self.current = &self.current["↦".len()..];
            self.trim_ws();
            return Ok(())
        }
        if self.current.starts_with("->") {
            self.current = &self.current["->".len()..];
            self.trim_ws();
            return Ok(())
        }
        
        Err(ParserError::ExpectedColon)
    }
    
    fn parse_ident(&mut self) -> Result<&'src str, ParserError> {
        let idx = self.current.char_indices()
            .find_map(|(i, c)| (!c.is_alphanumeric() && c != '_').then_some(i))
            .unwrap_or(self.current.len());
        
        let ident_str = &self.current[..idx];
        
        self.current = &self.current[idx..];
        self.trim_ws();
        
        if ident_str.len() == 0 {
            // println!("Expected ident @ {:?}", self.current);
            return Err(ParserError::ExpectedIdentifier)
        }
        
        Ok(ident_str)
    }
    
    fn parse_func(&mut self) -> Result<Syntax, ParserError> {
        // TODO: if result is err, see if we find a colon, and try to keep going
        let _ = self.pop_lambda()?;
        
        let ident = match self.parse_ident() {
            Ok(i) => i,
            Err(e) => {
                println!("{e:?}");
                return Err(e);
            }
        };
        
        // TODO: better errors here too
        self.pop_colon()?;
        
        self.variables.push(ident.to_owned());
        
        let result = self.parse_syntax();
        
        let i = self.variables.pop().expect("Nowhere else should pop variables from the variable stack");
        assert_eq!(i, ident);
        
        Ok(Syntax::Lambda(i, Box::new(result?)))
    }
    
    fn parse_variable(&mut self) -> Result<Syntax, ParserError> {
        let ident = self.parse_ident()?;
        let shadow_idx = if self.current.starts_with("@") {
            self.current = &self.current["@".len()..];
            let idx = self.current.chars().position(|c| !c.is_numeric()).unwrap_or(self.current.len());
            let result = self.current[..idx].parse::<usize>();
            self.current = &self.current[idx..];
            self.trim_ws();
            result.or(Err(ParserError::ExpectedInteger))?
        } else {
            0
        };
        
        let (de_bruin_idx, _) = self.variables.iter()
            .rev().enumerate()
            .filter(|(_, n)| *n == ident)
            .nth(shadow_idx)
            .ok_or(ParserError::UnknownVariable)?;
        
        Ok(Syntax::Variable { name: ident.to_owned(), shadow_idx, de_bruin_idx })
    }
    
    fn parse_neutral_term(&mut self) -> Result<Syntax, ParserError> {
        if self.current.starts_with("(") {
            self.pop_open_paren().expect("just checked for opening paren");
            
            let result = match self.parse_syntax() {
                Ok(x) => x,
                Err(e) => {
                    // if result is err, continue until we find the first closing parenthesis. if there isnt one, tell user that
                    let (idx, _) = self.current.char_indices().find(|&(_, c)| c == ')').ok_or(ParserError::ExpectedClosingParenthesis)?;
                    self.current = &self.current[idx..];
                    self.trim_ws();
                    return Err(e);
                }
            };
            
            self.pop_close_paren()?;
            
            return Ok(result)
        }
        
        if self.has_lambda_next() {
            return self.parse_func()
        }
        
        match self.parse_variable() {
            Err(ParserError::ExpectedIdentifier) => {
                // println!("Tried parsing variable at {:?}", self.current);
            },
            result => return result
        }
        
        Err(ParserError::ExpectedNeutralTerm)
    }
    
    fn parse_syntax(&mut self) -> Result<Syntax, ParserError> {
        let mut neutral = self.parse_neutral_term()?;
        
        let mut old_current = self.current;
        let mut next_neutral_result = self.parse_neutral_term();
        
        while let Ok(next_neutral) = next_neutral_result {
            old_current = self.current;
            neutral = Syntax::Apply(Box::new(neutral), Box::new(next_neutral));
            next_neutral_result = self.parse_neutral_term();
        }
        
        // println!("{next_neutral_result:?} {:?}", self.current);
        self.current = old_current;
        
        Ok(neutral)
    }
}

impl FromStr for Syntax {
    type Err = ParserError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Parser::new(s).parse_syntax()
    }
}


fn main() {
    let src = "(λx: (λf: f f) (λs: s (s (s (x s)))))";
    // let src = "(λf: f f f f) (λx: λy: x (x (x y)))"; // bro this brings this thing to its KNEES wtf
    
    let mut term = src.parse::<Syntax>().unwrap();
    println!("0. \x1b[31m{term}\x1b[0m");
    
    const MAX_ITER: usize = 32;
    let mut iters = 0;
    loop {
        if term.reduce() { break }
        println!("{iters}. ");
        iters += 1;
        if iters == MAX_ITER { break }
    }
    println!("{iters}. \x1b[32m{term}\x1b[0m");
}
