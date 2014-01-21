// Copyright (c) 2014 Michael Woerister

// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

use statemachine::{StateMachine, StateId, Char, Epsilon};

#[deriving(Clone, IterBytes, Eq)]
pub enum Regex {
    Leaf(char),
    Kleene(~Regex),
    Seq(~Regex, ~Regex),
    Union(~Regex, ~Regex),
}

impl Regex {

    pub fn to_state_machine(&self) -> (StateMachine, StateId, StateId) {
        match *self {
            Leaf(c) => {
                let mut sm = StateMachine::new();
                let start_state = sm.add_state();
                let end_state = sm.add_state();
                sm.add_transition(start_state, end_state, Char(c));
                (sm, start_state, end_state)
            }
            Kleene(ref sub) => {
                let (mut sm, sub_start, sub_end) = sub.to_state_machine();

                let start_state = sm.add_state();
                let end_state = sm.add_state();

                sm.add_transition(start_state, sub_start, Epsilon);
                sm.add_transition(sub_end, sub_start, Epsilon);
                sm.add_transition(sub_end, end_state, Epsilon);
                sm.add_transition(start_state, end_state, Epsilon);

                (sm, start_state, end_state)
            }
            Seq(ref left, ref right) => {
                let (mut left_sm, left_start, left_end) = left.to_state_machine();
                let (right_sm, right_start, right_end) = right.to_state_machine();

                left_sm.consume(right_sm);

                left_sm.add_transition(left_end, right_start, Epsilon);

                (left_sm, left_start, right_end)
            }
            Union(ref left, ref right) => {
                let (mut sm, left_start, left_end) = left.to_state_machine();
                let (right_sm, right_start, right_end) = right.to_state_machine();

                sm.consume(right_sm);

                let start_state = sm.add_state();
                let end_state = sm.add_state();

                sm.add_transition(start_state, left_start, Epsilon);
                sm.add_transition(start_state, right_start, Epsilon);

                sm.add_transition(left_end, end_state, Epsilon);
                sm.add_transition(right_end, end_state, Epsilon);

                (sm, start_state, end_state)
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::{Regex, Seq, Union, Kleene, Leaf};
    use statemachine::{StateMachine, StateId, StateSet, ToDfaResult};

    fn compile(regex: &Regex) -> (StateMachine, StateId, ~[StateId]) {
        let (sm, start, end) = regex.to_state_machine();
        let end_states = [end];
        let end_states: StateSet = end_states.iter().map(|x| *x).collect();
        let ToDfaResult { dfa, start_state, end_state_map } = sm.to_dfa(start, &end_states);
        let dfa_end_states = end_state_map.keys().map(|x| *x).to_owned_vec();

        let partitioning = dfa.accepting_non_accepting_partitioning(dfa_end_states.iter().map(|s| *s));
        let (minimized_dfa, state_map) = dfa.to_minimal(&partitioning);

        let start_state = state_map.get_copy(&start_state);
        let dfa_end_states = dfa_end_states.iter().map(|s| state_map.get_copy(s)).collect::<StateSet>();

        (minimized_dfa, start_state, dfa_end_states.iter().map(|x| x.clone()).to_owned_vec())
    }

    fn matches(&(ref sm, start_state, ref end_states): &(StateMachine, StateId, ~[StateId]), s: &str) -> bool {
        let result_state = sm.run(start_state, s);
        end_states.iter().any(|&x| Some(x) == result_state)
    }


    #[test]
    fn test_kleene() {
        let sm = compile(&Kleene(~Leaf('a')));

        assert!(matches(&sm, ""));
        assert!(matches(&sm, "a"));
        assert!(matches(&sm, "aaa"));
        assert!(matches(&sm, "aaaaaaaaaaaaaaaaaaaaaaaaaa"));

        assert!(!matches(&sm, "b"));
        assert!(!matches(&sm, "caaaa"));
        assert!(!matches(&sm, "daaa"));
        assert!(!matches(&sm, "e"));
        assert!(!matches(&sm, "ab"));
    }

    #[test]
    fn test_seq() {
        let sm = compile(&Seq(~Leaf('a'), ~Seq(~Leaf('b'),~Leaf('c'))));

        assert!(!matches(&sm, ""));
        assert!(!matches(&sm, "a"));
        assert!(!matches(&sm, "ab"));
        assert!(matches(&sm, "abc"));
        assert!(!matches(&sm, "abcd"));

        assert!(!matches(&sm, "bc"));
        assert!(!matches(&sm, "c"));
        assert!(!matches(&sm, "bca"));
    }

    #[test]
    fn test_union() {
        let sm = compile(&Union(~Leaf('a'), ~Union(~Leaf('b'),~Leaf('c'))));

        assert!(!matches(&sm, ""));
        assert!(matches(&sm, "a"));
        assert!(matches(&sm, "b"));
        assert!(matches(&sm, "c"));

        assert!(!matches(&sm, "ab"));
        assert!(!matches(&sm, "ac"));
        assert!(!matches(&sm, "bc"));
    }

    #[test]
    fn test_ident_like() {
        let alpha = ~Union(
            ~Leaf('a'),
            ~Union(
                ~Leaf('b'),
                ~Union(
                    ~Leaf('c'),
                    ~Leaf('d')
                )
            )
        );

        let digit = ~Union(
            ~Leaf('1'),
            ~Union(
                ~Leaf('2'),
                ~Union(
                    ~Leaf('3'),
                    ~Leaf('4')
                )
            )
        );

        let regex = Seq(alpha.clone(), ~Kleene(~Union(alpha, digit)));
        let sm = compile(&regex);

        assert!(!matches(&sm, ""));

        assert!(matches(&sm, "a"));
        assert!(matches(&sm, "b"));
        assert!(matches(&sm, "c"));
        assert!(matches(&sm, "d"));

        assert!(!matches(&sm, "1"));
        assert!(!matches(&sm, "2"));
        assert!(!matches(&sm, "3"));
        assert!(!matches(&sm, "4"));

        assert!(matches(&sm, "aaaa"));
        assert!(matches(&sm, "a1b2"));
        assert!(matches(&sm, "aab1a"));
        assert!(matches(&sm, "dddaca"));

        assert!(!matches(&sm, "1cbda"));
        assert!(!matches(&sm, "2dca"));
        assert!(!matches(&sm, "3da"));
        assert!(!matches(&sm, "4d"));
        assert!(!matches(&sm, "5ddda"));
    }
}